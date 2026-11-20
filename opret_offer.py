"""Opretter nye offers som KOPI af offers du allerede har. Bruges af siden "Create" i dashboardet (knapperne),
og kan ogsaa koeres fra kommandolinjen.

Dashboardet (hovedvejen):  Find/skift-ord i titel og beskrivelse (fx "1 year, 12 months" -> "2 Years"), 1 key i foerste
account-slot (Scroll Down + Additional info for 1 aar / 2 aar) og alle nye offers staar paa PAUSE.

Kommandolinjen (kopierer uden keys):
  py opret_offer.py                               -> viser dine offers med numre og spoerger hvilket du vil kopiere
  py opret_offer.py --fra "netflix,12 month"      -> kopierer det ene offer hvis titel har alle ordene (stopper hvis flere)
  py opret_offer.py --id <offer-id>               -> kopierer netop dette offer
  --antal 3  --titel "..."  --pris 7.7  --lager 1  --kun-se  --ja

Sikkerhed: den foerste kopi bliver oprettet, sat paa pause og LAEST TILBAGE fra Eldorado og sammenlignet med det der
skulle vaere oprettet. Er der forskel, stopper det, saa der ikke kommer flere forkerte.
Adressen kommer fra Eldorados egen API-beskrivelse: POST /api/flexibleOffers/account (med accountDeliveryDetails).
"""
import argparse
import copy
import json
import re
import threading
import time
from pathlib import Path

import requests

import offer as O
from ligg_op_nye import all_offers, title_of

HERE = Path(__file__).resolve().parent
LOG = HERE / "opret_log.txt"            # command line log (ids only)
LOG_JSON = Path("opret_log.json")       # what the dashboard page created (like keys.txt: in the working folder)
INFLIGHT_KEYS = Path("keys_igang.txt")      # the key being used right now (if the program dies, it is not lost: it stays here)
UNSURE_KEYS = Path("keys_usikre.txt")   # a key whose offer may or may not have been created (no answer from Eldorado)
MAX_COPIES = 30
UUID_RE = re.compile(r"^[0-9a-fA-F-]{32,40}$")
_log_lock = threading.Lock()


# ---------------------------------------------------------------- reading and comparing

def money(m):
    m = m or {}
    return {"amount": m.get("amount"), "currency": m.get("currency")}


def image(i):
    i = i or {}
    return {k: i.get(k) for k in ("smallImage", "largeImage", "originalSizeImage")}


def private(client, offer_id):
    return (client.request("GET", f"/api/flexibleOffers/{offer_id}/private") or {}).get("offer") or {}


def price_text(o):
    p = o.get("pricePerUnit") or {}
    return f"{p.get('amount')} {p.get('currency')}" if p.get("amount") is not None else "?"


def build_body(src, title=None, price=None, stock=1, description=None):
    """The request for POST /api/flexibleOffers/account, built from the private view of an existing offer."""
    pricing = {
        "quantity": int(stock),
        "minQuantity": int(src.get("minQuantity") or 1),
        "pricePerUnit": money(src.get("pricePerUnit")),
    }
    if price is not None:
        pricing["pricePerUnit"]["amount"] = float(price)
    if src.get("volumeDiscounts"):
        pricing["volumeDiscounts"] = [{"quantity": v["quantity"], "percentage": v["percentage"]} for v in src["volumeDiscounts"]]
    details = {
        "offerTitle": title or src.get("offerTitle"),
        "description": description if description is not None else src.get("description"),
        "guaranteedDeliveryTime": src.get("guaranteedDeliveryTime"),
        "mainOfferImage": image(src.get("mainOfferImage")),
        "offerImages": [image(i) for i in (src.get("offerImages") or [])],
        "pricing": pricing,
    }
    if src.get("hasOriginalEmail") is not None:
        details["hasOriginalEmail"] = src["hasOriginalEmail"]
    game = {"gameId": src.get("gameId"), "category": src.get("category") or "Account"}
    env = [e.get("id") for e in (src.get("tradeEnvironmentValues") or []) if e.get("id")]
    if env:
        game["tradeEnvironmentId"] = env[0]
    attrs = [{"id": a["id"]} for a in (src.get("offerAttributeIdValues") or []) if a.get("id")]
    if attrs:
        game["offerAttributes"] = attrs
    return {"details": details, "augmentedGame": game}


def differences(src, new, title=None, price=None, description=None, stock=None, state=None):
    """What differs between what we meant to create and what Eldorado reports back. Empty list = as intended."""
    out = []

    def cmp(name, a, b):
        if a != b:
            out.append(f"{name}: skulle vaere {a!r}, er {b!r}")

    cmp("gameId", src.get("gameId"), new.get("gameId"))
    cmp("kategori", src.get("category"), new.get("category"))
    norm = lambda x: (x or "").replace("\r\n", "\n").replace("\r", "\n").strip()   # Eldorado may change line endings / edge spaces
    cmp("titel", norm(title or src.get("offerTitle")), norm(new.get("offerTitle")))
    cmp("beskrivelse", norm(description if description is not None else src.get("description")), norm(new.get("description")))
    cmp("leveringstid", src.get("guaranteedDeliveryTime"), new.get("guaranteedDeliveryTime"))
    num = lambda x: round(float(x), 4) if isinstance(x, (int, float)) else x
    cmp("pris", num(price if price is not None else (src.get("pricePerUnit") or {}).get("amount")),
        num((new.get("pricePerUnit") or {}).get("amount")))
    cmp("valuta", (src.get("pricePerUnit") or {}).get("currency"), (new.get("pricePerUnit") or {}).get("currency"))
    ids = lambda o, k: sorted(str(x.get("id")) for x in (o.get(k) or []))
    cmp("valg (attributter)", ids(src, "offerAttributeIdValues"), ids(new, "offerAttributeIdValues"))
    cmp("miljoe", ids(src, "tradeEnvironmentValues"), ids(new, "tradeEnvironmentValues"))
    has = lambda o: bool((o.get("mainOfferImage") or {}).get("originalSizeImage") or (o.get("mainOfferImage") or {}).get("largeImage"))
    cmp("hovedbillede", has(src), has(new))
    cmp("antal billeder", len(src.get("offerImages") or []), len(new.get("offerImages") or []))
    if stock is not None:
        cmp("lager", stock, new.get("quantity"))
    if state is not None:
        cmp("tilstand", state, new.get("offerState"))
    return out


def err_text(e):
    r = getattr(e, "response", None)
    if r is None:
        return f"{type(e).__name__}: {e}"[:400]
    return f"{r.status_code} {r.text[:500]}"


# ---------------------------------------------------------------- find / replace in title and description

def word_regex(find):
    """'1 year, 12 months' -> one case-insensitive pattern. Spaces and hyphens are interchangeable ('12-Months' matches),
    a final plural s is optional ('12 month' matches), and a number is never the tail of a longer number ('11 years' is left alone)."""
    alts = []
    for a in str(find).split(","):
        words = [w for w in re.split(r"[\s\-]+", a.strip()) if w]
        if not words or sum(len(w) for w in words) < 2:
            continue
        parts = [re.escape(w) for w in words]
        last = words[-1]
        if last.isalpha() and len(last) > 2:
            base = last[:-1] if last.lower().endswith("s") else last
            parts[-1] = re.escape(base) + "s?"
        alts.append(r"(?<![A-Za-z0-9])" + r"[\s\-]+".join(parts) + r"(?![A-Za-z0-9])")
    if not alts:
        raise ValueError("bad find")
    return re.compile("|".join(alts), re.I)


def swap(text, rx, repl):
    """Returns (new_text, number_of_changes, old_parts, new_parts). The parts are [[text, changed?], ...] for showing the difference."""
    text = text or ""
    old_p, new_p, pos, n = [], [], 0, 0
    for m in rx.finditer(text):
        if m.start() > pos:
            old_p.append([text[pos:m.start()], False])
            new_p.append([text[pos:m.start()], False])
        old_p.append([m.group(0), True])
        new_p.append([repl, True])
        pos = m.end()
        n += 1
    if pos < len(text) or not n:
        old_p.append([text[pos:], False])
        new_p.append([text[pos:], False])
    return "".join(x for x, _ in new_p), n, old_p, new_p


def snippets(old_p, new_p, width=34, limit=8):
    """Short 'before -> after' pieces of a long text (the description)."""
    out = []
    for i, (x, ch) in enumerate(old_p):
        if not ch or len(out) >= limit:
            continue
        pre = old_p[i - 1][0][-width:] if i > 0 else ""
        post = old_p[i + 1][0][:width] if i + 1 < len(old_p) else ""
        out.append({"pre": pre, "old": x, "new": new_p[i][0], "post": post})
    return out


KIND_2AR = re.compile(r"(?<![A-Za-z0-9])2[\s\-]*years?(?![A-Za-z0-9])", re.I)
KIND_1AR = re.compile(r"(?<![A-Za-z0-9])(?:1[\s\-]*years?|12[\s\-]*months?)(?![A-Za-z0-9])", re.I)


def kind_of_title(title):
    """'2ar' for 2 years, '1ar' for 1 year / 12 months, None when it cannot tell."""
    a, b = bool(KIND_2AR.search(title or "")), bool(KIND_1AR.search(title or ""))
    return "2ar" if a and not b else "1ar" if b and not a else None


def info_text(kind):
    """The Additional info text for 1 year (info_1ar.txt, else additional_info.txt) or 2 years (info_2ar.txt)."""
    names = ("info_2ar.txt",) if kind == "2ar" else ("info_1ar.txt", "additional_info.txt")
    for n in names:
        for base in (Path.cwd(), HERE):
            f = base / n
            if f.exists():
                return f.read_text(encoding="utf-8").rstrip(), n
    return None, names[0]


def info_status(loader=None):
    out = {}
    for k in ("1ar", "2ar"):
        text, name = (loader or info_text)(k)
        out[k] = {"file": name, "found": text is not None, "ok": bool(text) and O.PLACEHOLDER in text}
    return out


def clean_args(j):
    """Checks what the page sends. Raises ValueError with a short code."""
    ids = j.get("ids")
    if not isinstance(ids, list) or not ids:
        raise ValueError("no offers chosen")
    seen = []
    for x in ids:
        if not isinstance(x, str) or not UUID_RE.match(x):
            raise ValueError("bad offer id")
        if x not in seen:
            seen.append(x)
    if len(seen) > MAX_COPIES:
        raise ValueError(f"at most {MAX_COPIES} offers at a time")
    find = str(j.get("find", "")).strip()
    repl = str(j.get("repl", "")).strip()
    if len(find) < 2 or len(find) > 120:
        raise ValueError("bad find")
    if not repl or len(repl) > 80 or "\n" in repl:
        raise ValueError("bad replace")
    info = j.get("info", "auto")
    if info not in ("auto", "1ar", "2ar"):
        raise ValueError("bad info")
    word_regex(find)
    return seen, find, repl, info


# ---------------------------------------------------------------- keys

class FileKeys:
    """keys.txt - shared with the auto refills. Only one program at a time takes keys (keys.lock)."""

    def left(self):
        n = 0
        for f in (O.KEYS_FILE, O.INBOX_FILE):
            try:
                n += sum(1 for l in f.read_text(encoding="utf-8").splitlines() if l.strip() and not l.strip().startswith("#"))
            except OSError:
                pass
        return n

    def take(self):
        """Takes the first key OUT of keys.txt right now (so nothing else can use it). None = no keys left."""
        try:
            with O.keys_lock():
                O.absorb_inbox()
                if not O.KEYS_FILE.exists():
                    return None
                lines = O.KEYS_FILE.read_text(encoding="utf-8").splitlines()
                keys = [l.strip() for l in lines if l.strip() and not l.strip().startswith("#")]
                if not keys:
                    return None
                key, rest, gone = keys[0], [], False
                for l in lines:
                    if not gone and l.strip() == key:
                        gone = True
                        continue
                    rest.append(l)
                O.KEYS_FILE.write_text("\n".join(rest) + ("\n" if rest else ""), encoding="utf-8")
                self._inflight(key, True)
                return key
        except SystemExit as e:
            raise RuntimeError(str(e))

    @staticmethod
    def _inflight(key, add):
        """keys_igang.txt = keys taken out of keys.txt that are not yet used or given back."""
        try:
            have = [l for l in INFLIGHT_KEYS.read_text(encoding="utf-8").splitlines() if l.strip()] if INFLIGHT_KEYS.exists() else []
            have = [l for l in have if l.strip() != key] + ([key] if add else [])
            INFLIGHT_KEYS.write_text("\n".join(have) + ("\n" if have else ""), encoding="utf-8")
        except OSError:
            pass

    def give_back(self, key):
        self._inflight(key, False)
        try:
            with O.keys_lock():
                have = O.KEYS_FILE.read_text(encoding="utf-8") if O.KEYS_FILE.exists() else ""
                O.KEYS_FILE.write_text(key + "\n" + have, encoding="utf-8")
        except SystemExit as e:
            raise RuntimeError(str(e))

    def used(self, key):
        with O.USED_FILE.open("a", encoding="utf-8") as f:
            f.write(key + "\n")
        self._inflight(key, False)

    def unsure(self, key):
        with UNSURE_KEYS.open("a", encoding="utf-8") as f:
            f.write(key + "\n")
        self._inflight(key, False)


class ListKeys:
    """Keys in memory (demo mode and tests)."""

    def __init__(self, keys):
        self.keys, self.used_keys, self.unsure_keys = list(keys), [], []

    def left(self):
        return len(self.keys)

    def take(self):
        return self.keys.pop(0) if self.keys else None

    def give_back(self, key):
        self.keys.insert(0, key)

    def used(self, key):
        self.used_keys.append(key)

    def unsure(self, key):
        self.unsure_keys.append(key)


# ---------------------------------------------------------------- the dashboard's list of created offers

def read_log():
    with _log_lock:
        try:
            data = json.loads(LOG_JSON.read_text(encoding="utf-8"))
            return data if isinstance(data, list) else []
        except (OSError, ValueError):
            return []


def log_add(entry):
    with _log_lock:
        try:
            data = json.loads(LOG_JSON.read_text(encoding="utf-8"))
            data = data if isinstance(data, list) else []
        except (OSError, ValueError):
            data = []
        data.append(entry)
        tmp = LOG_JSON.with_suffix(".tmp")
        tmp.write_text(json.dumps(data[-300:], ensure_ascii=False), encoding="utf-8")
        tmp.replace(LOG_JSON)


def list_offers(client):
    out = []
    for o, st in all_offers(client):
        img = o.get("mainOfferImage") or {}
        out.append({"id": o.get("id"), "title": title_of(o), "price": (o.get("pricePerUnit") or {}).get("amount"),
                    "currency": (o.get("pricePerUnit") or {}).get("currency"), "quantity": o.get("quantity"),
                    "state": o.get("offerState") or st, "image": img.get("smallImage") or img.get("largeImage") or ""})
    return out


# ---------------------------------------------------------------- plan (changes nothing) and execution

def make_plan(client, ids, find, repl, info_mode="auto", keys_left=None, loader=None):
    """What would be created. Reads the originals from Eldorado, changes nothing.
    Each item has status: ok | skip (reason) | nokeys. Items starting with _ are internal (not for the page)."""
    loader = loader or info_text
    rx = word_regex(find)
    items = []
    before = {}
    for entry in read_log():
        if entry.get("src"):
            before[entry["src"]] = before.get(entry["src"], 0) + 1
    for oid in ids:
        it = {"id": oid, "copied": before.get(oid, 0), "status": "ok", "reason": "", "title": "", "new_title": "", "title_n": 0, "desc_n": 0,
              "old_parts": [], "new_parts": [], "desc_changes": [], "kind": "", "info_file": "", "new_id": "", "msg": ""}
        items.append(it)
        try:
            src = private(client, oid)
        except requests.RequestException as e:
            it.update(status="skip", reason="read", msg=err_text(e))
            continue
        if not src.get("offerTitle"):
            it.update(status="skip", reason="read", msg="no title")
            continue
        it["_src"] = src
        it["title"] = src["offerTitle"]
        it["new_title"], it["title_n"], it["old_parts"], it["new_parts"] = swap(src["offerTitle"], rx, repl)
        it["_desc"], it["desc_n"], dold, dnew = swap(src.get("description") or "", rx, repl)
        it["desc_changes"] = snippets(dold, dnew)
        if not it["title_n"]:
            it.update(status="skip", reason="nomatch")
            continue
        kind = info_mode if info_mode in ("1ar", "2ar") else kind_of_title(it["new_title"])
        if not kind:
            it.update(status="skip", reason="nokind")
            continue
        text, fname = loader(kind)
        it["kind"], it["info_file"] = kind, fname
        if text is None:
            it.update(status="skip", reason="nofile", msg=fname)
            continue
        if O.PLACEHOLDER not in text:
            it.update(status="skip", reason="noplaceholder", msg=fname)
            continue
        n = len(O.tidy_info(text).replace(O.PLACEHOLDER, "X" * 25))
        if n > O.MAX_INFO:
            it.update(status="skip", reason="toolong", msg=f"{fname}: {n}/{O.MAX_INFO}")
            continue
    if keys_left is not None:
        left = keys_left
        for it in items:
            if it["status"] == "ok":
                if left > 0:
                    left -= 1
                else:
                    it["status"] = "nokeys"
    return {"items": items, "keys": keys_left, "ok": sum(1 for i in items if i["status"] == "ok")}


def public_plan(plan):
    return {"keys": plan["keys"], "ok": plan["ok"],
            "items": [{k: v for k, v in it.items() if not k.startswith("_")} for it in plan["items"]]}


def execute(client, plan, keys, emit=lambda msg=None: None, stop=lambda: False, loader=None, pause_between=1.0, sleep=time.sleep):
    """Creates the copies one by one: 1 key each, then PAUSE, then reads the offer back and compares.
    Stops at the first problem (nothing is retried, so nothing can be created twice).
    Returns {"created": n, "state": "done"|"stopped"|"failed", "error": text}."""
    loader = loader or info_text
    todo = [it for it in plan["items"] if it["status"] == "ok"]
    created, first = 0, True
    for it in todo:
        if stop():
            return {"created": created, "state": "stopped", "error": ""}
        it["status"] = "working"
        emit()
        try:
            key = keys.take()
        except RuntimeError as e:
            it.update(status="failed", reason="keys", msg=str(e)[:300])
            emit()
            return {"created": created, "state": "failed", "error": str(e)[:300]}
        if key is None:
            it.update(status="nokeys")
            emit("out of keys")
            return {"created": created, "state": "failed", "error": "out of keys"}
        text, fname = loader(it["kind"])
        try:
            O.check_info_length(text, key)
        except SystemExit as e:
            keys.give_back(key)
            it.update(status="failed", reason="toolong", msg=str(e)[:300])
            emit()
            return {"created": created, "state": "failed", "error": str(e)[:300]}
        src = it["_src"]
        body = build_body(src, title=it["new_title"], description=it["_desc"], stock=1)
        body["accountDeliveryDetails"] = [O.account_body(text, key)["structuredDetails"]]
        try:
            res = client.request("POST", "/api/flexibleOffers/account", json=body) or {}
        except requests.HTTPError as e:                      # Eldorado answered with an error: nothing was created
            keys.give_back(key)
            msg = err_text(e)
            it.update(status="failed", reason="refused", msg=msg)
            emit()
            return {"created": created, "state": "failed", "error": msg}
        except requests.RequestException as e:               # no answer at all: it may or may not have been created
            keys.unsure(key)
            msg = err_text(e)
            it.update(status="failed", reason="unsure", msg=msg)
            emit()
            return {"created": created, "state": "failed", "error": msg}
        new_id = res.get("id") or (res.get("offer") or {}).get("id")
        if not new_id:
            keys.unsure(key)
            it.update(status="failed", reason="noid", msg=json.dumps(res)[:300])
            emit()
            return {"created": created, "state": "failed", "error": "no id"}
        keys.used(key)
        created += 1
        it["new_id"] = new_id
        log_add({"time": time.strftime("%Y-%m-%d %H:%M:%S"), "id": new_id, "title": it["new_title"], "src": it["id"],
                 "kind": it["kind"], "info": fname})
        try:
            client.request("PUT", f"/api/flexibleOffersUser/me/{new_id}/pause")
        except requests.RequestException as e:
            msg = err_text(e)
            it.update(status="failed", reason="nopause", msg=msg)
            emit()
            return {"created": created, "state": "failed", "error": msg}
        problems = []
        try:
            new = private(client, new_id)
            problems = differences(src, new, title=it["new_title"], description=it["_desc"], stock=1, state="Paused")
        except requests.RequestException as e:
            problems = ["kunne ikke laese det nye offer tilbage: " + err_text(e)]
        if problems:
            it["msg"] = "; ".join(problems)
            if first:
                it.update(status="check", reason="differs")
                emit()
                return {"created": created, "state": "failed", "error": it["msg"]}
            it["status"] = "check"
            it["reason"] = "differs"
        else:
            it["status"] = "done"
        first = False
        emit()
        if pause_between:
            sleep(pause_between)
    return {"created": created, "state": "done", "error": ""}


def in_log(offer_id):
    return any(e.get("id") == offer_id for e in read_log())


def set_live(client, offer_id):
    """Only offers made by the Create page may be set live from there."""
    if not UUID_RE.match(offer_id or "") or not in_log(offer_id):
        raise ValueError("not one of the offers made here")
    client.request("PUT", f"/api/flexibleOffersUser/me/{offer_id}/resume")
    return private(client, offer_id).get("offerState")


def delete_offer(client, offer_id):
    """Deletes an offer made here - but only while it is still PAUSED (never one that is live and may have orders)."""
    if not UUID_RE.match(offer_id or "") or not in_log(offer_id):
        raise ValueError("not one of the offers made here")
    if private(client, offer_id).get("offerState") != "Paused":
        raise ValueError("only paused offers can be deleted here")
    client.request("DELETE", f"/api/flexibleOffersUser/me/{offer_id}")


# ---------------------------------------------------------------- demo (fake Eldorado for 'py dashboard.py demo' and tests)

class DemoClient:
    """Pretends to be Eldorado: a few Netflix offers, creating, pausing, resuming, deleting."""
    BASE_DESC = ("Netflix Premium 4K account - valid for {p}.\nDelivered instantly after payment.\n"
                 "Warranty: {p}. If anything stops working we replace it.")

    def __init__(self):
        self.db, self.n = {}, 0
        titles = ["Netflix | 12 Months Subscription", "Premium plan 4K | 12 months", "Netflix 1 Year Premium UHD",
                  "NETFLIX 4K ULTRA HD - 1 YEAR WARRANTY", "Netflix Premium 12-Months (Private Profile)",
                  "Netflix | 1-Year Full Access", "Netflix UHD 4K 12 months Instant", "Netflix 1 year | Own profile",
                  "Netflix Premium | 12 Month Plan", "Netflix 4K Premium 1 Year Account", "Netflix | 12 Months | 4 Screens",
                  "Netflix Ultra HD 12 months", "Netflix | 2 Years Subscription", "Netflix Lifetime Premium"]
        for i, t in enumerate(titles):
            oid = "%08x-0000-4000-8000-%012x" % (0xA1B2C3D0 + i, 0x100 + i)
            p = "2 years" if "2 Years" in t else "lifetime" if "Lifetime" in t else ("1 year" if i % 2 else "12 months")
            self.db[oid] = {"id": oid, "offerTitle": t, "description": self.BASE_DESC.format(p=p), "gameId": "87", "category": "Account",
                            "guaranteedDeliveryTime": "Instant", "quantity": 3 + i, "minQuantity": 1,
                            "pricePerUnit": {"amount": round(7.7 + (i % 4) * 0.35, 2), "currency": "USD"}, "volumeDiscounts": [],
                            "mainOfferImage": {"smallImage": "", "largeImage": "", "originalSizeImage": ""}, "offerImages": [],
                            "tradeEnvironmentValues": [], "offerAttributeIdValues": [{"id": "attr-region", "name": "Region", "value": "Global"}],
                            "hasOriginalEmail": False, "offerState": "Active" if i % 5 else "Paused"}

    def request(self, method, path, **kw):
        time.sleep(0.05)
        if method == "GET" and path == "/api/flexibleOffers/me/search":
            st = kw["params"]["offerState"]
            return {"results": [o for o in self.db.values() if o["offerState"] == st], "totalPages": 1}
        if method == "GET" and path.endswith("/private"):
            o = self.db.get(path.split("/")[-2])
            if not o:
                raise requests.HTTPError(response=_resp(404, "not found"))
            return {"offer": copy.deepcopy(o)}
        if method == "POST" and path == "/api/flexibleOffers/account":
            b = kw["json"]
            d, g = b["details"], b["augmentedGame"]
            if not (g.get("gameId") and d["pricing"]["pricePerUnit"]["amount"] and b.get("accountDeliveryDetails")):
                raise requests.HTTPError(response=_resp(400, '{"messages":["missing fields"]}'))
            self.n += 1
            nid = "%08x-0000-4000-8000-%012x" % (0xD0000000 + self.n, 0x900 + self.n)
            o = {"id": nid, "offerTitle": d["offerTitle"], "description": d["description"], "gameId": g["gameId"], "category": g["category"],
                 "guaranteedDeliveryTime": d["guaranteedDeliveryTime"], "quantity": len(b["accountDeliveryDetails"]), "minQuantity": 1,
                 "pricePerUnit": d["pricing"]["pricePerUnit"], "volumeDiscounts": [], "mainOfferImage": d["mainOfferImage"],
                 "offerImages": d["offerImages"], "tradeEnvironmentValues": [],
                 "offerAttributeIdValues": [{"id": a["id"]} for a in g.get("offerAttributes", [])],
                 "hasOriginalEmail": d.get("hasOriginalEmail"), "offerState": "Active"}
            self.db[nid] = o
            return {"id": nid}
        if method == "PUT" and path.endswith("/pause"):
            self.db[path.split("/")[-2]]["offerState"] = "Paused"
            return None
        if method == "PUT" and path.endswith("/resume"):
            self.db[path.split("/")[-2]]["offerState"] = "Active"
            return None
        if method == "DELETE":
            self.db.pop(path.split("/")[-1], None)
            return None
        raise AssertionError((method, path))


def _resp(status, text):
    r = requests.Response()
    r.status_code = status
    r._content = text.encode()
    return r


def demo_info(kind):
    return ("Thank you for your order!\n1) Go to netflix.com and use the key below.\nKEY: " + O.PLACEHOLDER +
            "\nPlan: " + ("2 years" if kind == "2ar" else "1 year") + "\nIf you leave a good review we will be happy."), \
        ("info_2ar.txt" if kind == "2ar" else "info_1ar.txt")


# ---------------------------------------------------------------- command line (copies without keys)

def choose(offers, args):
    """Returns the offer id to copy."""
    if args.id:
        return args.id
    if args.fra:
        words = [w.strip().lower() for w in args.fra.split(",") if w.strip()]
        hits = [(o, st) for o, st in offers if all(w in title_of(o).lower() for w in words)]
        if len(hits) == 1:
            return hits[0][0]["id"]
        if not hits:
            raise SystemExit(f"STOPPET: intet offer med alle ordene '{args.fra}' i titlen.")
        raise SystemExit("STOPPET: flere offers passer paa '" + args.fra + "':\n  " +
                         "\n  ".join(f"{title_of(o)} ({st})" for o, st in hits) + "\nBrug flere ord, eller --id.")
    if not offers:
        raise SystemExit("Fandt ingen offers paa din konto.")
    print("\nDine offers:\n")
    for n, (o, st) in enumerate(offers, 1):
        print(f"  {n:>2}) {title_of(o)[:70]:<70} {price_text(o):>10}  {st}")
    while True:
        s = input("\nHvilket nummer vil du kopiere? ").strip()
        if s.isdigit() and 1 <= int(s) <= len(offers):
            return offers[int(s) - 1][0]["id"]
        print("Skriv et af numrene fra listen.")


def main(client=None, argv=None):
    from eldorado_client import EldoradoClient
    ap = argparse.ArgumentParser(description="Opret nye offers som kopi af et eksisterende (sat paa pause).")
    ap.add_argument("--fra")
    ap.add_argument("--id")
    ap.add_argument("--antal", type=int)
    ap.add_argument("--titel")
    ap.add_argument("--pris", type=float)
    ap.add_argument("--lager", type=int, default=1)
    ap.add_argument("--kun-se", action="store_true")
    ap.add_argument("--ja", action="store_true")
    args = ap.parse_args(argv)

    client = client or EldoradoClient()
    offers = [] if args.id else all_offers(client)
    src_id = choose(offers, args)
    src = private(client, src_id)
    if not src.get("offerTitle"):
        raise SystemExit("STOPPET: kunne ikke laese originalen fra Eldorado.")

    n = args.antal
    if n is None:
        if args.fra or args.id or args.ja:
            n = 1
        else:
            s = input("Hvor mange kopier? (1) ").strip()
            n = int(s) if s.isdigit() else 1
    n = max(1, min(MAX_COPIES, n))
    body = build_body(src, args.titel, args.pris, args.lager)

    print(f"\nOriginal : {src.get('offerTitle')}  ({price_text(src)}, id {src_id})")
    print(f"Nye      : {n} stk. \"{body['details']['offerTitle']}\" til {body['details']['pricing']['pricePerUnit']['amount']} "
          f"{body['details']['pricing']['pricePerUnit']['currency']}, lager {args.lager}, sat paa PAUSE")
    if args.kun_se:
        print("\n--kun-se: dette ville blive sendt til Eldorado (POST /api/flexibleOffers/account):\n")
        print(json.dumps(body, indent=1, ensure_ascii=False))
        return 0
    if not args.ja and input("\nSkriv ja for at oprette: ").strip().lower() not in ("ja", "j", "yes", "y"):
        print("Afbrudt - intet er oprettet.")
        return 0

    made = []
    for i in range(1, n + 1):
        try:
            res = client.request("POST", "/api/flexibleOffers/account", json=body) or {}
        except requests.HTTPError as e:
            print(f"\n[{i}/{n}] Eldorado afviste oprettelsen: {err_text(e)}")
            print("Intet blev oprettet i denne omgang. Send mig teksten ovenfor.")
            break
        new_id = res.get("id") or (res.get("offer") or {}).get("id")
        if not new_id:
            print(f"\n[{i}/{n}] Eldorado svarede, men uden offer-id: {json.dumps(res)[:400]}")
            print("STOPPET. Tjek siden 'My offers' om der er kommet et nyt offer.")
            break
        made.append(new_id)
        with LOG.open("a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {new_id} kopi af {src_id}\n")
        try:
            client.request("PUT", f"/api/flexibleOffersUser/me/{new_id}/pause")
            paused = "sat paa pause"
        except requests.HTTPError as e:
            print(f"\n[{i}/{n}] !!! Offer {new_id} blev oprettet, men kunne IKKE saettes paa pause: {err_text(e)}")
            print("Saet det paa pause paa hjemmesiden nu. STOPPET - der oprettes ikke flere.")
            break
        new = private(client, new_id)
        diff = differences(src, new, title=args.titel, price=args.pris)
        print(f"[{i}/{n}] oprettet {new_id} ({paused}, tilstand: {new.get('offerState')})")
        if diff and i == 1:
            print("\nDen foerste kopi er IKKE helt ens med originalen:")
            for d in diff:
                print("   -", d)
            print("STOPPET efter foerste kopi, saa der ikke kommer flere forkerte. Tjek den paa pause paa hjemmesiden,")
            print("slet den hvis den er forkert, og send mig linjerne ovenfor.")
            break
        if diff:
            print("   forskelle:", "; ".join(diff))
    print(f"\nFaerdig: {len(made)} offer(s) oprettet paa pause." + (" Id'er staar i opret_log.txt." if made else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
