"""Lægger N keys op i hvert af de offers du vælger. Bruges af siden "Fyld op" i dashboardet (knapperne).

Du vælger offers og skriver hvor mange keys hvert offer skal have (fx 10 offers x 5 keys = 50 keys). Teksten i Additional
info vaelges automatisk ud fra titlen: "1 year" / "12 months" bruger info_1ar.txt (ellers additional_info.txt), "2 years"
bruger info_2ar.txt. Keys tages fra keys.txt (og keys_inbox.txt) - de samme som restock bruger - og flyttes til
keys_used.txt naar de er lagt op.

Samme maade som offer.py: en key ad gangen til /secretDetails (Scroll Down i felterne + Additional info). Afviser Eldorado
keys (graensen for hvor mange der kan lægges op ad gangen), holder den pause i 5 minutter og proever igen med de keys der er tilbage.
Efter hvert offer laeses lageret tilbage: gik det ikke op med antallet af keys, stopper alt (saa der ikke bruges flere keys forgæves).
"""
import json
import threading
import time
from pathlib import Path

import requests

import offer as O
import opret_offer as C

MAX_OFFERS = 40
MAX_PER_OFFER = 200
PAUSE_ERROR = 300            # seconds to wait when Eldorado refuses keys (the same as offer.py)
MAX_ROUNDS = 6               # how many times it waits and tries again for one offer
LOG_JSON = Path("fyld_log.json")
_log_lock = threading.Lock()


def clean_args(j):
    """Checks what the page sends. Returns (ids, keys_each, info_mode). Raises ValueError with a short code."""
    ids = j.get("ids")
    if not isinstance(ids, list) or not ids:
        raise ValueError("no offers chosen")
    seen = []
    for x in ids:
        if not isinstance(x, str) or not C.UUID_RE.match(x):
            raise ValueError("bad offer id")
        if x not in seen:
            seen.append(x)
    if len(seen) > MAX_OFFERS:
        raise ValueError(f"at most {MAX_OFFERS} offers at a time")
    n = j.get("n")
    if not isinstance(n, int) or isinstance(n, bool) or not 1 <= n <= MAX_PER_OFFER:
        raise ValueError("bad number of keys")
    info = j.get("info", "auto")
    if info not in ("auto", "1ar", "2ar"):
        raise ValueError("bad info")
    return seen, n, info


# ---------------------------------------------------------------- log (what the page added)

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


# ---------------------------------------------------------------- list and plan (changes nothing)

def list_offers(client):
    """Your offers for the page: the same list as the Create page, plus which Additional info text each one would use."""
    out = C.list_offers(client)
    for o in out:
        o["kind"] = C.kind_of_title(o["title"]) or ""
    return out


def make_plan(client, ids, n, info_mode="auto", keys_left=None, loader=None):
    """What would be added. Reads each offer from Eldorado, changes nothing.
    Item status: ok | skip (reason) | nokeys.  item["keys"] = how many keys it will get (less than n when the keys run out).
    Items starting with _ are internal (not for the page)."""
    loader = loader or C.info_text
    items = []
    for oid in ids:
        it = {"id": oid, "status": "ok", "reason": "", "msg": "", "title": "", "state": "", "quantity": None, "kind": "", "info_file": "",
              "want": n, "keys": 0, "added": 0, "before": None, "after": None}
        items.append(it)
        try:
            src = C.private(client, oid)
        except requests.RequestException as e:
            it.update(status="skip", reason="read", msg=C.err_text(e))
            continue
        if not src.get("offerTitle"):
            it.update(status="skip", reason="read", msg="no title")
            continue
        it.update(title=src["offerTitle"], state=src.get("offerState") or "", quantity=src.get("quantity"))
        kind = info_mode if info_mode in ("1ar", "2ar") else C.kind_of_title(src["offerTitle"])
        if not kind:
            it.update(status="skip", reason="nokind")
            continue
        text, fname = loader(kind)
        it.update(kind=kind, info_file=fname)
        if text is None:
            it.update(status="skip", reason="nofile", msg=fname)
            continue
        if O.PLACEHOLDER not in text:
            it.update(status="skip", reason="noplaceholder", msg=fname)
            continue
        length = len(O.tidy_info(text).replace(O.PLACEHOLDER, "X" * 25))
        if length > O.MAX_INFO:
            it.update(status="skip", reason="toolong", msg=f"{fname}: {length}/{O.MAX_INFO}")
            continue
    left = keys_left if keys_left is not None else None
    for it in items:
        if it["status"] != "ok":
            continue
        if left is None:
            it["keys"] = n
            continue
        it["keys"] = min(n, left)
        left -= it["keys"]
        if it["keys"] == 0:
            it["status"] = "nokeys"
    return {"items": items, "keys": keys_left, "ok": sum(1 for i in items if i["status"] == "ok"),
            "total": sum(i["keys"] for i in items if i["status"] == "ok")}


def public_plan(plan):
    return {"keys": plan["keys"], "ok": plan["ok"], "total": plan["total"],
            "items": [{k: v for k, v in it.items() if not k.startswith("_")} for it in plan["items"]]}


# ---------------------------------------------------------------- execution

def _post_key(client, offer_id, text, key):
    """Adds ONE key. Raises requests.HTTPError when Eldorado refuses it (then nothing was added)."""
    path = f"/api/flexibleOffersUser/me/offers/{offer_id}/secretDetails"
    try:
        client.request("POST", path, json=O.account_body(text, key))
    except requests.HTTPError as e:
        r = e.response
        # the same fallback as offer.py: if Eldorado does not accept the text in the fields, use the old "." filler
        if r is not None and r.status_code in (400, 422) and "maximum length" not in r.text:
            client.request("POST", path, json=O.account_body(text, key, "."))
        else:
            raise


def _wait(seconds, stop, sleep):
    for _ in range(int(seconds)):
        if stop():
            return
        sleep(1)


def _verify(client, it, sleep, settle):
    """Reads the stock back. True = it went up by the number of keys added (or it could not be read)."""
    sleep(settle)
    after = None
    for _ in range(3):
        try:
            after = C.private(client, it["id"]).get("quantity")
        except requests.RequestException:
            after = None
        if after is not None and it["before"] is not None and after >= it["before"] + it["added"]:
            break
        sleep(settle)
    it["after"] = after
    return not (after is not None and it["before"] is not None and after < it["before"] + it["added"])


def execute(client, plan, keys, emit=lambda msg=None: None, stop=lambda: False, loader=None, pause=PAUSE_ERROR, sleep=time.sleep, settle=3):
    """Adds the keys offer by offer. Stops at the first real problem. Returns {"added": n, "state": "done"|"stopped"|"failed", "error": text}."""
    loader = loader or C.info_text
    todo = [it for it in plan["items"] if it["status"] == "ok" and it["keys"] > 0]
    total = 0

    def finish(it, stopped=False):
        """Reads the stock back after an offer. Returns an error text or ''."""
        if it["added"] == 0:
            return ""
        entry = {"time": time.strftime("%Y-%m-%d %H:%M:%S"), "id": it["id"], "title": it["title"], "added": it["added"],
                 "before": it["before"], "info": it["info_file"]}
        if not _verify(client, it, sleep, settle):
            it.update(status="check", reason="stock", msg=f"Stock {it['before']} -> {it['after']} (should be {it['before'] + it['added']})")
            entry["after"] = it["after"]
            log_add(entry)
            return it["msg"]
        entry["after"] = it["after"]
        log_add(entry)
        if not stopped:
            it["status"] = "done" if it["added"] >= it["keys"] else "part"
        return ""

    for it in todo:
        if stop():
            return {"added": total, "state": "stopped", "error": ""}
        it["status"] = "working"
        emit()
        text, fname = loader(it["kind"])
        try:
            it["before"] = C.private(client, it["id"]).get("quantity")
        except requests.RequestException as e:
            msg = C.err_text(e)
            it.update(status="failed", reason="read", msg=msg)
            emit()
            return {"added": total, "state": "failed", "error": msg}
        rounds, why = 0, ""
        while it["added"] < it["keys"]:
            if stop():
                why = "stopped"
                break
            try:
                key = keys.take()
            except RuntimeError as e:
                it.update(status="failed", reason="keys", msg=str(e)[:300])
                emit()
                return {"added": total, "state": "failed", "error": str(e)[:300]}
            if key is None:
                why = "nokeys"
                break
            try:
                O.check_info_length(text, key)
            except SystemExit as e:
                keys.give_back(key)
                it.update(status="failed", reason="toolong", msg=str(e)[:300])
                emit()
                return {"added": total, "state": "failed", "error": str(e)[:300]}
            try:
                _post_key(client, it["id"], text, key)
            except requests.HTTPError as e:                       # Eldorado answered with a refusal: this key was NOT added
                keys.give_back(key)
                code = e.response.status_code if e.response is not None else 0
                msg = C.err_text(e)
                if code in (401, 403):
                    finish(it)
                    it.update(status="failed", reason="denied", msg=msg)
                    emit()
                    return {"added": total, "state": "failed", "error": "no permission to add accounts: " + msg}
                rounds += 1
                if rounds > MAX_ROUNDS:
                    finish(it)
                    it.update(status="failed", reason="refused", msg=msg)
                    emit()
                    return {"added": total, "state": "failed", "error": msg}
                it.update(status="waiting", reason="limit", msg=msg)
                emit(f"Eldorado refused a key ({code}). Waiting {pause // 60} min, then I try again ({rounds}/{MAX_ROUNDS}).")
                _wait(pause, stop, sleep)
                it.update(status="working", reason="", msg="")
                emit()
                continue
            except requests.RequestException as e:                # no answer at all: the key may or may not have been added
                keys.unsure(key)
                msg = C.err_text(e)
                finish(it)
                it.update(status="failed", reason="unsure", msg=msg)
                emit()
                return {"added": total, "state": "failed", "error": msg}
            keys.used(key)
            it["added"] += 1
            total += 1
            emit()
        err = finish(it, stopped=bool(why))
        if err:
            emit()
            return {"added": total, "state": "failed", "error": err}
        if why == "stopped":
            it["status"] = "part" if it["added"] else "ok"
            emit()
            return {"added": total, "state": "stopped", "error": ""}
        if why == "nokeys":
            it["status"] = "part" if it["added"] else "nokeys"
            emit("out of keys")
            return {"added": total, "state": "failed", "error": "out of keys"}
        emit()
    return {"added": total, "state": "done", "error": ""}
