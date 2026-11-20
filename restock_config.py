"""Auto restock: hvilke offers der fyldes op automatisk, og hvad hvert offer maks skal op til. Bruges af siden "Auto restock"
i dashboardet. Valget staar i auto_restock.json (i samme mappe som keys.txt) - dashboardet starter et offer.py-program pr. offer
og offer.py laeser maks-lageret derfra hver runde, saa et nyt tal virker uden genstart.

Foer du gemmer noget paa siden findes filen ikke, og dashboardet starter de to programmer det altid har startet (det originale
12 Months-offer og 2 Years-offeret, begge op til 100).
"""
import json
import socket
import threading
import time
from pathlib import Path

import offer as O
import opret_offer as C

CONFIG = Path("auto_restock.json")
MAX_ENTRIES = 40
MAX_TARGET = 9999
PORT_BASE = 47240                  # lock port per offer (47234 and 47235 are the two old programs)
LEGACY_ORIGINAL_ID = "bf70b7ff-a242-4073-ad3a-08df2f3fdeae"
LEGACY_TARGET = 100
INFO_MODES = ("auto", "1ar", "2ar", "default")
_lock = threading.Lock()


def clean_entries(raw):
    """What the page sends -> [{"id", "target", "info"}]. Raises ValueError with a short code."""
    if not isinstance(raw, list) or len(raw) > MAX_ENTRIES:
        raise ValueError("bad list")
    out, seen = [], set()
    for e in raw:
        if not isinstance(e, dict):
            raise ValueError("bad list")
        oid = e.get("id")
        if not isinstance(oid, str) or not C.UUID_RE.match(oid):
            raise ValueError("bad offer id")
        if oid in seen:
            continue
        seen.add(oid)
        t = e.get("target")
        if not isinstance(t, int) or isinstance(t, bool) or not 1 <= t <= MAX_TARGET:
            raise ValueError("bad max stock")
        info = e.get("info", "auto")
        if info not in INFO_MODES:
            raise ValueError("bad info")
        out.append({"id": oid, "target": t, "info": info})
    return out


def load():
    """The saved entries (with title and port), or None when nothing was ever saved (or the file is broken)."""
    with _lock:
        try:
            data = json.loads(CONFIG.read_text(encoding="utf-8"))
            ents = data.get("entries")
            if not isinstance(ents, list):
                return None
            return [e for e in ents if isinstance(e, dict) and isinstance(e.get("id"), str)]
        except (OSError, ValueError, AttributeError):
            return None


def save(entries):
    with _lock:
        tmp = CONFIG.with_suffix(".tmp")
        tmp.write_text(json.dumps({"version": 1, "saved": time.strftime("%Y-%m-%d %H:%M:%S"), "entries": entries}, ensure_ascii=False, indent=1),
                       encoding="utf-8")
        tmp.replace(CONFIG)


def _port_free(port):
    """True when nothing listens on the lock port (a program that was taken off the list may still hold it for a few minutes)."""
    sk = socket.socket()
    try:
        sk.bind(("127.0.0.1", port))
        return True
    except OSError:
        return False
    finally:
        sk.close()


def assign(entries, titles, old=None, preferred=None, free=_port_free):
    """Adds title and a lock port to each entry. An offer keeps the port it had; the two offers the old programs looked after
    keep their old ports (47234 / 47235); the others get the next free one."""
    keep = {e["id"]: e.get("port") for e in (old or []) if isinstance(e.get("port"), int)}
    for oid, port in (preferred or {}).items():
        keep.setdefault(oid, port)
    used = {keep[e["id"]] for e in entries if e["id"] in keep}
    out, nxt = [], PORT_BASE
    for e in entries:
        port = keep.get(e["id"])
        if port is None:
            while nxt in used or not free(nxt):
                nxt += 1
            port = nxt
            used.add(port)
        out.append({**e, "title": titles.get(e["id"], ""), "port": port})
    return out


def info_for(mode, title, loader=None):
    """Which Additional info file an offer uses. Returns (kind, file_name, problem); problem is '' or nokind | nofile | noplaceholder | toolong."""
    loader = loader or C.info_text
    kind = "default" if mode == "default" else mode if mode in ("1ar", "2ar") else C.kind_of_title(title)
    if not kind:
        return "", "", "nokind"
    text, fname = loader(kind)
    if text is None:
        return kind, fname, "nofile"
    if O.PLACEHOLDER not in text:
        return kind, fname, "noplaceholder"
    if len(O.tidy_info(text).replace(O.PLACEHOLDER, "X" * 25)) > O.MAX_INFO:
        return kind, fname, "toolong"
    return kind, fname, ""


def program_args(entry, fname):
    """The command line for one offer's offer.py program."""
    return ["auto", "--id", entry["id"], "--target", str(entry["target"]), "--info", fname, "--port", str(entry["port"]), "--managed"]


def program_name(offer_id):
    return "restock-" + offer_id[:8]


def legacy_ids(offers):
    """The offers the two old programs look after: {"offer": original 12 Months id or None, "offer2": the 'netflix' + '2 year' offer or None}."""
    orig = LEGACY_ORIGINAL_ID if any(o["id"] == LEGACY_ORIGINAL_ID for o in offers) else None
    hits = [o for o in offers if all(w in o["title"].lower() for w in ("netflix", "2 year")) and o["id"] != LEGACY_ORIGINAL_ID]
    return {"offer": orig, "offer2": hits[0]["id"] if len(hits) == 1 else None}


def legacy_2year_state(offers):
    """Why the old 2 Years program can or cannot find its offer: ok | ambiguous (several offers fit) | none."""
    hits = [o for o in offers if all(w in o["title"].lower() for w in ("netflix", "2 year")) and o["id"] != LEGACY_ORIGINAL_ID]
    return "ok" if len(hits) == 1 else "ambiguous" if hits else "none"


def legacy_entries(offers):
    """What runs today without a saved list: the original 12 Months offer (standard text) and the 2 Years offer, both up to 100."""
    leg = legacy_ids(offers)
    out = []
    if leg["offer"]:
        out.append({"id": leg["offer"], "target": LEGACY_TARGET, "info": "default"})
    if leg["offer2"]:
        out.append({"id": leg["offer2"], "target": LEGACY_TARGET, "info": "2ar"})
    return out


def legacy_ports(offers):
    leg = legacy_ids(offers)
    return {leg[k]: port for k, port in (("offer", 47234), ("offer2", 47235)) if leg[k]}


def info_status(loader=None):
    out = {}
    for k in ("1ar", "2ar", "default"):
        text, name = (loader or C.info_text)(k)
        out[k] = {"file": name, "found": text is not None, "ok": bool(text) and O.PLACEHOLDER in text}
    return out


def make_plan(client, entries, keys_left, loader=None, old=None):
    """What saving would do. Reads each offer from Eldorado (changes nothing).
    Item status: ok | skip (reason). Also lists the offers that were on the old list and now are not."""
    items = []
    for e in entries:
        it = {"id": e["id"], "target": e["target"], "info": e["info"], "status": "ok", "reason": "", "msg": "", "title": "", "state": "",
              "stock": None, "missing": 0, "kind": "", "info_file": ""}
        items.append(it)
        try:
            src = C.private(client, e["id"])
        except Exception as ex:                                   # any read problem: do not save blind
            it.update(status="skip", reason="read", msg=C.err_text(ex))
            continue
        if not src.get("offerTitle"):
            it.update(status="skip", reason="read", msg="no title")
            continue
        it.update(title=src["offerTitle"], state=src.get("offerState") or "", stock=src.get("quantity"))
        if isinstance(it["stock"], int):
            it["missing"] = max(0, e["target"] - it["stock"])
        kind, fname, problem = info_for(e["info"], src["offerTitle"], loader)
        it.update(kind=kind, info_file=fname)
        if problem:
            it.update(status="skip", reason=problem, msg=fname if problem != "nokind" else "")
    now_ids = {e["id"] for e in entries}
    removed = [{"id": o["id"], "title": o.get("title", "")} for o in (old or []) if o["id"] not in now_ids]
    return {"items": items, "ok": sum(1 for i in items if i["status"] == "ok"), "keys": keys_left, "removed": removed,
            "need": sum(i["missing"] for i in items if i["status"] == "ok")}
