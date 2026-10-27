"""Web dashboard for your shop: sales, orders, stock, reviews and keys, with a login for many users.

READ ONLY on Eldorado. One background thread fetches the data from Eldorado every few
seconds and keeps it in memory, so any number of people can have the page open without
adding load on Eldorado. The sales numbers come from ledger.json, exactly like the Discord
sales board, so both always show the same.

Needs the other scripts in the SAME folder (order_alerts.py, stock_board.py, review_alerts.py,
eldorado_client.py) and your normal .env. order_alerts.py should be running (it keeps
ledger.json up to date).

Install once:   py -m pip install flask waitress pywebpush     (pywebpush = notifications when the app is closed)
First user:     py dashboard.py adduser YOURNAME --admin      (add --show to see the password while you type)
More users:     py dashboard.py adduser NAME          (or as admin, on the page: "Users")
Run:            py dashboard.py                        -> open  http://localhost:8000
Try it with fake data (no Eldorado needed):   py dashboard.py demo

Optional in .env:
  DASHBOARD_PORT=8000            DASHBOARD_HOST=0.0.0.0
  DASHBOARD_POLL_SECONDS=20      how often Eldorado is asked (default 20)
  DASHBOARD_SECRET=...           secret for the login cookies (made automatically if missing)
  DASHBOARD_HTTPS=1              set this ONLY when the site is served over https (marks cookies secure)
  DASHBOARD_LOGIN_DAYS=90        how long you stay logged in on a device (default 90, renewed on every visit)
  QUOTE=...                      the fixed quote at the top of every page (empty = no quote)
  SHOP_NAME, TIMEZONE, STOCK_CATEGORIES, STOCK_HIDE   (same as the other scripts)
"""
import argparse
import base64
import getpass
import hashlib
import json
import math
import os
import random
import re
import secrets
import sys
import threading
import time
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path

import requests
from dotenv import load_dotenv
from flask import Flask, Response, jsonify, redirect, request, session
from werkzeug.security import check_password_hash, generate_password_hash

load_dotenv()

_q = os.getenv("QUOTE")
QUOTE = ("Aldrig betal skat uden selvfølgelig" if _q is None else _q).strip()[:160]

HOST = os.getenv("DASHBOARD_HOST", "0.0.0.0")
PORT = int(os.getenv("DASHBOARD_PORT", "8000"))
POLL_SECONDS = int(os.getenv("DASHBOARD_POLL_SECONDS", "20"))
SHOP_NAME = os.getenv("SHOP_NAME", "Eldorado Shop")
USERS_FILE = Path("users.json")
# The secret that signs the login cookies. Kept next to this script (not in whatever folder you started
# it from), so the logins survive restarts and a different working folder.
SECRET_FILE = Path(__file__).resolve().parent / "dashboard_secret.key"
LOGIN_DAYS = int(os.getenv("DASHBOARD_LOGIN_DAYS", "90"))
KEYS_FILE, KEYS_USED_FILE = Path("keys.txt"), Path("keys_used.txt")
KEYS_INBOX = Path("keys_inbox.txt")  # offer.py moves these into keys.txt
KEY_RE = re.compile(r"^[^\s#]\S{3,119}$")
_keys_lock = threading.Lock()
_demo_keys = {"extra": 0, "queued": {"NETF-DEMO-WAIT-0001"}, "used": {"NETF-DEMO-SOLD-0001"}}
REFILL_LOG = Path("refill_log.json")
LEDGER_FILE_NAME = "ledger.json"
MONTH_NAMES = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
DEMO = False
ORDERS_DB, COSTS_FILE, PREFS_FILE = Path("orders_db.json"), Path("costs.json"), Path("prefs.json")
PRESENCE_FILE, DEVICES_FILE = Path("presence.json"), Path("devices.json")
CURRENCIES = ("DKK", "USD", "EUR")
SOUNDS = ("ding", "bell", "pop", "chime", "none")
NOTIFY_KINDS = ("warroom", "orders", "reviews", "keys")
OVERVIEW_TILES = ("today", "month", "all", "avg", "stock", "profit", "taxpot", "lastorder", "revrate", "pending", "reviews", "keys", "latest", "chart")
BACKGROUNDS = ("", "dots", "grid", "waves", "aurora", "diagonal")
DEFAULT_PREFS = {"lang": "", "accent": "", "currency": "", "sound": "ding", "gross": None, "tax": 37,
                 "emoji": "", "color": "", "bg": "", "hide": [],
                 "notify": {"warroom": True, "orders": False, "reviews": True, "keys": True}}

_mem = {}                      # demo mode keeps its small data files in memory only
_file_lock = threading.RLock()


def jload(path, default):
    if DEMO:
        return json.loads(json.dumps(_mem.get(path.name, default)))
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return json.loads(json.dumps(default))


def jsave(path, obj):
    if DEMO:
        _mem[path.name] = json.loads(json.dumps(obj))
        return
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False), encoding="utf-8")
    tmp.replace(path)


# fee / date helpers: the real ones live in order_alerts.py (so all scripts agree); demo mode has simple copies
DEMO_FEE = 10


def _demo_net(a):
    return round(float(a) - math.ceil(round(float(a) * DEMO_FEE, 6)) / 100, 2)


def _demo_entry_date(e):
    return datetime.fromisoformat(e["ts"]).astimezone().date().isoformat()


def _demo_today():
    return datetime.now().astimezone().date().isoformat()


def fx():
    """(fee_percent, net_of, entry_date, today_date)"""
    if DEMO:
        return DEMO_FEE, _demo_net, _demo_entry_date, _demo_today
    from order_alerts import FEE_PERCENT, entry_date, net_of, today_date
    return FEE_PERCENT, net_of, entry_date, today_date


def ledger_now():
    if DEMO:
        return demo_state()["ledger"]
    from order_alerts import LEDGER_FILE
    return jload(LEDGER_FILE, {})

app = Flask(__name__)
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.getenv("DASHBOARD_HTTPS") == "1",
    PERMANENT_SESSION_LIFETIME=timedelta(days=LOGIN_DAYS),
    SESSION_REFRESH_EACH_REQUEST=True,  # every visit pushes the expiry forward again
    MAX_CONTENT_LENGTH=512 * 1024,
)


def _secret_key():
    env = os.getenv("DASHBOARD_SECRET")
    if env:
        return env
    if not SECRET_FILE.exists():
        old = Path("dashboard_secret.key")  # earlier versions kept it in the current folder
        SECRET_FILE.write_text(old.read_text().strip() if old.exists() and old.read_text().strip() else secrets.token_hex(32))
    return SECRET_FILE.read_text().strip()


# ======================= users =======================

_users_lock = threading.Lock()
_demo_users = {}


def load_users():
    if DEMO:
        return _demo_users
    try:
        return json.loads(USERS_FILE.read_text())
    except (OSError, ValueError):
        return {}


def save_users(users):
    if DEMO:
        return
    tmp = USERS_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(users, indent=1))
    tmp.replace(USERS_FILE)


USERNAME_RE = re.compile(r"^[A-Za-z0-9_.-]{2,32}$")


def add_user(name, password, role="viewer"):
    if not USERNAME_RE.match(name or ""):
        raise ValueError("Username: 2-32 characters, letters, digits, _ . - only.")
    if len(password or "") < 8:
        raise ValueError("Password must be at least 8 characters.")
    if role not in ("admin", "viewer"):
        raise ValueError("Role must be admin or viewer.")
    with _users_lock:
        users = load_users()
        users[name.lower()] = {"name": name, "role": role, "hash": generate_password_hash(password),
                               "created": datetime.now(timezone.utc).isoformat()}
        save_users(users)


def current_user():
    name = session.get("u")
    if not name:
        return None
    u = load_users().get(name)
    if not u or not device_ok(name):
        return None
    return u


# ---------- logins and devices (a device = one logged-in browser) ----------

def client_ip():
    ip = request.remote_addr or ""
    if ip in ("127.0.0.1", "::1"):     # behind a local proxy (Caddy): the real address is in this header
        fwd = request.headers.get("X-Forwarded-For", "").split(",")[0].strip()
        if fwd:
            return fwd[:45]
    return ip[:45]


def device_label(ua):
    ua = ua or ""
    os_ = next((n for k, n in (("iPhone", "iPhone"), ("iPad", "iPad"), ("Android", "Android"), ("Windows", "Windows"),
                               ("Macintosh", "Mac"), ("Mac OS", "Mac"), ("CrOS", "Chromebook"), ("Linux", "Linux")) if k in ua), "Unknown device")
    br = next((n for k, n in (("Edg/", "Edge"), ("OPR/", "Opera"), ("SamsungBrowser", "Samsung Internet"), ("Firefox/", "Firefox"),
                              ("CriOS", "Chrome"), ("Chrome/", "Chrome"), ("Safari/", "Safari")) if k in ua), "Browser")
    return f"{br} · {os_}"


def _devs():
    data = jload(DEVICES_FILE, {})
    if not isinstance(data.get("devices"), dict):
        data["devices"] = {}
    if not isinstance(data.get("log"), list):
        data["log"] = []
    return data


def device_ok(name):
    """False if this login was ended from the Users/Settings page. Old logins are registered on their next visit."""
    did = session.get("d")
    now = datetime.now(timezone.utc)
    with _file_lock:
        data = _devs()
        devs = data["devices"]
        if did and (did not in devs or devs[did].get("user") != name):
            session.clear()
            return False
        if not did:
            did = secrets.token_hex(8)
            session["d"] = did
            devs[did] = {"user": name, "ua": request.headers.get("User-Agent", "")[:200], "ip": client_ip(),
                         "created": now.isoformat(), "seen": now.isoformat()}
            jsave(DEVICES_FILE, data)
            return True
        d = devs[did]
        try:
            old = (now - datetime.fromisoformat(d.get("seen", ""))).total_seconds()
        except ValueError:
            old = 999
        if old > 60:
            d["seen"] = now.isoformat()
            d["ip"] = client_ip()
            jsave(DEVICES_FILE, data)
    return True


def log_login(name, ok, did=None):
    now = datetime.now(timezone.utc).isoformat()
    with _file_lock:
        data = _devs()
        if ok and did:
            data["devices"][did] = {"user": name, "ua": request.headers.get("User-Agent", "")[:200], "ip": client_ip(),
                                    "created": now, "seen": now}
        data["log"].append({"time": now, "user": name[:32], "ok": ok, "ip": client_ip(),
                            "label": device_label(request.headers.get("User-Agent", ""))})
        del data["log"][:-100]
        jsave(DEVICES_FILE, data)


def drop_devices(user, keep=None):
    with _file_lock:
        data = _devs()
        data["devices"] = {k: v for k, v in data["devices"].items() if v.get("user") != user or k == keep}
        jsave(DEVICES_FILE, data)


# ---------- who is online / last seen ----------

_presence = {}
_seen_saved = {}
_typing = {}


def touch(name):
    now = time.time()
    _presence[name] = now
    if now - _seen_saved.get(name, 0) > 30:
        _seen_saved[name] = now
        with _file_lock:
            seen = jload(PRESENCE_FILE, {})
            seen[name] = datetime.now(timezone.utc).isoformat()
            jsave(PRESENCE_FILE, seen)


# ---------- per-user settings (language, colour, currency, sound, which notifications) ----------

def prefs_of(name):
    p = jload(PREFS_FILE, {}).get((name or "").lower()) or {}
    out = json.loads(json.dumps(DEFAULT_PREFS))
    for k in ("lang", "accent", "currency", "sound"):
        if isinstance(p.get(k), str):
            out[k] = p[k]
    for k in NOTIFY_KINDS:
        v = (p.get("notify") or {}).get(k)
        if isinstance(v, bool):
            out["notify"][k] = v
    if isinstance(p.get("gross"), bool):
        out["gross"] = p["gross"]
    if isinstance(p.get("tax"), (int, float)) and not isinstance(p.get("tax"), bool) and 0 <= p["tax"] <= 80:
        out["tax"] = p["tax"]
    for k in ("emoji", "color"):
        if isinstance(p.get(k), str):
            out[k] = p[k]
    if p.get("bg") in BACKGROUNDS:
        out["bg"] = p["bg"]
    if isinstance(p.get("hide"), list):
        out["hide"] = [x for x in p["hide"] if x in OVERVIEW_TILES]
    return out


# ---------- brute-force protection ----------

_fails = {}
_fails_lock = threading.Lock()
MAX_FAILS, BLOCK_SECONDS = 5, 600


def _fail_key(username):
    return f"{request.remote_addr}|{(username or '').lower()}"


def is_blocked(username):
    with _fails_lock:
        n, until = _fails.get(_fail_key(username), (0, 0))
        return until > time.time()


def register_fail(username):
    with _fails_lock:
        k = _fail_key(username)
        n, until = _fails.get(k, (0, 0))
        n += 1
        _fails[k] = (0, time.time() + BLOCK_SECONDS) if n >= MAX_FAILS else (n, 0)


def clear_fails(username):
    with _fails_lock:
        _fails.pop(_fail_key(username), None)


# ======================= data =======================

_cache = {"orders": [], "stock": {"offers": [], "units": 0}, "reviews": {"positive": 0, "negative": 0, "items": []},
          "updated": None, "errors": {}}
_cache_lock = threading.Lock()
_status = {}   # per section: last good fetch, last error, and how many fetches in a row failed


def money(m):
    m = m or {}
    return {"amount": float(m.get("amount") or 0), "currency": m.get("currency") or "USD"}


# ---------- order database (orders_db.json): every order the dashboard has seen ----------

_odb_lock = threading.Lock()
_odb = {"for": None, "orders": {}}
_odb_seen = set()              # ids that were in the newest Eldorado answer
_odb_started = {"v": False}
BLOB_MAX, DB_KEEP = 6000, 2000


def odb():
    """The orders dict. Call with _odb_lock held."""
    key = "demo" if DEMO else str(ORDERS_DB.resolve())
    if _odb["for"] != key:
        _odb["for"] = key
        data = demo_state()["orders"] if DEMO else jload(ORDERS_DB, {})
        _odb["orders"] = data if isinstance(data, dict) else {}
    return _odb["orders"]


def odb_save():
    db = _odb["orders"]
    if len(db) > DB_KEEP:
        for oid, _ in sorted(db.items(), key=lambda kv: kv[1].get("time", ""))[:len(db) - DB_KEEP]:
            del db[oid]
    if not DEMO:
        jsave(ORDERS_DB, db)


def _blob(o):
    try:
        return json.dumps(o, ensure_ascii=False).lower()[:BLOB_MAX]
    except (TypeError, ValueError):
        return ""


def pub(r, net_of):
    """An order the way the page gets it (no raw text)."""
    amt = r["price"]["amount"]
    net = net_of(amt)
    return {"id": r["id"], "time": r["time"], "state": r["state"], "item": r["item"], "quantity": r["quantity"],
            "price": r["price"], "net": net, "fee": round(amt - net, 2), "buyer": r["buyer"],
            "log": r.get("log", {}), "first": r.get("first", "")}


def ingest_orders(found, gone, order_time, net_of):
    """found = [(state, raw order)] from Eldorado. Updates orders_db.json, returns the 30 newest."""
    now = datetime.now(timezone.utc).isoformat()
    changed, fresh, seen = False, [], set()
    with _odb_lock:
        db = odb()
        for oid in gone:
            if oid in db:
                del db[oid]
                changed = True
        for state, o in found:
            oid = o["id"]
            if oid in gone:
                continue
            seen.add(oid)
            d = o.get("orderOfferDetails") or {}
            row = db.get(oid)
            if row is None:
                row = db[oid] = {"id": oid, "log": {}, "first": state}
                changed = True
                if _odb_started["v"]:
                    fresh.append(oid)
            vals = {"time": order_time(o).astimezone(timezone.utc).isoformat(), "state": state,
                    "item": d.get("offerTitle") or d.get("gameCategoryTitle") or "?",
                    "quantity": o.get("purchaseQuantity") or 1, "price": money(o.get("totalPrice")),
                    "buyer": o.get("buyerUsername") or "?", "blob": _blob(o)}
            if any(row.get(k) != v for k, v in vals.items()):
                row.update(vals)
                changed = True
            if state not in row["log"]:
                row["log"][state] = now
                changed = True
        _odb_seen.clear()
        _odb_seen.update(seen)
        if changed:
            odb_save()
        _odb_started["v"] = True
        newest = sorted(db.values(), key=lambda r: r["time"], reverse=True)[:30]
        out = [pub(r, net_of) for r in newest]
        events = [pub(db[i], net_of) for i in fresh if i in db]
    cutoff = (datetime.now(timezone.utc) - timedelta(hours=2)).isoformat()
    for e in events:
        if e["time"] >= cutoff:
            amt = f"{e['price']['amount']:.2f} {e['price']['currency']}"
            notify_event("orders", {"da": ("Ny ordre", f"{amt} · {e['buyer']}"), "en": ("New order", f"{amt} · {e['buyer']}")}, "/#orders")
    return out


def is_stale(r, now):
    """An unfinished order that Eldorado no longer lists and is older than 36 hours: we cannot know its state any more."""
    if r["state"] == "Completed" or r["id"] in _odb_seen:
        return False
    try:
        return (now - datetime.fromisoformat(r["time"])).total_seconds() > 36 * 3600
    except ValueError:
        return False


def pending_info(db, main, net_of):
    now = datetime.now(timezone.utc)
    rows = sorted((r for r in db.values() if r["state"] != "Completed" and not is_stale(r, now)), key=lambda r: r["time"])
    cur = [r for r in rows if r["price"]["currency"] == main]
    return {"n": len(rows), "currency": main, "net": round(sum(net_of(r["price"]["amount"]) for r in cur), 2),
            "gross": round(sum(r["price"]["amount"] for r in cur), 2), "rows": [pub(r, net_of) for r in rows[:8]]}


def refresh_orders(client):
    from order_alerts import fetch_canceled_ids, fetch_orders, load_ignored, net_of, order_time
    gone = fetch_canceled_ids(client) | load_ignored()
    return ingest_orders(fetch_orders(client), gone, order_time, net_of)


def refresh_stock(client):
    from stock_board import CATEGORIES, ENABLED, fetch_offers
    offers = []
    for key in ENABLED:
        for o in fetch_offers(client, CATEGORIES[key]):
            offers.append({"title": o.get("offerTitle") or o.get("gameCategoryTitle") or "?",
                           "category": CATEGORIES[key]["name"], "quantity": o.get("quantity") or 0,
                           "price": money(o.get("pricePerUnit"))})
    offers.sort(key=lambda r: r["title"].casefold())
    return {"offers": offers, "units": sum(o["quantity"] for o in offers)}


_seen_neg = {"v": None}


def refresh_reviews(client):
    from order_alerts import order_time
    from review_alerts import fetch_reviewed_orders, pretty_tag
    rows = []
    for o in fetch_reviewed_orders(client):
        r = o.get("review") or {}
        d = o.get("orderOfferDetails") or {}
        rows.append({
            "time": order_time(o).astimezone(timezone.utc).isoformat(), "order_id": o.get("id") or "",
            "rating": r.get("feedbackRating") or "?", "item": d.get("offerTitle") or "?",
            "buyer": o.get("buyerUsername") or "?", "text": (r.get("reviewMessage") or "").strip()[:600],
            "visible": r.get("isReviewMessageVisible", True),
            "tags": [pretty_tag(t) for t in (r.get("feedbackTags") or [])],
        })
    rows.sort(key=lambda r: r["time"], reverse=True)
    sig = lambda r: f"{r['order_id']}|{r['time']}"
    prev, _seen_neg["v"] = _seen_neg["v"], {sig(r) for r in rows if r["rating"] == "Negative"}
    if prev is not None:
        for r in rows:
            if r["rating"] == "Negative" and sig(r) not in prev:
                txt = r["text"][:100]
                notify_event("reviews", {"da": ("Dårlig anmeldelse", f"{r['buyer']}: {txt or 'ingen tekst'}"),
                                         "en": ("Bad review", f"{r['buyer']}: {txt or 'no text'}")}, "/#reviews")
    return {"positive": sum(1 for r in rows if r["rating"] == "Positive"),
            "negative": sum(1 for r in rows if r["rating"] == "Negative"), "items": rows[:40]}


_key_state = {"v": None}


def check_key_alert():
    """Push when the keys run low (10 or fewer) or out. Stays quiet again until there are more than 20."""
    left = keys_info()["left"]
    prev = _key_state["v"]
    if left == 0:
        state = "out"
    elif left <= 10 or (left <= 20 and prev in ("low", "out")):
        state = "low"
    else:
        state = "ok"
    _key_state["v"] = state
    if prev is not None and state != prev and state != "ok":
        if state == "out":
            texts = {"da": ("Ingen keys tilbage", "Upload nye keys nu."), "en": ("Out of keys", "Upload new keys now.")}
        else:
            texts = {"da": ("Keys er ved at løbe tør", f"Kun {left} tilbage."), "en": ("Keys running low", f"Only {left} left.")}
        notify_event("keys", texts, "/#keys")


def poll_loop():
    from eldorado_client import EldoradoClient
    client = EldoradoClient()
    delay = POLL_SECONDS
    while True:
        failed = False
        for name, fn in (("orders", refresh_orders), ("stock", refresh_stock), ("reviews", refresh_reviews)):
            try:
                result = fn(client)
                with _cache_lock:
                    _cache[name] = result
                    _cache["errors"].pop(name, None)
                    _status[name] = {"ok": datetime.now(timezone.utc).isoformat(), "err": "", "fails": 0}
            except requests.RequestException as e:
                failed = True
                code = getattr(getattr(e, "response", None), "status_code", None)
                with _cache_lock:
                    _cache["errors"][name] = f"API error {code}" if code else type(e).__name__
                    st = _status.setdefault(name, {"ok": None, "err": "", "fails": 0})
                    st["err"], st["fails"] = _cache["errors"][name], st["fails"] + 1
            except Exception as e:  # keep the other sections alive
                failed = True
                with _cache_lock:
                    _cache["errors"][name] = type(e).__name__
                    st = _status.setdefault(name, {"ok": None, "err": "", "fails": 0})
                    st["err"], st["fails"] = type(e).__name__, st["fails"] + 1
                print(f"{name}: {type(e).__name__}: {e}", flush=True)
        try:
            check_key_alert()
        except Exception as e:
            print(f"key alert: {type(e).__name__}: {e}", flush=True)
        with _cache_lock:
            _cache["updated"] = datetime.now(timezone.utc).isoformat()
        delay = min(delay * 2, 60) if failed else POLL_SECONDS
        time.sleep(delay)


# ---------- sales (from ledger.json, same numbers as the Discord board) ----------

def last_months(count, today):
    y, m = int(today[:4]), int(today[5:7])
    keys = []
    for _ in range(count):
        keys.append(f"{y}-{m:02d}")
        m -= 1
        if m == 0:
            y, m = y - 1, 12
    return keys[::-1]


def month_range(first, last):
    out, y, m = [], int(first[:4]), int(first[5:7])
    while f"{y}-{m:02d}" <= last and len(out) < 600:
        out.append(f"{y}-{m:02d}")
        m += 1
        if m == 13:
            y, m = y + 1, 1
    return out


def compute_records(days, today):
    """Best day / week / month, and whether the current one is a NEW record (needs some history to compare with)."""
    by_day = {d: v[0] for d, v in days.items()}
    by_week, by_month = {}, {}
    for d, v in days.items():
        try:
            y, w = datetime.strptime(d, "%Y-%m-%d").isocalendar()[:2]
        except ValueError:
            continue
        by_week[f"{y}-W{w:02d}"] = by_week.get(f"{y}-W{w:02d}", 0.0) + v[0]
        by_month[d[:7]] = by_month.get(d[:7], 0.0) + v[0]
    ty, tw = datetime.strptime(today, "%Y-%m-%d").isocalendar()[:2]
    cur = {"day": today, "week": f"{ty}-W{tw:02d}", "month": today[:7]}
    need = {"day": 3, "week": 1, "month": 1}
    out = {}
    for name, m in (("day", by_day), ("week", by_week), ("month", by_month)):
        best = max(m, key=lambda k: m[k], default=None)
        others = [x for k, x in m.items() if k != cur[name] and x > 0]
        now_amt = m.get(cur[name], 0.0)
        out[name] = {"key": best, "amount": round(m[best], 2) if best else 0.0,
                     "orders": days[best][1] if best and name == "day" else None,
                     "record": bool(now_amt > 0 and len(others) >= need[name] and now_amt > max(others))}
    return out


def sales_summary(ledger, today, entry_date, net_of=None, fee_percent=0):
    per = {}
    for e in ledger.values():
        d = entry_date(e)
        c = per.setdefault(e["currency"], {"today": [0.0, 0], "month": [0.0, 0], "all": [0.0, 0], "months": {}, "days": {}, "gross": {}})
        amt = net_of(e["amount"]) if net_of else float(e["amount"])
        gross = float(e["amount"])
        for k, hit in (("all", True), ("today", d == today), ("month", d[:7] == today[:7])):
            if hit:
                c[k][0] += amt
                c[k][1] += 1
                c["gross"][k] = c["gross"].get(k, 0.0) + gross
        for bucket, key in ((c["months"], d[:7]), (c["days"], d)):
            v = bucket.setdefault(key, [0.0, 0, 0.0])
            v[0] += amt
            v[1] += 1
            v[2] += gross
    main = max(per, key=lambda cur: per[cur]["all"][0], default="USD")
    blank = {"today": [0.0, 0], "month": [0.0, 0], "all": [0.0, 0], "months": {}, "days": {}, "gross": {}}
    pack = lambda v: {"amount": round(v[0], 2), "orders": v[1]}
    mc = per.get(main, blank)
    keys = last_months(12, today)
    floor = (datetime.strptime(today, "%Y-%m-%d") - timedelta(days=400)).strftime("%Y-%m-%d")
    return {
        "currency": main,
        "date": today,
        "fee_percent": fee_percent,
        "today": {**pack(mc["today"]), "gross": round(mc["gross"].get("today", 0.0), 2)},
        "month": {**pack(mc["month"]), "gross": round(mc["gross"].get("month", 0.0), 2)},
        "all": {**pack(mc["all"]), "gross": round(mc["gross"].get("all", 0.0), 2)},
        "months": [{"key": k, "label": f"{MONTH_NAMES[int(k[5:7]) - 1]} {k[:4]}", "short": MONTH_NAMES[int(k[5:7]) - 1],
                    **pack(mc["months"].get(k, [0.0, 0, 0.0])), "gross": round(mc["months"].get(k, [0, 0, 0.0])[2], 2)} for k in keys],
        "days": {d: {"a": round(v[0], 2), "n": v[1], "g": round(v[2], 2)} for d, v in mc["days"].items() if d >= floor},
        "records": compute_records(mc["days"], today),
        "others": [{"currency": cur, "today": pack(v["today"]), "month": pack(v["month"]), "all": pack(v["all"])}
                   for cur, v in sorted(per.items()) if cur != main],
    }


# ---------- currency rates (shown as a conversion only: Eldorado pays out in its own currency) ----------

RATES_URL = "https://api.frankfurter.dev/v1/latest"
RATES_TTL = 6 * 3600
RATE_FALLBACK = {"USD": 1.0, "EUR": 0.86, "DKK": 6.45}   # rough numbers, only used while the live rates are not available
_rates = {"base": None, "data": {}, "live": False, "date": None, "at": 0.0, "busy": False}


def _fetch_rates(base):
    try:
        symbols = ",".join(c for c in CURRENCIES if c != base)
        r = requests.get(RATES_URL, params={"base": base, "symbols": symbols}, timeout=6)
        r.raise_for_status()
        j = r.json()
        data = {k: float(v) for k, v in (j.get("rates") or {}).items() if k in CURRENCIES and float(v) > 0}
        if not data:
            raise ValueError("no rates in answer")
        data[base] = 1.0
        _rates.update(base=base, data=data, live=True, date=j.get("date"), at=time.time())
    except Exception as e:
        _rates["at"] = time.time() - RATES_TTL + 300   # try again in 5 minutes
        print(f"Currency rates not available right now ({type(e).__name__}); using rough numbers.", flush=True)
    finally:
        _rates["busy"] = False


def get_rates(base):
    """Units of each currency per 1 `base`. Never blocks: asks the internet in the background."""
    if not DEMO and (_rates["base"] != base or time.time() - _rates["at"] > RATES_TTL) and not _rates["busy"]:
        _rates["busy"] = True
        threading.Thread(target=_fetch_rates, args=(base,), daemon=True).start()
    if _rates["base"] == base and _rates["data"]:
        return {"base": base, "rates": dict(_rates["data"]), "live": _rates["live"], "date": _rates["date"]}
    if base in RATE_FALLBACK:
        data = {c: round(RATE_FALLBACK[c] / RATE_FALLBACK[base], 6) for c in CURRENCIES}
    else:
        data = {base: 1.0}
    return {"base": base, "rates": data, "live": False, "date": None}


# ---------- costs and real profit (costs.json) ----------

def load_costs():
    j = jload(COSTS_FILE, {})
    items = [i for i in (j.get("items") or []) if isinstance(i, dict) and "amount" in i]
    kc = j.get("key_cost") if isinstance(j.get("key_cost"), dict) else {}
    return items, {"amount": float(kc.get("amount") or 0), "currency": kc.get("currency") if kc.get("currency") in CURRENCIES else "USD"}


def save_costs(items, kc):
    jsave(COSTS_FILE, {"items": items, "key_cost": kc})


def to_main(amount, cur, rates):
    r = rates["rates"].get(cur)
    return float(amount) / r if r else float(amount)


def profit_calc():
    fee, net_of, entry_date, today_date = fx()
    today = today_date()
    per = {}
    for e in ledger_now().values():
        v = per.setdefault(e["currency"], {}).setdefault(entry_date(e)[:7], [0.0, 0, 0])
        v[0] += net_of(e["amount"])
        v[1] += 1
        v[2] += int(e.get("qty") or 1)
    main = max(per, key=lambda c: sum(x[0] for x in per[c].values()), default="USD")
    sales = per.get(main, {})
    items, kc = load_costs()
    rates = get_rates(main)
    first = min([today[:7], *sales, *((i.get("date") or today)[:7] for i in items)])
    rows = []
    for m in month_range(first, today[:7]):
        s, n, units = sales.get(m, [0.0, 0, 0])
        costs = 0.0
        for i in items:
            start = (i.get("date") or today)[:7]
            if (i.get("kind") == "monthly" and start <= m) or (i.get("kind") != "monthly" and start == m):
                costs += to_main(i["amount"], i["currency"], rates)
        keys = units * to_main(kc["amount"], kc["currency"], rates)
        rows.append({"key": m, "label": f"{MONTH_NAMES[int(m[5:7]) - 1]} {m[:4]}", "sales": round(s, 2), "orders": n, "units": units,
                     "costs": round(costs, 2), "keys": round(keys, 2), "profit": round(s - costs - keys, 2)})
    total = {k: round(sum(r[k] for r in rows), 2) for k in ("sales", "costs", "keys", "profit")}
    total["orders"] = sum(r["orders"] for r in rows)
    cur = next((r for r in rows if r["key"] == today[:7]), None) or {"sales": 0, "costs": 0, "keys": 0, "profit": 0, "orders": 0}
    return {"currency": main, "months": rows[::-1][:36], "total": total, "this_month": cur, "rates_live": rates["live"]}


def profit_brief():
    p = profit_calc()
    dkk = get_rates(p["currency"])
    # how much that profit is in kroner (for the tax pot): rates are "units per 1 main currency"
    return {"currency": p["currency"], "month": p["this_month"]["profit"], "all": p["total"]["profit"],
            "month_dkk": round(p["this_month"]["profit"] * dkk["rates"].get("DKK", 1), 2),
            "all_dkk": round(p["total"]["profit"] * dkk["rates"].get("DKK", 1), 2), "dkk_live": dkk["live"]}


# ---------- history: when money was added (new order) and taken off again (cancelled) ----------

def _demo_history(led):
    rnd = random.Random(11)
    rows = sorted(led.items(), key=lambda kv: kv[1]["ts"], reverse=True)[:70]
    out = []
    for i, (oid, e) in enumerate(rows):
        out.append({"t": e["ts"], "k": "add", "id": oid, "ots": e["ts"], "amount": e["amount"], "currency": e["currency"],
                    "buyer": e.get("buyer", ""), "item": e.get("item", ""), "qty": e.get("qty", 1)})
        if i % 11 == 7:   # a few of them got cancelled later
            t = datetime.fromisoformat(e["ts"]) + timedelta(minutes=rnd.randint(20, 400))
            if t < datetime.now(timezone.utc):
                out.append({"t": t.isoformat(), "k": "remove", "id": oid[:-2] + "ff", "ots": e["ts"], "amount": e["amount"],
                            "currency": e["currency"], "buyer": e.get("buyer", ""), "item": e.get("item", ""), "qty": 1})
    return out


def history_view(kind, limit, offset):
    fee, net_of, entry_date, today_date = fx()
    led = ledger_now()
    if DEMO:
        st = demo_state()
        if "history" not in st:
            st["history"] = _demo_history(led)
        raw = st["history"]
    else:
        from order_alerts import HISTORY_FILE
        raw = jload(HISTORY_FILE, [])
    ev, have = [], set()
    for r in raw if isinstance(raw, list) else []:
        if isinstance(r, dict) and r.get("k") in ("add", "remove") and r.get("t"):
            ev.append(r)
            if r["k"] == "add":
                have.add(r.get("id"))
    for oid, e in led.items():     # orders from before the history started: shown as added when they came in
        if oid not in have:
            ts = e.get("ts") or (e.get("date", "1970-01-01") + "T12:00:00+00:00")
            ev.append({"t": ts, "k": "add", "id": oid, "ots": ts, "amount": e["amount"], "currency": e["currency"],
                       "buyer": e.get("buyer", ""), "item": e.get("item", ""), "qty": e.get("qty", 1), "old": True})
    ev.sort(key=lambda r: r["t"], reverse=True)
    per = {}
    for e in led.values():
        per[e["currency"]] = per.get(e["currency"], 0.0) + net_of(e["amount"])
    main = max(per, key=per.get, default="USD")
    run = round(per.get(main, 0.0), 2)
    today = today_date()
    tot = {"added_today": 0.0, "removed_today": 0.0, "added_month": 0.0, "removed_month": 0.0, "n_added_today": 0, "n_removed_today": 0}
    out = []
    for r in ev:
        net = net_of(r["amount"])
        sign = 1 if r["k"] == "add" else -1
        d = entry_date({"ts": r["t"], "date": r["t"][:10]})
        if r["currency"] == main:
            if d == today:
                tot[("added" if sign > 0 else "removed") + "_today"] += net
                tot["n_" + ("added" if sign > 0 else "removed") + "_today"] += 1
            if d[:7] == today[:7]:
                tot[("added" if sign > 0 else "removed") + "_month"] += net
        bal = run if r["currency"] == main else None
        if r["currency"] == main:
            run = round(run - sign * net, 2)
        if kind in ("add", "remove") and r["k"] != kind:
            continue
        out.append({"id": r.get("id", ""), "t": r["t"], "k": r["k"], "net": net, "gross": round(float(r["amount"]), 2),
                    "currency": r["currency"], "buyer": r.get("buyer", ""), "item": r.get("item", ""), "qty": r.get("qty", 1),
                    "old": bool(r.get("old")), "est": bool(r.get("est")), "bal": bal})
    tot = {k: round(v, 2) if isinstance(v, float) else v for k, v in tot.items()}
    page = out[offset:offset + limit]
    return {"events": page, "more": len(out) > offset + limit, "total": len(out), "currency": main, "balance": round(per.get(main, 0.0), 2), **tot}


def stock_forecast(left):
    """Keys sold per day over the last 7 days, and how long the stock then lasts."""
    now = datetime.now(timezone.utc)
    units = 0
    for e in ledger_now().values():
        try:
            t = datetime.fromisoformat(e["ts"])
        except (KeyError, ValueError):
            continue
        if now - t <= timedelta(days=7):
            units += int(e.get("qty") or 1)
    per_day = units / 7.0
    if per_day <= 0:
        return {"per_day": 0, "days": None, "units7": units}
    days = left / per_day
    return {"per_day": round(per_day, 1), "days": round(days, 1), "units7": units,
            "empty_at": (now + timedelta(days=days)).isoformat()}


# ---------- keys ----------

def read_key_lines(path):
    try:
        return [l.strip() for l in path.read_text(encoding="utf-8").splitlines() if l.strip() and not l.strip().startswith("#")]
    except OSError:
        return []


def key_sets():
    """(waiting in the queue, already uploaded to Eldorado)"""
    if DEMO:
        return set(_demo_keys["queued"]), set(_demo_keys["used"])
    return set(read_key_lines(KEYS_FILE)) | set(read_key_lines(KEYS_INBOX)), set(read_key_lines(KEYS_USED_FILE))


def keys_info():
    if DEMO:
        return {"left": 42 + _demo_keys["extra"], "used": 318, "refills": demo_state()["refills"]}
    try:
        log = json.loads(REFILL_LOG.read_text())
    except (OSError, ValueError):
        log = []
    queued = len(read_key_lines(KEYS_FILE)) + len(read_key_lines(KEYS_INBOX))
    return {"left": queued, "used": len(read_key_lines(KEYS_USED_FILE)), "refills": log[-15:][::-1]}


def log_refill(added, before, after, left):
    """Used by offer.py auto, kept here so the format lives in one place."""
    try:
        log = json.loads(REFILL_LOG.read_text())
    except (OSError, ValueError):
        log = []
    log.append({"time": datetime.now(timezone.utc).isoformat(), "added": added, "before": before,
                "after": after, "left": left})
    REFILL_LOG.write_text(json.dumps(log[-200:]))


# ---------- demo data (only used by `py dashboard.py demo`) ----------

_demo = {}


def demo_state():
    if _demo:
        return _demo
    rnd = random.Random(7)
    now = datetime.now(timezone.utc)
    buyers = ["FieryFang-hHOT", "ShadowKid22", "LunaPlays", "nordic_gamer", "xXMaxXx", "StreamQueen", "Tobias_K",
              "pixelpanda", "KaffeKarl", "RavenWing", "mille_m", "SolidSnake88"]
    items = [("Netflix Premium 1 Year", 6.0)] * 4 + [("Disney+ Premium 1 Year", 5.5), ("Crunchyroll Mega Fan 1 Year", 4.0)]
    ledger = {}

    def add(ts):
        item, amt = rnd.choice(items)
        oid = str(uuid.UUID(int=rnd.getrandbits(128), version=4))
        ledger[oid] = {"ts": ts.isoformat(), "date": ts.astimezone().date().isoformat(), "amount": amt, "currency": "USD",
                       "buyer": rnd.choice(buyers), "item": item, "qty": 1}

    for back in range(150, 0, -1):
        day = now - timedelta(days=back)
        lam = 0.4 + (150 - back) / 150 * 3.6 + (1.0 if day.weekday() >= 5 else 0.0)
        for _ in range(max(0, min(6, round(rnd.gauss(lam, 1.2))))):
            ts = day + timedelta(hours=rnd.uniform(-11, 11))
            if ts < now - timedelta(minutes=30):
                add(ts)
    for k in range(8):
        add(now - timedelta(minutes=4 + k * 6))
    newest = sorted(ledger.items(), key=lambda kv: kv[1]["ts"], reverse=True)
    orders = {}
    for k, (oid, e) in enumerate(newest[:45]):
        t0 = datetime.fromisoformat(e["ts"])
        state = "Paid" if k == 0 else "Delivered" if k in (1, 2, 9) else "Received" if k == 3 else "Completed"
        steps = STATE_ORDER[:STATE_ORDER.index(state) + 1]
        recent = k < 12
        log = {s: (t0 + timedelta(minutes=[0, 2, 20, 26][i])).isoformat() for i, s in enumerate(steps)} if recent \
            else {"Completed": (t0 + timedelta(hours=1)).isoformat()}
        blob = {"id": oid, "buyer": e["buyer"], "item": e["item"]}
        if k == 1:
            blob["deliveredkey"] = "NETF-DEMO-SOLD-0001"
        orders[oid] = {"id": oid, "time": e["ts"], "state": state, "item": e["item"], "quantity": 1,
                       "price": {"amount": e["amount"], "currency": "USD"}, "buyer": e["buyer"],
                       "log": log, "first": "Paid" if recent else "Completed", "blob": json.dumps(blob).lower()}
    texts = ["Fast and easy, thanks!", "Worked perfectly, will buy again.", "Took a while but support helped.", "",
             "Great seller!", "Link expired after a day, had to use Replace.", "Perfect, 10/10", "All good.", "",
             "Account stopped working after 3 days, no reply yet.", "Quick delivery.", "Thanks a lot!", "Good price", "Smooth."]
    revs = []
    for i, t in enumerate(texts):
        o = orders[newest[i + 3][0]] if i + 3 < len(newest) else None
        bad = i in (5, 9)
        revs.append({"time": (now - timedelta(hours=3 + i * 9)).isoformat(), "order_id": o["id"] if o else "",
                     "rating": "Negative" if bad else "Positive", "item": "Netflix Premium 1 Year",
                     "buyer": o["buyer"] if o else buyers[i % len(buyers)], "text": t, "visible": True,
                     "tags": [] if bad else ["Fast Delivery"] if i % 2 == 0 else ["Fast Delivery", "Good Communication"]})
    stock = {"offers": [
        {"title": "Netflix Premium 1 Year", "category": "Accounts", "quantity": 100, "price": {"amount": 6.0, "currency": "USD"}},
        {"title": "Disney+ Premium 1 Year", "category": "Accounts", "quantity": 24, "price": {"amount": 5.5, "currency": "USD"}},
        {"title": "Crunchyroll Mega Fan 1 Year", "category": "Accounts", "quantity": 9, "price": {"amount": 4.0, "currency": "USD"}}], "units": 133}
    refills = [
        {"time": (now - timedelta(minutes=12)).isoformat(), "added": 3, "before": 97, "after": 100, "left": 42},
        {"time": (now - timedelta(hours=1, minutes=5)).isoformat(), "added": 5, "before": 95, "after": 100, "left": 45},
        {"time": (now - timedelta(hours=3)).isoformat(), "added": 1, "before": 99, "after": 100, "left": 50}]
    _demo.update(ledger=ledger, orders=orders, refills=refills)
    with _cache_lock:
        _cache["stock"] = stock
        _cache["reviews"] = {"positive": 46, "negative": 2, "items": revs}
        _cache["updated"] = now.isoformat()
    return _demo


def build_payload():
    fee, net_of, entry_date, today_date = fx()
    if DEMO:
        demo_state()
    sales = sales_summary(ledger_now(), today_date(), entry_date, net_of, fee)
    with _cache_lock:
        d = {k: json.loads(json.dumps(v)) for k, v in _cache.items()}
    with _odb_lock:
        db = odb()
        d["orders"] = [pub(r, net_of) for r in sorted(db.values(), key=lambda r: r["time"], reverse=True)[:30]]
        d["pending"] = pending_info(db, sales["currency"], net_of)
    d["sales"] = sales
    d["keys"] = keys_info()
    d["keys"]["forecast"] = stock_forecast(d["keys"]["left"])
    d["status"] = {k: dict(v) for k, v in _status.items()} if not DEMO else {
        k: {"ok": d.get("updated"), "err": "", "fails": 0} for k in ("orders", "stock", "reviews")}
    d["rates"] = get_rates(sales["currency"])
    return d


STATE_ORDER = ["Paid", "Delivered", "Received", "Completed"]


# ======================= routes =======================

@app.after_request
def headers(resp):
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["X-Frame-Options"] = "DENY"
    resp.headers["Referrer-Policy"] = "same-origin"
    resp.headers["Cache-Control"] = "no-store"
    return resp


def api_guard(admin=False):
    """Returns an error response, or None if the request may go on."""
    u = current_user()
    if not u:
        return jsonify(error="login required"), 401
    if request.method not in ("GET", "HEAD") and request.headers.get("X-Requested-With") != "dashboard":
        return jsonify(error="bad request"), 400  # CSRF guard: only our own page sends this header
    if admin and u["role"] != "admin":
        return jsonify(error="admin only"), 403
    touch(u["name"])
    return None


@app.route("/")
def index():
    if not current_user():
        return redirect("/login")
    return Response(PAGE.replace("__SHOP__", SHOP_NAME.replace("<", "").replace(">", "")), mimetype="text/html")


@app.route("/login", methods=["GET", "POST"])
def login():
    error = ""
    if request.method == "POST":
        name = (request.form.get("username") or "").strip().lower()
        pw = request.form.get("password") or ""
        if is_blocked(name):
            error = "Too many attempts. Try again in a few minutes."
        else:
            u = load_users().get(name)
            ok = bool(u) and check_password_hash(u["hash"], pw)
            if not u:
                check_password_hash(generate_password_hash("x"), pw)  # same time for unknown users
            if ok:
                clear_fails(name)
                session.clear()
                session.permanent = True
                session["u"] = name
                session["d"] = secrets.token_hex(8)
                log_login(name, True, session["d"])
                return redirect("/")
            register_fail(name)
            log_login(name or "?", False)
            error = "Wrong username or password."
    return Response(LOGIN_PAGE.replace("__SHOP__", SHOP_NAME.replace("<", "").replace(">", ""))
                    .replace("__ERROR__", error), mimetype="text/html")


@app.route("/logout", methods=["POST"])
def logout():
    did, name = session.get("d"), session.get("u")
    if did:
        with _file_lock:
            data = _devs()
            if data["devices"].get(did, {}).get("user") == name:
                del data["devices"][did]
                jsave(DEVICES_FILE, data)
    session.clear()
    return jsonify(ok=True)


@app.route("/api/data")
def api_data():
    bad = api_guard()
    if bad:
        return bad
    u = current_user()
    d = build_payload()
    d["shop"] = SHOP_NAME
    d["quote"] = QUOTE
    d["user"] = {"name": u["name"], "role": u["role"]}
    d["prefs"] = prefs_of(u["name"])
    if u["role"] == "admin":
        d["profit"] = profit_brief()
    # nothing new since the last answer: send a tiny reply instead of the whole page of numbers again
    h = hashlib.md5(json.dumps({k: v for k, v in d.items() if k != "updated"}, sort_keys=True).encode()).hexdigest()[:16]
    if request.args.get("h") == h:
        return jsonify(same=True, h=h, updated=d.get("updated"))
    d["h"] = h
    return jsonify(d)


@app.route("/api/history")
def api_history():
    bad = api_guard()
    if bad:
        return bad
    kind = request.args.get("filter", "all")
    try:
        limit = max(1, min(500, int(request.args.get("limit", "100"))))
        offset = max(0, int(request.args.get("offset", "0")))
    except ValueError:
        limit, offset = 100, 0
    return jsonify(history_view(kind, limit, offset))


@app.route("/api/keys", methods=["POST"])
def api_keys_add():
    bad = api_guard(admin=True)
    if bad:
        return bad
    j = request.get_json(silent=True) or {}
    dry = bool(j.get("dry"))          # dry = only count what would happen, change nothing
    lines = [l.strip() for l in str(j.get("text", "")).splitlines()]
    lines = [l for l in lines if l and not l.startswith("#")]
    if len(lines) > 5000:
        return jsonify(error="At most 5000 keys at a time."), 400
    with _keys_lock:
        queued, used = key_sets()
        known = {k.lower() for k in queued | used}
        fresh, dup, invalid, samples = [], 0, 0, []
        for k in lines:
            if not KEY_RE.match(k):
                invalid += 1
                if len(samples) < 3:
                    samples.append(k[:40])
            elif k.lower() in known:
                dup += 1
            else:
                known.add(k.lower())
                fresh.append(k)
        if fresh and not dry:
            if DEMO:
                _demo_keys["extra"] += len(fresh)
                _demo_keys["queued"].update(fresh)
            else:
                have = KEYS_INBOX.read_text(encoding="utf-8") if KEYS_INBOX.exists() else ""
                with KEYS_INBOX.open("a", encoding="utf-8") as f:
                    if have and not have.endswith("\n"):
                        f.write("\n")
                    f.writelines(k + "\n" for k in fresh)
    if not dry:
        print(f"{current_user()['name']} uploaded {len(fresh)} keys ({dup} duplicates, {invalid} invalid).", flush=True)
    return jsonify(added=len(fresh), duplicates=dup, invalid=invalid, invalid_samples=samples, dry=dry, left=keys_info()["left"])


@app.route("/api/keys/find", methods=["POST"])
def api_keys_find():
    """Which order was this key delivered with? Only works when Eldorado shows the delivered key in the order data."""
    bad = api_guard(admin=True)
    if bad:
        return bad
    key = str((request.get_json(silent=True) or {}).get("key", "")).strip()
    if len(key) < 6 or len(key) > 120:
        return jsonify(error="Type at least 6 characters of the key."), 400
    queued, used = key_sets()
    low = key.lower()
    net_of = fx()[1]
    with _odb_lock:
        db = odb()
        hits = sorted((r for r in db.values() if low in r.get("blob", "")), key=lambda r: r["time"], reverse=True)
        found = [pub(r, net_of) for r in hits[:5]]
        tracked = len(db)
        total = len(hits)
    return jsonify(queued=any(low == k.lower() for k in queued), uploaded=any(low == k.lower() for k in used),
                   orders=found, matches=total, tracked=tracked)


# ---------- orders, buyers, days ----------

@app.route("/api/orders")
def api_orders():
    bad = api_guard()
    if bad:
        return bad
    q = (request.args.get("q") or "").strip().lower()[:60]
    flt = request.args.get("filter", "all")
    net_of = fx()[1]
    now = datetime.now(timezone.utc)

    def keep(r):
        if flt == "pending" and (r["state"] == "Completed" or is_stale(r, now)):
            return False
        if flt == "done" and r["state"] != "Completed":
            return False
        return not q or any(q in str(r[k]).lower() for k in ("buyer", "item", "id", "state"))

    with _odb_lock:
        rows = sorted(odb().values(), key=lambda r: r["time"], reverse=True)
        hits = [r for r in rows if keep(r)]
        out = [pub(r, net_of) for r in hits[:150]]
        total = len(rows)
    return jsonify(orders=out, matched=len(hits), total=total)


def _plain_order(oid, e, net_of):
    amt = float(e["amount"])
    net = net_of(amt)
    return {"id": oid, "time": e.get("ts") or "", "state": "", "item": e.get("item") or "", "quantity": e.get("qty") or 1,
            "price": {"amount": amt, "currency": e["currency"]}, "net": net, "fee": round(amt - net, 2),
            "buyer": e.get("buyer") or "", "log": {}, "first": ""}


@app.route("/api/buyer")
def api_buyer():
    bad = api_guard()
    if bad:
        return bad
    name = (request.args.get("name") or "").strip()
    low = name.lower()
    if not low:
        return jsonify(error="bad request"), 400
    net_of = fx()[1]
    rows = {}
    with _odb_lock:
        for r in odb().values():
            if r["buyer"].lower() == low:
                rows[r["id"]] = pub(r, net_of)
    for oid, e in ledger_now().items():
        if oid not in rows and (e.get("buyer") or "").lower() == low:
            rows[oid] = _plain_order(oid, e, net_of)
    lst = sorted(rows.values(), key=lambda r: r["time"], reverse=True)
    cur = lst[0]["price"]["currency"] if lst else "USD"
    same = [r for r in lst if r["price"]["currency"] == cur]
    return jsonify(name=name, count=len(lst), currency=cur, gross=round(sum(r["price"]["amount"] for r in same), 2),
                   net=round(sum(r["net"] for r in same), 2), orders=lst[:100])


@app.route("/api/day/<date>")
def api_day(date):
    bad = api_guard()
    if bad:
        return bad
    if not re.match(r"^\d{4}-\d{2}-\d{2}$", date):
        return jsonify(error="bad date"), 400
    fee, net_of, entry_date, _ = fx()
    out = []
    with _odb_lock:
        db = odb()
        for oid, e in ledger_now().items():
            if entry_date(e) != date:
                continue
            row = _plain_order(oid, e, net_of)
            r = db.get(oid)
            if r:
                row.update(pub(r, net_of))
            out.append(row)
    out.sort(key=lambda r: r["time"], reverse=True)
    return jsonify(date=date, orders=out)


# ---------- settings, costs, devices ----------

@app.route("/api/prefs", methods=["PUT"])
def api_prefs():
    bad = api_guard()
    if bad:
        return bad
    j = request.get_json(silent=True) or {}
    me = current_user()["name"].lower()
    with _file_lock:
        allp = jload(PREFS_FILE, {})
        p = allp.get(me) or {}
        if j.get("lang") in ("da", "en", ""):
            p["lang"] = j["lang"]
        if "accent" in j and (j["accent"] == "" or re.match(r"^#[0-9a-fA-F]{6}$", str(j["accent"]))):
            p["accent"] = j["accent"]
        if j.get("currency") in ("",) + CURRENCIES:
            p["currency"] = j["currency"]
        if j.get("sound") in SOUNDS:
            p["sound"] = j["sound"]
        if isinstance(j.get("gross"), bool):
            p["gross"] = j["gross"]
        if isinstance(j.get("tax"), (int, float)) and not isinstance(j.get("tax"), bool) and 0 <= j["tax"] <= 80:
            p["tax"] = round(float(j["tax"]), 1)
        if isinstance(j.get("emoji"), str) and len(j["emoji"]) <= 8 and not re.search(r"[<>&\"'`]", j["emoji"]):
            p["emoji"] = j["emoji"].strip()
        if "color" in j and (j["color"] == "" or re.match(r"^#[0-9a-fA-F]{6}$", str(j["color"]))):
            p["color"] = j["color"]
        if j.get("bg") in BACKGROUNDS:
            p["bg"] = j["bg"]
        if isinstance(j.get("hide"), list):
            p["hide"] = [x for x in j["hide"] if x in OVERVIEW_TILES]
        if isinstance(j.get("notify"), dict):
            n = p.get("notify") or {}
            for k in NOTIFY_KINDS:
                if isinstance(j["notify"].get(k), bool):
                    n[k] = j["notify"][k]
            p["notify"] = n
        allp[me] = p
        jsave(PREFS_FILE, allp)
    return jsonify(ok=True, prefs=prefs_of(me))


def _costs_view():
    p = profit_calc()
    rates = get_rates(p["currency"])
    items, kc = load_costs()
    for i in items:
        i["main"] = round(to_main(i["amount"], i["currency"], rates), 2)
    items.sort(key=lambda i: i.get("date") or "", reverse=True)
    return {"items": items, "key_cost": kc, "profit": p, "rates": rates}


@app.route("/api/costs", methods=["GET", "POST"])
def api_costs():
    bad = api_guard(admin=True)
    if bad:
        return bad
    if request.method == "POST":
        j = request.get_json(silent=True) or {}
        name = str(j.get("name", "")).strip()[:60]
        try:
            amount = round(float(j.get("amount")), 2)
        except (TypeError, ValueError):
            amount = 0
        date = str(j.get("date") or _today_for_costs())
        try:
            datetime.strptime(date, "%Y-%m-%d")
        except ValueError:
            return jsonify(error="Date must look like 2026-10-26."), 400
        if not name:
            return jsonify(error="Write what the cost is for."), 400
        if not 0 < amount <= 10_000_000:
            return jsonify(error="The amount must be above 0."), 400
        if j.get("currency") not in CURRENCIES or j.get("kind") not in ("once", "monthly"):
            return jsonify(error="bad request"), 400
        with _file_lock:
            items, kc = load_costs()
            if len(items) >= 300:
                return jsonify(error="Too many costs. Delete some old ones."), 400
            items.append({"id": secrets.token_hex(4), "name": name, "amount": amount, "currency": j["currency"],
                          "kind": j["kind"], "date": date})
            save_costs(items, kc)
    return jsonify(_costs_view())


def _today_for_costs():
    return fx()[3]()


@app.route("/api/costs/<cid>", methods=["DELETE"])
def api_cost_delete(cid):
    bad = api_guard(admin=True)
    if bad:
        return bad
    with _file_lock:
        items, kc = load_costs()
        save_costs([i for i in items if i.get("id") != cid], kc)
    return jsonify(_costs_view())


@app.route("/api/keycost", methods=["PUT"])
def api_keycost():
    bad = api_guard(admin=True)
    if bad:
        return bad
    j = request.get_json(silent=True) or {}
    try:
        amount = round(float(j.get("amount") or 0), 4)
    except (TypeError, ValueError):
        return jsonify(error="bad request"), 400
    if not 0 <= amount <= 100000 or j.get("currency") not in CURRENCIES:
        return jsonify(error="bad request"), 400
    with _file_lock:
        items, _ = load_costs()
        save_costs(items, {"amount": amount, "currency": j["currency"]})
    return jsonify(_costs_view())


@app.route("/api/devices")
def api_devices():
    bad = api_guard()
    if bad:
        return bad
    u = current_user()
    admin = u["role"] == "admin"
    with _file_lock:
        data = _devs()
    mine = session.get("d")
    devs = [{"id": k, "user": v.get("user"), "label": device_label(v.get("ua")), "ip": v.get("ip"),
             "created": v.get("created"), "seen": v.get("seen"), "current": k == mine}
            for k, v in data["devices"].items() if admin or v.get("user") == u["name"].lower() or v.get("user") == u["name"]]
    devs.sort(key=lambda d: d["seen"] or "", reverse=True)
    return jsonify(devices=devs, log=data["log"][::-1][:40] if admin else [])


@app.route("/api/devices/<did>", methods=["DELETE"])
def api_device_delete(did):
    bad = api_guard()
    if bad:
        return bad
    u = current_user()
    with _file_lock:
        data = _devs()
        d = data["devices"].get(did)
        if not d:
            return jsonify(error="No such device."), 404
        if u["role"] != "admin" and d.get("user") != u["name"].lower():
            return jsonify(error="admin only"), 403
        del data["devices"][did]
        jsave(DEVICES_FILE, data)
    return jsonify(ok=True, me=did == session.get("d"))


# ---------- push notifications (work even when the app is closed) ----------
# Needs:  py -m pip install pywebpush      and the site on https.   Optional in .env:  PUSH_CONTACT=mailto:you@yourmail.com

PUSH_FILE = Path("push_subs.json")
VAPID_FILE = Path(__file__).resolve().parent / "vapid_private.pem"
PUSH_CONTACT = os.getenv("PUSH_CONTACT", "mailto:admin@example.com")
PUSH_HOSTS = ("fcm.googleapis.com", ".googleapis.com", ".push.services.mozilla.com", ".notify.windows.com",
              ".push.apple.com", "web.push.apple.com")   # only real browser push services are ever called
_push_lock = threading.Lock()


def push_available():
    try:
        import pywebpush  # noqa: F401
        return True
    except Exception:
        return False


def vapid_public_key():
    """The public half of the key that signs our pushes, in the form browsers want. Made on first use."""
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    if not VAPID_FILE.exists():
        k = ec.generate_private_key(ec.SECP256R1())
        VAPID_FILE.write_bytes(k.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                               serialization.NoEncryption()))
    k = serialization.load_pem_private_key(VAPID_FILE.read_bytes(), None)
    raw = k.public_key().public_bytes(serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint)
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


def load_subs():
    try:
        j = json.loads(PUSH_FILE.read_text(encoding="utf-8"))
        return j if isinstance(j, list) else []
    except (OSError, ValueError):
        return []


def save_subs(subs):
    tmp = PUSH_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(subs), encoding="utf-8")
    tmp.replace(PUSH_FILE)


def endpoint_ok(url):
    m = re.match(r"^https://([A-Za-z0-9.-]+)(:\d+)?/", url or "")
    if not m or len(url) > 1000:
        return False
    host = m.group(1).lower()
    return any(host == h.lstrip(".") or host.endswith(h if h.startswith(".") else "." + h) for h in PUSH_HOSTS)


def _pick(v, lang):
    return (v.get(lang) or v.get("da") or "") if isinstance(v, dict) else v


def notify_event(kind, texts, url):
    """Push about something that happened in the shop. texts = {"da": (title, body), "en": (title, body)}"""
    threading.Thread(target=send_push, args=({k: v[0] for k, v in texts.items()}, {k: v[1] for k, v in texts.items()}),
                     kwargs={"kind": kind, "url": url, "skip_present": True}, daemon=True).start()


def send_push(title, body, skip_user=None, skip_present=True, webpush_fn=None, kind="warroom", url="/#warroom", only_user=None):
    """Sends a notification to every subscribed admin device that wants this kind. Dead subscriptions are removed.
    title/body can be a text or {"da": ..., "en": ...} (each person gets the language they chose)."""
    if DEMO:
        return
    try:
        if webpush_fn is None:
            from pywebpush import WebPushException, webpush as webpush_fn
        else:
            from pywebpush import WebPushException
    except Exception:
        return
    now = time.time()
    dead = []
    with _push_lock:
        subs = load_subs()
    admins = {u["name"] for u in load_users().values() if u["role"] == "admin"}
    for s in subs:
        skip = skip_user if isinstance(skip_user, (set, frozenset, list, tuple)) else {skip_user}
        if s["user"] in skip or s["user"] not in admins or (only_user and s["user"] != only_user):
            continue
        if skip_present and now - _presence.get(s["user"], 0) < 20:
            continue  # that person has the page open, the page tells them itself
        pr = prefs_of(s["user"])
        if not pr["notify"].get(kind, True):
            continue
        lang = pr["lang"] or "da"
        payload = json.dumps({"title": str(_pick(title, lang)), "body": str(_pick(body, lang))[:140], "url": url, "tag": kind})
        try:
            webpush_fn(subscription_info=s["sub"], data=payload, vapid_private_key=str(VAPID_FILE),
                       vapid_claims={"sub": PUSH_CONTACT}, ttl=3600, timeout=10)
        except WebPushException as e:
            code = getattr(getattr(e, "response", None), "status_code", None)
            if code in (404, 410):
                dead.append(s["sub"]["endpoint"])
            else:
                print("Push error:", code or type(e).__name__, flush=True)
        except Exception as e:
            print("Push error:", type(e).__name__, flush=True)
    if dead:
        with _push_lock:
            save_subs([s for s in load_subs() if s["sub"]["endpoint"] not in dead])


@app.route("/api/push/key")
def api_push_key():
    bad = api_guard(admin=True)
    if bad:
        return bad
    if not push_available():
        return jsonify(enabled=False, reason="Run:  py -m pip install pywebpush   and restart the dashboard.")
    try:
        return jsonify(enabled=True, key=vapid_public_key())
    except Exception as e:
        return jsonify(enabled=False, reason=type(e).__name__)


@app.route("/api/push/subscribe", methods=["POST"])
def api_push_subscribe():
    bad = api_guard(admin=True)
    if bad:
        return bad
    sub = (request.get_json(silent=True) or {}).get("subscription") or {}
    keys = sub.get("keys") or {}
    if not endpoint_ok(sub.get("endpoint")) or not isinstance(keys.get("p256dh"), str) or not isinstance(keys.get("auth"), str):
        return jsonify(error="Not a valid push subscription."), 400
    me = current_user()["name"]
    clean = {"endpoint": sub["endpoint"], "keys": {"p256dh": keys["p256dh"][:200], "auth": keys["auth"][:100]}}
    with _push_lock:
        subs = [s for s in load_subs() if s["sub"]["endpoint"] != clean["endpoint"]]
        mine = [s for s in subs if s["user"] == me][-9:]
        subs = [s for s in subs if s["user"] != me] + mine
        subs.append({"user": me, "sub": clean, "created": datetime.now(timezone.utc).isoformat()})
        save_subs(subs)
    return jsonify(ok=True)


@app.route("/api/push/unsubscribe", methods=["POST"])
def api_push_unsubscribe():
    bad = api_guard(admin=True)
    if bad:
        return bad
    ep = str((request.get_json(silent=True) or {}).get("endpoint", ""))
    me = current_user()["name"]
    with _push_lock:
        save_subs([s for s in load_subs() if not (s["sub"]["endpoint"] == ep and s["user"] == me)])
    return jsonify(ok=True)


# ---------- War-Room (admin chat) ----------

WARROOM_FILE = Path("warroom.json")
WARROOM_KEEP, WARROOM_MAX_LEN = 500, 1000
_wr_lock = threading.Lock()
_wr = {"loaded": False, "msgs": [], "next": 1, "rev": 0}
_last_post = {}


def _wr_load():
    if _wr["loaded"]:
        return
    _wr["loaded"] = True
    if DEMO:
        now = datetime.now(timezone.utc)
        seed = [("demo", "Morning! Stock is at 100, refill ran 3 times last night."),
                ("anna", "Nice. Netflix key batch #4 is uploaded, 120 keys."),
                ("demo", "Perfect, I'll check the reviews page."),
                ("anna", "One bad review about the link expiring, can someone reply?")]
        for i, (u, t) in enumerate(seed):
            _wr["msgs"].append({"id": i + 1, "user": u, "text": t, "time": (now - timedelta(minutes=40 - i * 9)).isoformat()})
        _wr["next"] = len(seed) + 1
        return
    try:
        msgs = json.loads(WARROOM_FILE.read_text(encoding="utf-8"))
        if isinstance(msgs, list):
            _wr["msgs"] = msgs[-WARROOM_KEEP:]
            _wr["next"] = max((m["id"] for m in _wr["msgs"]), default=0) + 1
    except (OSError, ValueError, KeyError):
        pass


def _wr_save():
    if DEMO:
        return
    tmp = WARROOM_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(_wr["msgs"], ensure_ascii=False), encoding="utf-8")
    tmp.replace(WARROOM_FILE)


@app.route("/api/warroom", methods=["GET", "POST"])
def api_warroom():
    bad = api_guard(admin=True)
    if bad:
        return bad
    u = current_user()
    me = u["name"]
    now = time.time()
    with _wr_lock:
        _wr_load()
        _presence[me] = now
        if request.method == "POST":
            text = str((request.get_json(silent=True) or {}).get("text", "")).replace("\r\n", "\n").strip()
            if not text:
                return jsonify(error="Empty message."), 400
            if len(text) > WARROOM_MAX_LEN:
                return jsonify(error=f"Max {WARROOM_MAX_LEN} characters."), 400
            if now - _last_post.get(me, 0) < 0.4:
                return jsonify(error="Slow down a little."), 429
            _last_post[me] = now
            msg = {"id": _wr["next"], "user": me, "text": text, "time": datetime.now(timezone.utc).isoformat()}
            _wr["next"] += 1
            _wr["msgs"].append(msg)
            del _wr["msgs"][:-WARROOM_KEEP]
            _wr_save()
            names = [x["name"] for x in load_users().values() if x["role"] == "admin"]
            tagged = {n for n in names if n != me and re.search(r"(?<![\w@])@" + re.escape(n) + r"(?![\w-])", text, re.I)}
            msg["mentions"] = sorted(tagged)
            _wr_save()
            threading.Thread(target=send_push, args=("War-Room · " + me, text), kwargs={"skip_user": {me} | tagged}, daemon=True).start()
            for n in tagged:
                threading.Thread(target=send_push, args=({"da": f"{me} nævnte dig", "en": f"{me} mentioned you"}, text),
                                 kwargs={"only_user": n}, daemon=True).start()
            return jsonify(ok=True, id=msg["id"])
        try:
            after = int(request.args.get("after", "0"))
            rev = int(request.args.get("rev", "-1"))
        except ValueError:
            after, rev = 0, -1
        reset = rev != _wr["rev"] and after > 0   # something was edited or deleted: send the list again
        msgs = [m for m in _wr["msgs"] if m["id"] > after] if not reset else _wr["msgs"][-100:]
        if after <= 0:
            msgs = msgs[-100:]
        admins = {x["name"] for x in load_users().values() if x["role"] == "admin"}
        online = sorted((n for n, t in _presence.items() if now - t < 15 and n in admins), key=str.lower)
        seen = jload(PRESENCE_FILE, {})
        away = {n: seen[n] for n in sorted(admins, key=str.lower) if n not in online and n in seen}
        typing = sorted((n for n, t in _typing.items() if now - t < 4 and n != me), key=str.lower)
        allp = jload(PREFS_FILE, {})
        styles = {n: {"emoji": (allp.get(n.lower()) or {}).get("emoji", ""), "color": (allp.get(n.lower()) or {}).get("color", "")}
                  for n in admins}
        return jsonify(messages=msgs, online=online, away=away, typing=typing, me=me, rev=_wr["rev"],
                       reset=reset or after <= 0, styles=styles, people=sorted(admins, key=str.lower))


@app.route("/api/warroom/typing", methods=["POST"])
def api_warroom_typing():
    bad = api_guard(admin=True)
    if bad:
        return bad
    _typing[current_user()["name"]] = time.time()
    return jsonify(ok=True)


@app.route("/api/warroom/<int:mid>", methods=["PATCH", "DELETE"])
def api_warroom_one(mid):
    bad = api_guard(admin=True)
    if bad:
        return bad
    me = current_user()["name"]
    with _wr_lock:
        _wr_load()
        msg = next((m for m in _wr["msgs"] if m["id"] == mid), None)
        if not msg:
            return jsonify(error="Message not found."), 404
        if msg["user"] != me:
            return jsonify(error="You can only change your own messages."), 403
        if request.method == "DELETE":
            _wr["msgs"].remove(msg)
        else:
            text = str((request.get_json(silent=True) or {}).get("text", "")).replace("\r\n", "\n").strip()
            if not text:
                return jsonify(error="Empty message."), 400
            if len(text) > WARROOM_MAX_LEN:
                return jsonify(error=f"Max {WARROOM_MAX_LEN} characters."), 400
            if text != msg["text"]:
                msg["text"] = text
                msg["edited"] = True
        _wr["rev"] += 1
        _wr_save()
    return jsonify(ok=True)


# ---------- Mindmap (shared board of notes, admins only) ----------

MIND_FILE = Path("mindmap.json")
MIND_W, MIND_H, MIND_MAX_NOTES, MIND_MAX_LEN = 1800, 1200, 300, 1000
MIND_COLORS = ("yellow", "green", "blue", "pink", "orange", "purple")
MIND_TAGS = ("", "Important", "Idea", "Todo", "Done")
_mm_lock = threading.Lock()
_mm = {"loaded": False, "notes": [], "links": [], "next": 1, "rev": 1}


def _mm_load():
    if _mm["loaded"]:
        return
    _mm["loaded"] = True
    if DEMO:
        now = datetime.now(timezone.utc).isoformat()
        seed = [(60, 50, -1.5, "yellow", "Important", "VPS\nMove to https with Caddy + DuckDNS. Then notifications work in War-Room.", "demo"),
                (370, 70, 1.2, "green", "Idea", "Add Disney+ offer with the same auto-refill. Same keys flow, new keys file.", "anna"),
                (690, 40, -0.8, "blue", "", "Fee check\nOpen one 6.00 order on Eldorado and note what we actually receive.", "demo"),
                (120, 300, 1.0, "pink", "Todo", "Reply to the bad review about the expired link.", "anna"),
                (440, 310, -1.4, "orange", "", "Refill target\nStock must always be 100. Upload new keys when the dashboard says < 20 left.", "demo")]
        for i, (x, y, r, c, tag, text, by) in enumerate(seed, 1):
            _mm["notes"].append({"id": i, "x": x, "y": y, "r": r, "color": c, "tag": tag, "text": text, "by": by, "time": now})
        _mm["links"] = [[1, 2], [2, 3], [1, 4], [2, 5]]
        _mm["next"] = len(seed) + 1
        return
    try:
        j = json.loads(MIND_FILE.read_text(encoding="utf-8"))
        _mm["notes"] = [n for n in j.get("notes", []) if isinstance(n, dict) and "id" in n]
        _mm["links"] = [l for l in j.get("links", []) if isinstance(l, list) and len(l) == 2]
        _mm["next"] = max((n["id"] for n in _mm["notes"]), default=0) + 1
    except (OSError, ValueError, AttributeError):
        pass


def _mm_save():
    _mm["rev"] += 1
    if DEMO:
        return
    tmp = MIND_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps({"notes": _mm["notes"], "links": _mm["links"]}, ensure_ascii=False), encoding="utf-8")
    tmp.replace(MIND_FILE)


def _mm_num(v, lo, hi, default):
    try:
        v = float(v)
    except (TypeError, ValueError):
        return default
    return max(lo, min(hi, v))


def _mm_apply(note, j):
    """Copies the allowed fields from the request into a note (all checked)."""
    if "x" in j:
        note["x"] = round(_mm_num(j["x"], 0, MIND_W - 230, note.get("x", 60)))
    if "y" in j:
        note["y"] = round(_mm_num(j["y"], 0, MIND_H - 90, note.get("y", 60)))
    if "r" in j:
        note["r"] = round(_mm_num(j["r"], -3, 3, 0), 1)
    if j.get("color") in MIND_COLORS:
        note["color"] = j["color"]
    if j.get("tag") in MIND_TAGS:
        note["tag"] = j["tag"]
    if "text" in j:
        note["text"] = str(j["text"]).replace("\r\n", "\n")[:MIND_MAX_LEN]


@app.route("/api/mindmap", methods=["GET"])
def api_mind_get():
    bad = api_guard(admin=True)
    if bad:
        return bad
    with _mm_lock:
        _mm_load()
        try:
            have = int(request.args.get("rev", "-1"))
        except ValueError:
            have = -1
        if have == _mm["rev"]:
            return jsonify(same=True, rev=_mm["rev"])
        return jsonify(rev=_mm["rev"], notes=_mm["notes"], links=_mm["links"])


@app.route("/api/mindmap/notes", methods=["POST"])
def api_mind_add():
    bad = api_guard(admin=True)
    if bad:
        return bad
    j = request.get_json(silent=True) or {}
    with _mm_lock:
        _mm_load()
        if len(_mm["notes"]) >= MIND_MAX_NOTES:
            return jsonify(error=f"The board is full ({MIND_MAX_NOTES} notes). Delete some first."), 400
        note = {"id": _mm["next"], "x": 60, "y": 60, "r": 0, "color": "yellow", "tag": "", "text": "",
                "by": current_user()["name"], "time": datetime.now(timezone.utc).isoformat()}
        _mm["next"] += 1
        _mm_apply(note, j)
        _mm["notes"].append(note)
        _mm_save()
        return jsonify(note=note, rev=_mm["rev"])


@app.route("/api/mindmap/notes/<int:nid>", methods=["PATCH", "DELETE"])
def api_mind_one(nid):
    bad = api_guard(admin=True)
    if bad:
        return bad
    with _mm_lock:
        _mm_load()
        note = next((n for n in _mm["notes"] if n["id"] == nid), None)
        if not note:
            return jsonify(error="No such note."), 404
        if request.method == "DELETE":
            _mm["notes"].remove(note)
            _mm["links"] = [l for l in _mm["links"] if nid not in l]
        else:
            _mm_apply(note, request.get_json(silent=True) or {})
        _mm_save()
        return jsonify(ok=True, rev=_mm["rev"])


@app.route("/api/mindmap/links", methods=["POST", "DELETE"])
def api_mind_link():
    bad = api_guard(admin=True)
    if bad:
        return bad
    src = (request.get_json(silent=True) or {}) if request.method == "POST" else request.args
    try:
        a, b = int(src.get("a")), int(src.get("b"))
    except (TypeError, ValueError):
        return jsonify(error="bad request"), 400
    with _mm_lock:
        _mm_load()
        ids = {n["id"] for n in _mm["notes"]}
        pair = sorted([a, b])
        existing = [l for l in _mm["links"] if sorted(l) == pair]
        if request.method == "POST":
            if a == b or a not in ids or b not in ids:
                return jsonify(error="bad request"), 400
            if not existing:
                _mm["links"].append([a, b])
        else:
            for l in existing:
                _mm["links"].remove(l)
        _mm_save()
        return jsonify(ok=True, rev=_mm["rev"])


# ---------- app (PWA): manifest, icons, service worker ----------


ICONS = {
    "192": "iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAHaklEQVR42u2dXYhc1QGAz9/s/O7spCFmu43ZXYyUNIWSnwclpUJrRAUDETcvEl9aQcxDHtLm3de0KeQhQhRfIn3JlgZSKqUrgsXgkwmiVorKbtJ03Sgxuzs/d2bn3nP6sAkG7UtmzubO3PN9zPMs584353539p5z5b6PzgqAXlEcAkAgQCBAIEAgAAQCBAIEAgQCQCBAIEAgQCAABAIEAgQCBAJAIEAgQCBAIEAgAAQCBAIEAgQCQCBAIEAgQCAABAIEAgQCBAJAIEAgQCBAIAgak/Lfd87zG0o5NMfe19hTHXLKAkmjPX8o1gorxDBY5GvsLrGhCuRcvNryao8z5YIwSiR20Kcif2PXpXyKgzVpHT5pdFyP/n38bLzakkb3P59LpZKoM/qzh3a8csQmbpDV8TN2KV2cmGrpx398yYwWXZykolH6M5AvgdYd+uadK4s7Jrb95qnuckNqNeAzUP8CbUhHDlcDrb98HQVTqyyem6vs3D72yM643hpkh/odu5QbEZHDdhnvnOeXFFKr+VOzazduqXxO2IE+l/l5BS2Qd6xT+dzajVvzp2alVkIKQKB7vqw1o6XlS58snnvbVMvpXuUi0NA6VC0vnptbvvSJGS3hEAL10JjDE0MIRAwhUEZPZMQQAhFDCEQMIRAxBIEKRAwhEDGEQMQQAhFDELRAxBACEUMIRAwhUFZiaOHUn4khBOo9hm5d+njxzbfNWOX2zcWAQPfgkHVmtPTln95ZvfwZMYRAPRjkpFIuSeZPnu8uN9SISf3+YgQauknI6mIhWli6evqCGskJ/EGge4+hJDdWvjn3wdLsu2as7BJiCIF6iqHrr7+1euVzUyGGEKjHGLLEEAIRQwhEDCFQCvjYmIIYClQgZ51biz04RAwFJ5Bc/6dEsTD5gO2sSaX6dpEYCmsGksJalc9N/3YmV6tYH/MQMRTYKUyppNUpTI9PHnvWrnW9/GudGAqrgaRW8UrzBwf2jB/+RbzSlLrvPZeIodCuwqSSSb217cWnq7sfjhseNiYjhoK7jHfWCaWmTxBDCNTrJGSjTnGKGEKgPmKou9LcfGDP+MxjxBAC9TgPxcQQAvUXQ1ZqYgiBep+EVBK1i1Pjk8cObUgMlYvEUJYFEkJIrbsrjc1P7N166OfxcsPDbtx3Ymjh9+fjVlvlNDGUZYFuz0P16Ee/frLyk6m4EXmKoXw0v/SfV/+qSgXHcsRsCySktEliyoWpE4d1MW99PItkfVn01xff//ri+7kaq8myLZAQUqm4EVV2bt9+9KBttqXycc+Qc6pcuHbmYuPTa6ZCDGX9jkRpdHe5seXgo1sOPtr1FEPK6CTqLJw8n0QdZUKPoezf0iqVtM329qMHKzsn/cRQYk2l2Pj06rUzF1U59BgKYZdWaeNEF/M+YyhOcrUKMSQCuale6g2IIUsMBSMQMYRAxBACEUMIRAwRQ0ELRAwhEDGEQMQQAhFDxFDQAhFDCEQMIRAxhEBZiyG5ATFkLQKFEkPxarP/E9ndMRQ320pnOYYQ6E4MtdoPvvxMcXo8iToe9hlaj6F/Lfz3jb/r0SxPQgh0J4a6iSkVpn53WGrlrPUSQ6ZWuXHhvZv/+CA3VsnqajIEuiuGmlF1945tLz4d11tefhkSTqiR3NXTF6KFJV0sZHIeQqC7HdLxSnN85rHNB/Z2PS2tVyOmu9yYPznrEiuVyl4MIdB3JBJ2rTt57FBxajyJ2p5iqLR65bPrr79lRkvZ+2UIgb4XQ2txrlaZPuEvhpLEjJWXZt+9OXc5N5a1B7Ui0P+LoUZrY2LoL9HCkirmszQPIdD9jiFhrVQyMzGEQCnEkM5QDCHQfY+h8//8Zu6yyUoMIVA6MdSeX9KlvBj+X4YQKKUY+sOs7XSFUmLIN81DoPseQ9aq/Ej76ldxPZJaDfumiwiUQgwJ5+SI8XNORKBQY4irMGIIECjFGEIgYkhyVBAo7RhCIGIIgYAYQqB0YkgHHkMI1GsM1VvVPQ//8PlfBh5DCNSrQ0bHK42JI49v2v/TuO7huVIIFB5OuMROHX9uZOsm2+mKIOchBOrn4Enb6Y5s3TR9fMYlNsxn0SGQhxiq7d818cIBP8uiEShEh1abEy88Xtu/K8AYQiBvMTR9fCbAGEIgYgiBiCEEIoYQCEKMIQQihhCIGEIgYgiBIMQYQiBiCIGIIQQihhAIQoyhtAWS0s9riGLI15AHY+wm5e9nnNx+HElva8Wl/PYdhiGGrr/2N1Mt+9kwejDGbtKdfky1JISQPT9aS0oXJ6ZaGvB1EVKreLU1ceRXrc8X6x9+YYolDw4Nxtjlvo/Opjf/uKTV8fJOupQf9LU1zgmtRGxjTw9IHJCxD8QM5OHTGfz9BqUUiRNa5mplz2amOvb0G8jbxzMEl/VCOOG/WlIdu0n/exka2RoyvwMBAgECAQIBAgEgECAQIBAgEAACAQIBAgECASAQIBAgECAQAAIBAgECAQIBAgEgECAQIBAgEAACAQIBAgECASAQIBAgECAQAAIBAgECAQJB2PwPzKk6ID74zUIAAAAASUVORK5CYII=",
    "512": "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAIAAAB7GkOtAAATxUlEQVR42u3d348d5WHH4Xln5uzu2T37w7gExyH2WglVgVwUkxuHqqgRriqqGJHWVqUo3FRcNE6FKhSrf4MjVKHGkSLUG6Lc2G0QjoKqGqWiKiAlwkRKCFKg8toBx8Q13h9n9+zumZm3Fwsp2bVxWhHJO+/ziD8An52Zz3nPd482fPYn38oASE/uJQAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAEAAABAEAAABAAAAQAAAEAQAAAEAAABAAAAQBAAAAQAAAEAAABAEAAAPjdKb0EH7EYYxNb+S8LechC8BPe3pdn02TRFYgA/G6e/vnYSD7ayWLMsjZdqTELoV5Zi+tVlrsDt/GPsex1Q1lsw+szZiE0a8NmdV0DBODmffovnn1z8ewbxdhIq84BIWvWhrf8yR+Of2p3PVgNuU8Ot2fEO8Xl53649vZ/551OjNvp+gx5qFfXp/bfMbX/0xogADfn4TrmoyOLr7xx8cSzYcdkrOv2PP/zPA7WFn/08z948m/yoohN4w7cjm9QQqe4/P0fLr30WuiNx2Y7XZ+hKOLVpezoQzMH7qpX1kLh8hOAm/UQEHb0OjMTsW7a9C8LOyb7r5+/cOL0vr//q2ph2R24TQ8BZa+b7+iVE93YbKfrMxT5MIv52EgWox+jANzUDYh1s/Ffq/5ZddOZ6V0+/XLvrr0fe+hzw6tLoSz8tLfhOfW9i3N7BWDjCvT0/8j5MJff/tkR84mxCydO91+/UPa6LSscCAB82OEmL4t6sDZ3/GQ9WMvf+2USQABIIQF1U/a6G2NAPjHW1m88gADAtRpQ1RtjwOXTL3dmerGqvSYgACTTAGMACACpFsAYAAJAsgkwBoAAkG4DjAEgAKTbAGMACACpFsAYAAJAsgkwBoAAkG4DjAEgAKTbAGMACACpFsAYAAJAsgkwBoAAkG4DjAEgAKTbgE1jQGMMAAEglQL87xhQLa/mhTEABIB0ErAxBvxs7u1/+tdi0iEABICkGlDV5UzvnWf+88q/vdKZ7sXaGAACQEIRyPKRzvknnxnMXSq6Y84BIACkE4CYj5TD+f6546di3YQ8NwaAAJBMAuqm7I0vvvrGW089V06O+2YACABJNaAupycunXrhypmznekJYwAIAElFYGMM+K4xAASA1AJgDAABINkEGANAAEi4AcYAEADSjYAxAASARANgDAABINkEGANAAEi4AcYAEADSjYAxAASARANgDAABINkEGANAAEi4AcYAEADSjYAxAASARANgDAABINkEGANAAEi4AcYAEADSjcB7Y8DKuUtFd9QYAAJAOgGI+Uhn+O7ShW88m4UQQvCSgACQTALqupyamH/ptYtPP19OTcTaIQAEgMQacPHpM/MvvlZOjmsACAApCVko8nNPnFp/52o+2sn8UhAIAKloYj7aWX/n6rknToUiz2wBIACkI9ZNOTk+/6IxAASANBtgDAABIFHGABAAEmUMAAEgWcYAEADSboAxAASARBkDQABIlDEABIBkGQNAAEi7AcYAEAASZQwAASBRxgAQAJJlDAABIO0GGANAAEiUMQAEgES9PwbMPfHPxgAQANKyMQZcffGnF7/9fDndi1XtNQEBIJkGNLGcHP/ld36wePYNYwAIAEkVIIY8j3V97vjJ4Xw/HymzaAwAASCVQ0BTdMcGc5fOP/lMPtLJPP9BAEioAXXdmZ64cuaVS6deKKcnYm0MAAEgoXNALCfH33rqucVX3yx7xgAQABIqwMYY0BgDQABI8BBgDAABINkGGANAAEj4HGAMAAEg0QIYA0AASPcQYAwAASDZBhgDQABI+BxgDAABINECGANAAEj3EGAMAAEg2QYYA0AA+D8IIQvt+QtbxgAQAH7bp38cVrGq29MAYwAIAL/l0390987OLZNxvWpNA4wBIADc8PkfmtX18U99fO9jDzfrwzb9pXVjAAgAN1Lkw4XlnQf37zryx9XiSiiK9jTgg2PARNcYAALAlnNAnldLg088+ueTn5mt+iuhaMvl8f4YMPf1k9XKat4pjAEgAGwqQMiaJhT53r/7i2JirGnRIBybpuiODs5d+sU3v5ePj8VGAEAA2HxF5M3Kau+uvXu+cqhZXg15i34rtG7KqYnLp1++fPrlzkwvVsYABAA2HQOKYjjfv/XQgVsPHRjO90PZojEgxnxi7MKJ0/3XL5Q9YwACAFsbkIdmeXXP0UO9O/dW/UGbxoC8LOrB2tzxk/VgLS+NAQgAbC5AaKq66I7OHjtSdEdbNQbUTdnr9l8/f+HE6XzCGIAAwNYEFHnVH/Tu3LPnaOvGgKruzPSMASAAXL8BZXvHgMYYAALAhzfAGAACQKoFMAaAAJBsAowBIACk2wBjAAgA6TbAGAACQKoFMAaAAJBsAowBIACk2wBjAAgA6TbAGAACQKoFMAaAAJBsAowBIACk2wBjAAgA6TbAGAACQKoF+M0xYNjeMUAAEADYnIAPjgGra20dA8qpCR8EIQCwpQFlMZzvf+zQgZ0P3DtcWG7fGPCLb35vcO5S0R2NjQYgALCpAXmoV9b2/O1D3dld9cpqyFs1BlQrq3NfPxXrJuS5MQABgE0FCM2w6sz09h07Eoo8Nk2rxoCJ7uKrb7z11HPl5LhvBiAAsCUBRV71V6bu+fTtjz5YLa20agyo63J64tKpF66cOduZnoi1bwYgALC5AUW1sLzr8P07D947XFgORXvGgCxm+Ujn/JPfHcxdKrpjxgAEALZGIGvWh3sfe7g7u6setGsMGCmH8/1zx40BCABcOwChWW/vGNAbNwYgAHD9BBgDQABIuAHGABAA0o2AMQAEgEQDYAwAASDZBBgDQABIuAHGABAA0o2AMQAEgEQDYAwAASDZBBgDQABIuAHGABAA0o2AMQAEgEQDYAwAASDZBBgDQABIuAHGABAA0o3Ae2PA+L5d9WCtpWNAbQxAAGBrAEKzPuzcMrnnqw9lMcYWPSVj3ZST44tnf/7L7/zAGIAAwLUSUBTV4vLM5+7e/cjBanE5FO25CGNVl9O9i99+/uqLr5WT47H2QRACANdqwO5HHpi57+5qaaVNDchCFop87olT6+9czUc7mXMAAgBb3i1nsW72PX545LYdzdowa80vBTUxH+2sv3P13BOnQpFnwU8aAYDNl15o1oYjt+3Y9/jhWDdZi94ob4wB8y++dvHp58upCR8EIQCwWSjyamll5r42jgF1U05NXHz6zLwxAAGA6zag1WPAOWMAAgDXf7dsDAABINFr0BgAAkCqjAEgAKTdAGMACACJMgaAAJDqxWgMAAEgVcYAEADSboAxAASARBkDQABI9ao0BoAAkCpjAAgAaTfAGAACQKKMASAApHp5vjcGzLZ/DKj9tBEA+A0bY8CO++7e/eUHqoV+KItWNWBjDHjpNQ1AAOBaDchDtbTy8S99fmr/77dsDAghZCFc+Mazw3eX8pFOFo0BCAD85mMyNk0oin3HDndmes16lYWWfGoem6bojq6cu3T+yWfykU7m+Y8AwJZDQF4PVruzu/Y+9sVmfdim1TTWdWd64sqZVy6deqGc9kEQAgBbG1AUw4XlnQf37zp8f7WwHIoWjQFNLCfH33rqucVX3yx7vhmAAMA1zgGhWlq5/dEHp+65o+q3aAyIMeR5rJtzx08O5/v5SGkMQABgUwE2xoC8pWPA2GDOGIAAwHUPAcYAEACSbYAxAASAhM8BxgAQABItgDEABIB0DwHGABAAkm2AMQAEgITPAcYAEAASLYAxAASAdA8BxgAQAJJtgDEABICEzwHGABAAEi2AMQAEgHQPAcYAEACSbYAxAASAhM8BHxgDlgetHQM6xgAEADYX4L0xYPZrh8vxsaaqWzUGjI8N5i5d+Mdni/HR2AgAAgCbDwF5PVjr7tv1ya98oVleDXl71oBY1Z3piSvPv/Kr0y93ZnqxMgYgALCpAUVeLS7feujArYcODOf7oWzVGJCPjV44cbr/+oWy1zUGIACwpQEhNMure44e6t25t+q3agzIO0U9WJs7frIerOVlYQxAAGBzAZqqLrqjs8eOFN3RVo0BdVP2uv3Xz184cTqfGDMGIACwJQFFXvUHvTv37Dl6qIVjwEzv8umXLxsDEAC4dgPKYjjfb+0YMDFmDEAA4PoNyNs7BpTGAAQAPqwAxgAQAJJNgDEABIB0G2AMAAEg3QYYA0AASLUAxgAQAJJNgDEABIB0G2AMAAEg3QYYA0AASLUAxgAQAJJNgDEABIB0G2AMQAC8BKTbAGMAAgCpFsAYgABAsgnYNAaE9o4BtTEAAYBNDfjAGFAtLrfng6BfjwHfPN3/2fl8fCxrjAEIAGxqQB6aldVPfuUL3X276sFayNs1Biyvnv+Hf4l1k+W5MQABgE0FCM2wLsfHZr92JBR5bJp2jQHjSz+de/up75eT3egQgADA5gQUebU8mLrn07c/+mC1tNKqbwbUdTk1funkf1w5c7YzPZH5rVAEALY0oKgWlncdvn/nwXuHC8uhaM83A7KY5SOd808+s/Jfv8zHRqIPghAA2BKBrFkf7n3s4e7srnqw2qYxIIyUw3eX1i5eCZ3SEoAAwNYAhGa96sz09h1r2xiQxRjKwtMfAYDrJ6DIq/5KK8eALEZPfwQAPrwB7R0DQADgRhFo6RgAAgA3CkB7xwAQALhBAlo8BoAAwI0aYAxAACDdCBgDEABINADGAAQAkk2AMQABgIQbYAxAACDdCBgDEABINADGAAQAkk2AMQABgIQbYAxAACDdCBgDEABINAAfHAMKYwACACkloMirpZWp/Xd8/EufNwYgAJBYA8qiWujv/vIDO+77TLW0Egq3EgIA6YhZrJvZx/9y5LYdzdowcw5AACCZuyc0a8OR23bse/xwrJvMH1tEACAdG2PAzH13737kYLW47IMgBAASa8Di8u5HHpi5725jAAIAiYlZrJt9jx82BiAAkNptZAxAACBVxgAEANJugDEAAYBEGQMQAEj1fjIGIACQKmMAAgBpN8AYgABAoowBCACkemMZAxAASJUxAAGAtBtgDEAAIFHGAAQAUr3DjAEIAKRqyxhQeE0QAEipARtjwOfu1gAEANISY8xi3PPVhzq3TDbrwywYAxAASOQQkOf1YG183669j32xWR9mnv8IACTUgKIYLizvPLh/1+H7qwUfBCEAkNY5IFRLK7c/+uDUPXdUfd8MQAAgoQKE2DShyPcdO9yZ6TXrlTEAAYB0DgF5PVjtzhoDEABIsAHGAAQAEj4HGAMQAEi0AMYABADSPQQYAxAASLYBxgAEABI+BxgDEABItADGAAQA0j0EGAMQAEi2AcYABAASPgcYAxAASLQAxgAEANI9BBgDEABItgHGAAQAEj4HGAMQAEi0AMYABADSPQT8egx42BiAAEBiDSiK4UJ/55/ee9vDf1TN90NpDEAAIKlzwNLgE3/9Z727Zqv+wBiAAEA6BQhNXZcTY7PHjhTd0aaqjQEIACR0CKj6g96de/YcPdQsr4ZcABAASKcBZTGc79966MCthw4MjQEIACR2DgjN8uqeo4d6d+41BiAAkFQBQlPVRXfUGIAAQHoJKIwBCAAk2wBjAAIA6TbAGIAAQKoFMAYgAJBsAowBCACk2wBjAAIA6TbAGIAAQKoFMAYgAJBsAowBCACk2wBjAAIA6TbAGIAAQKoFMAYgAJBsAowB/H+VXoKP/B1ZKPJtdxIPeR6KPOTeEGzPi+79MaD/s/O/evalkZ3Tsa5bFrlQ5A43AnDTn8dX1+PV/jAL2+sODHkR+ytVf5C5xbbppff+GLDy87f7P34zdEdj07QoAEW82m9W1zVAAG7iO3BtfereO7KvPlSMjcQmbq9zSzMcjn7i9+LQh8jb9s1HXRfdsdljR9799x/no50sturmqlfXp/bf0ayt+4zro3xhP/uTb3kVPjIx5mMj+WgnizHbZu+lYxZCrOp6ec0hYBtrYhgpi/HRbXgF3vj6bNaGDgFOADf3u7DV9Xplbdv+/2dmgO0tD3FYDa8O23rI9vQXgJu9AaFwjeIKZDu8YfASAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAIAgAAAIAAACAAAAgCAAAAgAAAIAAACAIAAACAAAAgAAAIAgAAAIAAA/O78D86+5c6p/8PLAAAAAElFTkSuQmCC",
    "180": "iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAHmklEQVR42u2dy2sd1x2Az++cmfuWdGXhWjWpHjSGJt40SjZOFkmh3gQq04CMV9ll0TrgRVrTv8FtFoa6ELLzKkTgYhWycaEJNMmiRAmENBAbZKmpI9fYet3XvM7pQqpjpQpYdyTdq5nvQ1tdMXM/nfPN3DnnynOfv6UAdkJzCgA5ADkAOQA5ADkAOQA5ADkAOQA5AJADkAOQA5ADkAOQA5ADkAOQA5ADADkAOQA5ADkAOQA5ADkAOQA5ADkAkAOQA5ADkAOQA3qK15s/65yzbq9eTLQokb49xS6xh/QAvZ6YoUsFXfSVc0qlPGanRJJW4MJY6b70Q8QbqoqIUt0drFMiNohsJzx4P7yemLE+f2t9/qYpFdKOH6JsEB352U8rPz6etDui+2uWFC02iL659ncbREqLct28QtIJB6dODE49efB+HLQczjpdLKx/cvPOlesyPOCSJN3Z164drP/jq59c/pU2xlnbR/OLc0q0DaI7V2/Ea03lecrten4RY9zKhjp/pn7q6aQViMm0HA8HDxmu+fXqHszHwwONLxeXrsxN/u5cvNY84NP3mNOKEhHPKOd2L4eOlNOlQhe/e5iDNLGbP+lzz6/X7s19XHt6/Adnno9WNsQz/RakLrFKpLs32CW2J2Zk5FLWWaerpaUrc40vl7xaOb1wkKH7HM5pzyTt4Pald5N2oLsawCGjcijlEuvVypvxoaulPbyJghyZ8CNONuPj3tzHfr3m4oR3FzmID+QgPpCD+EAO4gM5iA/kID6Qg/hADuIDMi8H8YEcxAdy7FV8IAdyfF98eINVJhfk2CE+/vWnv7QXlk256Cx+IMf2+Ihbndu/n3WJFa2JD+TYHh/V8vqnN79++z1voMKdD+T4jh+JN1Rdnv3g/o15f6ia8tl35MieIEoX/MXL19q3l025RHwgx/b4KHjRamPhEvGBHDvGR61CfCAH8YEcxAdybCPlsljiI7NyiKT/CJ74yJwcIi6KCyMDPzz3UtIKUm67QHxkbuTQOmmHo+deGjk9Fa01xaRbOU18ZG1acS4JovELr5QnjqXdtoX4yGBzhLFXr05ePCtGp9y2hfjI2tWKGJ002gNTTz7x2svxRkvS7QlGfGTtPocYHa81R2deHDn9LPGBHP/nh1I2jMYv/LI8MUp8IMd348OGsV+vER/I8T2TS6M1+AzxgRw7+2G+jY/1pph0x/W/+Gjl+4HTTH3wZqN47Px08diRrU1hU8WHHz3YWPrjdSUifbx3NnI85qGIDaLC0frkb2ZcYlW6WnBJ4g1WVz/64s7Vv+Z2NUOmRg4xOt5o1V84efzV03HqyWXTjztXb6x++IU3UMmhH1l7nkOMjtebx1/9ef2Fk/FGK218iBKjF96cDe+u6KKvcnbxksWHfZxyiZ18Y6ZwbDhtfFini354d2XhzVkxWgkjRzbi49jw5Bt7Eh/WG6isfpjH+MjmY4J7HR82n/GR2WdIiQ/kID6Qg/hADuIDOYgP5CA+kIP4QA7iI3fxkaO1ssQHchAfyEF8IMf+x4dJ60d24yOP+3N8Gx/Pn0zvx1Z8/GE2vLeasfjI684+zinnxl4/4x8ZsGGUaqsP63TRD+4+WLoyp32PkePwDx5aJ+2gMjk6fuEVG0Ypc9Il1h+s3r/xyfLsB16GVjPkd9snMSZaa46cnhqdeTFOvZTSWecNVL5++731T295tYzER473BFNKtMQbrSdee3nwmRNxI92dD+dEa5fYhUvvRqsNXfAysJQy13IoEWetGD15ccav12wYp1pKaa0pl9q3lxcv/1kXfMfIkYn46JQn9io+En/o0fiwyEF87BAfG/O3zCH/4jDk2Mf4iFebcpjjAzn2Lz7uLl6+Zoq+OrRLbZFjX+Njfvmd9025oA7nOn3k2L/4sKZS/Oad98P7G+IfyskFOfYtPjZf8DB/WSly7GN8bPYpVyvERwZBjn2PD+QgPpCD+EAOID6Qg/hAjr2Kj2Y7V/GBHI8bHxO/nfEqJRsn+YkP5HjM+AjKk6M/+vUvbLOTcvts5MhefOh4vXl0+tTR6VPRakM8gxzw6PQittkZOz9de2o8buQiPpBjF3bYODHl4sTFs6ZczEN8IMcuJ5dGu/bU2Nj56TzEB3Ls0g/PRKuNnMQHcnRx8ZKX+EAO4gM5iA/kID6Qg/hADuIDOYgP5CA+kIP4yEp8IAfxgRzEx+7xevWvJkZ3OfyKKOf6cOh+GB+Nfy7+5/pHhZGh9DvHbZ2lHo1DXk/MsJ3QrTQiJd2cPtEqjpVzfbjS8GF8tL76d+OzW1IuunTr68UYt9KwnbAnfng9OH1BOPjsCfX6GVMquC62dJWtrT910VfO9dfsLmKTxJRLExfPPvjbZ7rop9xBW7QknXBw6oQNwoOfquS5z9866DPonC4Vtt7ablaDOKXEOZc0O326TNk6KXimUuz2ALcfrIgNop4MHj2bVpJWkH4+7tfKFxfF0Uq0h8NtLqaVR4I0049RZeIAuZQF5ADkAOQA5ADkAOQA5ADkAOQA5ABADkAOQA5ADkAOQA5ADkAOQA5ADgDkAOQA5ADkAOQA5ADkAOQA5ADkAEAOQA5ADkAOQA7oLf8FVa20r3AG300AAAAASUVORK5CYII=",
}

SERVICE_WORKER = r"""
// Keeps the dashboard installable and shows notifications. Private data is never cached.
self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", e => e.waitUntil(self.clients.claim()));
self.addEventListener("fetch", e => {
  if (e.request.mode === "navigate") {
    e.respondWith(fetch(e.request).catch(() => new Response(
      '<!doctype html><meta name="viewport" content="width=device-width,initial-scale=1"><body style="font:16px system-ui;background:#0e1014;color:#e9ebf1;display:grid;place-items:center;min-height:100vh;margin:0;text-align:center"><div><h2>You are offline</h2><p>Reconnect and open the app again.</p></div>',
      {headers: {"Content-Type": "text/html; charset=utf-8"}})));
  }
});
self.addEventListener("push", e => {
  let d = {};
  try { d = e.data.json(); } catch (_) { d = {title: "War-Room", body: e.data ? e.data.text() : ""}; }
  e.waitUntil(self.registration.showNotification(d.title || "War-Room", {
    body: d.body || "", tag: d.tag || "warroom", renotify: true, icon: "/icon-192.png", badge: "/icon-192.png",
    data: {url: d.url || "/#warroom"}}));
});
self.addEventListener("notificationclick", e => {
  e.notification.close();
  const url = (e.notification.data && e.notification.data.url) || "/#warroom";
  e.waitUntil(self.clients.matchAll({type: "window", includeUncontrolled: true}).then(list => {
    for (const c of list) { if ("focus" in c) { if (c.navigate) c.navigate(url); return c.focus(); } }
    return self.clients.openWindow(url);
  }));
});
"""


def _png(key):
    return Response(base64.b64decode(ICONS[key]), mimetype="image/png",
                    headers={"Cache-Control": "public, max-age=86400"})


@app.route("/icon-192.png")
def icon192():
    return _png("192")


@app.route("/icon-512.png")
def icon512():
    return _png("512")


@app.route("/apple-touch-icon.png")
def icon_apple():
    return _png("180")


WIDGET_PAGE = r"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#0e1014">
<link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="icon" href="/icon-192.png" type="image/png">
<meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black"><meta name="apple-mobile-web-app-title" content="Today">
<title>Today</title>
<style>
:root{--bg:#0e1014;--card:#171a21;--text:#eef0f4;--muted:#8b93a3;--good:#3ad49a;--warn:#f2b84b;--bad:#f06a6a}
@media (prefers-color-scheme:light){:root{--bg:#f4f5f8;--card:#fff;--text:#14171c;--muted:#667085;--good:#0f9f6e;--warn:#b7791f;--bad:#d64545}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:16px/1.4 system-ui,-apple-system,Segoe UI,sans-serif;min-height:100vh;display:flex;align-items:center;justify-content:center;padding:max(16px,env(safe-area-inset-top)) 16px max(16px,env(safe-area-inset-bottom))}
.w{width:100%;max-width:420px;background:var(--card);border-radius:22px;padding:24px;text-align:center}
.s{color:var(--muted);font-size:13px;letter-spacing:.04em;text-transform:uppercase}
.big{font-size:54px;font-weight:700;margin:6px 0 2px;font-variant-numeric:tabular-nums}.big small{font-size:20px;color:var(--muted);font-weight:500}
.row{display:flex;justify-content:space-around;margin-top:18px;gap:8px}.row div{flex:1}.row b{display:block;font-size:22px}
.ago.warn{color:var(--warn)}.ago.bad{color:var(--bad)}.err{color:var(--bad);margin-top:12px;font-size:13px}.foot{margin-top:16px;color:var(--muted);font-size:12px}
a{color:var(--muted)}
</style></head><body><div class="w"><div class="s" id="d">&nbsp;</div><div class="big" id="n">–</div>
<div class="row"><div><b id="o">–</b><span class="s" id="lo"></span></div><div><b id="l">–</b><span class="s" id="ll"></span></div><div><b id="p">–</b><span class="s" id="lp"></span></div></div>
<div class="err" id="e"></div><div class="foot"><a href="/">Dashboard</a></div></div>
<script>
var DA=(navigator.language||"").slice(0,2)=="da",T=DA?{t:"I dag",o:"ordrer",l:"seneste",p:"venter",e:"Kunne ikke hente tal.",now:"lige nu",m:" min",h:" t",d:" d"}:{t:"Today",o:"orders",l:"last order",p:"waiting",e:"Could not load.",now:"just now",m:" min",h:" h",d:" d"};
function ago(iso){if(!iso)return["–",""];var m=Math.max(0,Math.round((Date.now()-new Date(iso))/6e4));var t=m<1?T.now:m<90?m+T.m:m<2880?Math.round(m/60)+T.h:Math.round(m/1440)+T.d;return[t,m>360?"bad":m>120?"warn":""]}
function load(){fetch("/api/data",{credentials:"same-origin"}).then(function(r){if(r.status==401){location.href="/login";throw 0}return r.json()}).then(function(d){
var s=d.sales||{},td=(s.days||{})[s.date]||{a:0,n:0},c=s.currency||"";
document.getElementById("d").textContent=T.t;
document.getElementById("n").innerHTML=Number(td.a||0).toLocaleString(DA?"da-DK":"en-GB",{minimumFractionDigits:2,maximumFractionDigits:2})+" <small>"+c+"</small>";
document.getElementById("o").textContent=td.n||0;document.getElementById("lo").textContent=T.o;
var a=ago(((d.orders||[])[0]||{}).time);var el=document.getElementById("l");el.textContent=a[0];el.className="ago "+a[1];document.getElementById("ll").textContent=T.l;
document.getElementById("p").textContent=((d.pending||{}).n)||0;document.getElementById("lp").textContent=T.p;document.getElementById("e").textContent="";
document.title=(td.n||0)+" "+T.o}).catch(function(x){if(x!==0)document.getElementById("e").textContent=T.e})}
load();setInterval(load,30000);document.addEventListener("visibilitychange",function(){if(!document.hidden)load()});
</script></body></html>"""


@app.route("/widget")
def widget():
    if not current_user():
        return redirect("/login")
    return Response(WIDGET_PAGE, mimetype="text/html")


@app.route("/manifest.webmanifest")
def manifest():
    name = SHOP_NAME.replace("<", "").replace(">", "")
    return Response(json.dumps({
        "name": f"{name} Dashboard", "short_name": name[:12] or "Dashboard",
        "start_url": "/#overview", "scope": "/", "display": "standalone",
        "shortcuts": [{"name": "Today", "short_name": "Today", "url": "/widget", "icons": [{"src": "/icon-192.png", "sizes": "192x192"}]}],
        "background_color": "#0e1014", "theme_color": "#0e1014",
        "icons": [{"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
                  {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}],
    }), mimetype="application/manifest+json")


@app.route("/sw.js")
def service_worker():
    return Response(SERVICE_WORKER, mimetype="text/javascript", headers={"Service-Worker-Allowed": "/"})


@app.route("/api/users", methods=["GET", "POST"])
def api_users():
    bad = api_guard(admin=True)
    if bad:
        return bad
    if request.method == "POST":
        j = request.get_json(silent=True) or {}
        try:
            add_user(str(j.get("username", "")).strip(), str(j.get("password", "")), str(j.get("role", "viewer")))
        except ValueError as e:
            return jsonify(error=str(e)), 400
    seen, now = jload(PRESENCE_FILE, {}), time.time()
    return jsonify([{"name": u["name"], "role": u["role"], "last_seen": seen.get(u["name"]),
                     "online": now - _presence.get(u["name"], 0) < 20} for u in load_users().values()])


@app.route("/api/users/<name>", methods=["DELETE", "POST"])
def api_user_one(name):
    bad = api_guard(admin=True)
    if bad:
        return bad
    with _users_lock:
        users = load_users()
        u = users.get(name.lower())
        if not u:
            return jsonify(error="no such user"), 404
        if request.method == "DELETE":
            if u["role"] == "admin" and sum(1 for x in users.values() if x["role"] == "admin") == 1:
                return jsonify(error="You cannot delete the last admin."), 400
            del users[name.lower()]
            drop_devices(name.lower())
        else:
            pw = str((request.get_json(silent=True) or {}).get("password", ""))
            if len(pw) < 8:
                return jsonify(error="Password must be at least 8 characters."), 400
            u["hash"] = generate_password_hash(pw)
            same = name.lower() == session.get("u")
            drop_devices(name.lower(), keep=session.get("d") if same else None)   # a new password signs the other devices out
        save_users(users)
    return jsonify(ok=True)


# ======================= pages =======================

LOGIN_PAGE = r"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#0e1014"><link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="icon" href="/icon-192.png" type="image/png"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black"><meta name="apple-mobile-web-app-title" content="__SHOP__"><title>Sign in</title>
<script>try{var t=localStorage.getItem("theme");if(t==="light"||t==="dark")document.documentElement.dataset.theme=t;}catch(e){}</script>
<style>
:root{color-scheme:dark;--bg:#0e1014;--panel:#161920;--panel2:#1b1f27;--line:#252a35;--ink:#e9ebf1;--muted:#7d8496;--accent:#34d399;--red:#f87171}
:root[data-theme=light]{color-scheme:light;--bg:#f4f5f8;--panel:#fff;--panel2:#f8f9fb;--line:#e4e7ee;--ink:#12151c;--muted:#667085;--accent:#0b8f63;--red:#d92d20}
*{box-sizing:border-box}body{margin:0;min-height:100vh;display:grid;place-items:center;background:var(--bg);color:var(--ink);font:15px/1.5 Inter,system-ui,"Segoe UI",Arial,sans-serif;padding:16px}
form{width:100%;max-width:380px;background:var(--panel);border:1px solid var(--line);border-radius:18px;padding:32px 28px}
.logo{width:40px;height:40px;border-radius:12px;background:var(--accent);color:#04251a;display:grid;place-items:center;font-weight:800;font-size:18px;margin-bottom:18px}
h1{font-size:22px;margin:0 0 4px;letter-spacing:-.3px}p{margin:0 0 22px;color:var(--muted);font-size:14px}
label{display:block;font-size:13px;color:var(--muted);margin:14px 0 6px}
input{width:100%;padding:12px 14px;border-radius:10px;border:1px solid var(--line);background:var(--panel2);color:var(--ink);font:inherit;font-size:16px}
input:focus{outline:2px solid var(--accent);outline-offset:1px}
button{margin-top:24px;width:100%;padding:13px;border:0;border-radius:10px;background:var(--accent);color:#04251a;font:inherit;font-weight:700;cursor:pointer}
.err{color:var(--red);font-size:14px;margin-top:14px;min-height:20px}
</style></head><body>
<form method="post" autocomplete="on"><div class="logo">N</div><h1>__SHOP__</h1><p>Sign in to the dashboard</p>
<label for="u">Username</label><input id="u" name="username" autocomplete="username" required autofocus>
<label for="p">Password</label><input id="p" name="password" type="password" autocomplete="current-password" required>
<button type="submit">Sign in</button><div class="err" role="alert">__ERROR__</div></form>
<script>document.querySelector(".logo").textContent=(document.querySelector("h1").textContent.trim().slice(0,1)||"N");</script></body></html>"""

PAGE = r"""<!doctype html><html lang="en" data-theme="dark"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#0e1014"><link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="icon" href="/icon-192.png" type="image/png"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black"><meta name="apple-mobile-web-app-title" content="__SHOP__"><title>__SHOP__ Dashboard</title>
<script>(function(){try{var t=localStorage.getItem("theme");if(t==="light"||t==="dark")document.documentElement.dataset.theme=t;var a=localStorage.getItem("accent");if(a&&/^#[0-9a-f]{6}$/i.test(a))document.documentElement.style.setProperty("--accent",a);}catch(e){}})();</script>
<style>
:root{--onaccent:#04251a;color-scheme:dark;--bg:#0e1014;--panel:#161920;--panel2:#1b1f27;--line:#252a35;--ink:#e9ebf1;--ink2:#b3b9c7;--muted:#7d8496;
--accent:#34d399;--accent2:#1f9d74;--dot:#2a2f3b;--accentbg:#34d39918;--red:#f87171;--redbg:#f8717118;--amber:#fbbf24;--amberbg:#fbbf2418;--tip:#0a0b0e}
:root[data-theme=light]{color-scheme:light;--bg:#f4f5f8;--panel:#ffffff;--panel2:#f8f9fb;--line:#e4e7ee;--ink:#12151c;--ink2:#444b5a;--muted:#667085;
--accent:#0b8f63;--accent2:#8fd9bd;--dot:#d6dae3;--accentbg:#0b8f6314;--red:#d92d20;--redbg:#d92d200f;--amber:#b54708;--amberbg:#b547080f;--tip:#12151c}
*{box-sizing:border-box}
[hidden]{display:none!important}
body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.5 Inter,system-ui,"Segoe UI",Arial,sans-serif;-webkit-font-smoothing:antialiased}
svg.i{width:18px;height:18px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round;flex:none}
.app{display:grid;grid-template-columns:minmax(0,1fr) 240px;min-height:100vh}
main{padding:28px 36px 48px;min-width:0;max-width:1180px;width:100%;justify-self:center}
aside{position:sticky;top:0;height:100vh;border-left:1px solid var(--line);background:var(--panel);padding:22px 14px 18px;display:flex;flex-direction:column;gap:6px}
.brand{display:flex;align-items:center;gap:10px;padding:2px 10px 18px;font-weight:700;font-size:16px;letter-spacing:-.2px}
.logo{width:30px;height:30px;border-radius:9px;background:var(--accent);color:var(--onaccent);display:grid;place-items:center;font-weight:800;font-size:14px}
.brand span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
nav{display:flex;flex-direction:column;gap:2px}
nav a{display:flex;align-items:center;gap:12px;padding:10px 12px;border-radius:10px;color:var(--ink2);text-decoration:none;font-weight:500;transition:background .12s,color .12s}
nav a:hover{background:var(--panel2);color:var(--ink)}
nav a.on{background:var(--accentbg);color:var(--accent)}
nav a[hidden]{display:none}
.me{margin-top:auto;display:flex;align-items:center;gap:10px;padding:12px 10px 0;border-top:1px solid var(--line)}
.av{width:32px;height:32px;border-radius:50%;background:var(--panel2);border:1px solid var(--line);display:grid;place-items:center;font-weight:700;font-size:13px;text-transform:uppercase}
.me b{display:block;font-size:13px;line-height:1.2;overflow:hidden;text-overflow:ellipsis}.me small{color:var(--muted);font-size:12px}
header{display:flex;flex-wrap:wrap;gap:12px;align-items:center;justify-content:space-between;margin-bottom:22px}
h1{font-size:24px;letter-spacing:-.4px;margin:0;line-height:1.2}.sub{color:var(--muted);font-size:13px;margin-top:2px}
.hr{display:flex;gap:8px;align-items:center}
.live{display:flex;align-items:center;gap:8px;color:var(--ink2);font-size:13px;margin-right:6px}
.dot{width:8px;height:8px;border-radius:50%;background:var(--accent);box-shadow:0 0 0 3px var(--accentbg)}
.dot.stale{background:var(--amber);box-shadow:0 0 0 3px var(--amberbg)}
button.btn,a.btn{background:var(--panel);border:1px solid var(--line);color:var(--ink);border-radius:10px;padding:8px 12px;font:inherit;cursor:pointer;display:inline-flex;align-items:center;gap:8px;text-decoration:none}
button.btn:hover,a.btn:hover{border-color:var(--accent)}button.icon{padding:8px}
button.primary{background:var(--accent);color:var(--onaccent);border-color:var(--accent);font-weight:600}
.page{display:none}.page.on{display:block}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:14px;margin-bottom:14px}
.tile,.panel{background:var(--panel);border:1px solid var(--line);border-radius:14px}
.tile{padding:18px 20px}.tile .l{color:var(--muted);font-size:13px;font-weight:500;display:flex;flex-wrap:wrap;gap:6px;align-items:center}
.tile .v{font-size:28px;font-weight:700;margin:6px 0 2px;letter-spacing:-.6px;white-space:nowrap}.tile .v small{font-size:14px;color:var(--muted);font-weight:600;letter-spacing:0}
.tile .s{color:var(--muted);font-size:13px}
.grid{display:grid;grid-template-columns:minmax(0,3fr) minmax(0,2fr);gap:14px;margin-bottom:14px}
.grid3{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:14px}
.panel{padding:20px 22px;min-width:0}
.panel h2{font-size:15px;margin:0 0 14px;display:flex;justify-content:space-between;align-items:center;gap:8px;font-weight:650}
.panel h2 span,.panel h2 a{font-size:12.5px;color:var(--muted);font-weight:400;text-decoration:none}.panel h2 a:hover{color:var(--accent)}
.chart{position:relative}svg.ch{display:block;width:100%;height:auto;overflow:visible}
.gl{stroke:var(--line)}.tx{fill:var(--muted);font-size:11px}.val{fill:var(--ink);font-size:12px;font-weight:700}
.bar{fill:var(--accent2)}.bar.cur{fill:var(--accent)}
.tip{position:absolute;pointer-events:none;background:var(--tip);color:#fff;border-radius:8px;padding:6px 10px;font-size:12.5px;white-space:nowrap;transform:translate(-50%,-100%);opacity:0;transition:opacity .08s;z-index:5}
table{width:100%;border-collapse:collapse}th{text-align:left;color:var(--muted);font-weight:500;font-size:12px;padding:0 10px 10px 0;border-bottom:1px solid var(--line)}
td{padding:12px 10px 12px 0;border-bottom:1px solid var(--line);vertical-align:middle}tr:last-child td{border-bottom:0}
td.r,th.r{text-align:right;padding-right:0}.mono{font-variant-numeric:tabular-nums}
.scroll{overflow-x:auto;-webkit-overflow-scrolling:touch}.hit{touch-action:pan-y}
.pill{display:inline-block;padding:2px 10px;border-radius:999px;font-size:12px;font-weight:600;background:var(--panel2);color:var(--ink2);white-space:nowrap}
.pill.good{color:var(--accent);background:var(--accentbg)}.pill.bad{color:var(--red);background:var(--redbg)}.pill.warn{color:var(--amber);background:var(--amberbg)}
.muted{color:var(--muted)}
.row2{display:flex;justify-content:space-between;gap:12px;padding:11px 0;border-bottom:1px solid var(--line);align-items:center}.row2:last-child{border-bottom:0}
.row2 .t{min-width:0;overflow-wrap:anywhere}.row2 .t small{display:block;color:var(--muted);font-size:12px}.row2 .e{text-align:right;white-space:nowrap}
.qbar{height:6px;border-radius:99px;background:var(--panel2);overflow:hidden;margin-top:6px;min-width:90px}.qbar i{display:block;height:100%;background:var(--accent);border-radius:99px}
.qbar.warn i{background:var(--amber)}
.rev{padding:14px 0;border-bottom:1px solid var(--line)}.rev:last-child{border-bottom:0}
.rev .m{display:flex;flex-wrap:wrap;gap:10px;align-items:center;margin-bottom:6px;font-size:13px;color:var(--ink2)}
.rev .q{overflow-wrap:anywhere;white-space:pre-wrap}
.big{font-size:40px;font-weight:700;letter-spacing:-1px;line-height:1.1}.empty{color:var(--muted);padding:8px 0}
.err{background:var(--redbg);color:var(--red);border-radius:10px;padding:10px 14px;margin-bottom:14px;display:none}
.row{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0}
textarea{width:100%;background:var(--panel2);color:var(--ink);border:1px solid var(--line);border-radius:10px;padding:10px 12px;font:13px/1.5 Consolas,"SFMono-Regular",monospace;resize:vertical}
textarea:focus{outline:2px solid var(--accent);outline-offset:1px}
input,select{background:var(--panel2);color:var(--ink);border:1px solid var(--line);border-radius:10px;padding:9px 12px;font:inherit;min-width:0}
input:focus,select:focus{outline:2px solid var(--accent);outline-offset:1px}
.urow{display:flex;gap:10px;align-items:center;justify-content:space-between;padding:12px 0;border-bottom:1px solid var(--line);flex-wrap:wrap}
.score{display:flex;gap:28px;flex-wrap:wrap;align-items:flex-end}
.score div small{display:block;color:var(--muted);font-size:13px}
.chat{display:flex;flex-direction:column;height:calc(100vh - 150px);height:calc(100dvh - 150px);min-height:380px}
.chat .top{display:flex;justify-content:space-between;align-items:center;gap:10px;padding-bottom:12px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.chat .top b{font-size:15px}.onl{display:flex;gap:6px;flex-wrap:wrap;align-items:center;color:var(--muted);font-size:12.5px}
.onl i{width:7px;height:7px;border-radius:50%;background:var(--accent);display:inline-block;margin-right:4px}
.msgs{flex:1;overflow-y:auto;padding:10px 2px;display:flex;flex-direction:column;gap:2px;-webkit-overflow-scrolling:touch}
.m{max-width:78%;align-self:flex-start}.m.mine{align-self:flex-end}
.m .w{font-size:12px;color:var(--muted);margin:8px 6px 3px}.m.mine .w{text-align:right}
.bub{background:var(--panel2);border:1px solid var(--line);border-radius:14px;padding:8px 13px;overflow-wrap:anywhere;white-space:pre-wrap}
.m.mine .bub{background:var(--accentbg);border-color:transparent}
.day{align-self:center;color:var(--muted);font-size:12px;margin:12px 0 4px}
.send{display:flex;gap:8px;margin-top:12px;align-items:flex-end}
.send textarea{flex:1;resize:none;max-height:120px;font:inherit;line-height:1.4}
.badge{background:var(--red);color:#fff;border-radius:99px;font-size:11px;font-weight:700;padding:0 6px;line-height:17px;margin-left:auto}
.acts{display:flex;gap:10px;justify-content:flex-end;font-size:12px;margin:2px 6px 0;opacity:0;transition:opacity .12s}
.m:hover .acts,.m.touch .acts,.acts.on{opacity:1}
.acts button{background:none;border:0;color:var(--muted);cursor:pointer;font:inherit;padding:2px 0}.acts button:hover{color:var(--accent)}.acts button.del:hover,.acts button.sure{color:var(--red)}
.edited{color:var(--muted);font-size:11px;margin-left:6px}
.editbox{display:flex;flex-direction:column;gap:6px;min-width:240px}.editbox textarea{font:inherit;line-height:1.4;resize:none}
.editbox .row{margin:0;justify-content:flex-end}
.tg{display:flex;gap:6px;flex-wrap:wrap}.tg button{padding:5px 10px;font-size:12.5px}.tg button.on{border-color:var(--accent);color:var(--accent)}
@media(pointer:coarse){.acts{opacity:1}}
.mmbar{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:12px}
.mmsw{display:flex;gap:6px;padding:0 4px}.mmsw i{width:20px;height:20px;border-radius:50%;cursor:pointer;border:2px solid transparent;display:block}.mmsw i.on{border-color:var(--ink)}
.btn.on{border-color:var(--accent);color:var(--accent);background:var(--accentbg)}
.mmboard{position:relative;border:1px solid var(--line);border-radius:16px;overflow:auto;height:calc(100vh - 215px);height:calc(100dvh - 215px);min-height:360px;background-color:var(--panel);background-image:radial-gradient(var(--dot) 1.2px,transparent 1.2px);background-size:22px 22px}
.mmcv{position:relative;width:1800px;height:1200px}
svg.mml{position:absolute;inset:0;width:100%;height:100%;pointer-events:none}
svg.mml path{fill:none;stroke:var(--muted);stroke-width:2;opacity:.7}
svg.mml.on path{pointer-events:stroke;cursor:pointer;stroke-width:3}svg.mml.on path:hover{stroke:var(--red);opacity:1}svg.mml circle{fill:var(--muted);opacity:.8}
.note{position:absolute;width:218px;border-radius:6px 6px 14px 6px;color:#1d1a12;box-shadow:0 1px 2px #0003,0 10px 22px -8px #0006;transform:rotate(var(--r,0deg))}
.note.drag{box-shadow:0 2px 4px #0003,0 22px 34px -10px #0008;z-index:50;transform:rotate(0)}
.note.pick{outline:3px solid var(--accent);outline-offset:3px}
.note .h{display:flex;align-items:center;justify-content:space-between;gap:4px;padding:8px 6px 0 12px;cursor:grab;touch-action:none;font-size:11.5px;color:#0009;user-select:none}
.note.drag .h{cursor:grabbing}.note .h b{font-weight:600}.note .h span.who{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.note .h .nb{display:flex;gap:0;flex:none}
.note .nb button{border:0;background:none;color:#0009;cursor:pointer;font:inherit;font-size:12px;line-height:1;padding:3px 6px;border-radius:6px}.note .nb button:hover{background:#0002}
.note .nb button.sure{background:#d92d20;color:#fff}
.note textarea{display:block;width:100%;border:0;background:none;resize:none;font:inherit;font-size:14px;line-height:1.45;color:#1d1a12;padding:6px 12px 12px;outline:none;overflow:hidden;min-height:64px}
.note .tag{pointer-events:none;position:absolute;top:-9px;left:14px;background:var(--ink);color:var(--bg);font-size:10.5px;font-weight:700;border-radius:99px;padding:1px 9px}
@media(max-width:1000px){.grid{grid-template-columns:1fr}.grid3{grid-template-columns:1fr}.grid2{grid-template-columns:1fr}}
@media(max-width:820px){
 .app{display:block}
 main{padding:18px 16px calc(92px + env(safe-area-inset-bottom));padding-left:max(16px,env(safe-area-inset-left));padding-right:max(16px,env(safe-area-inset-right))}
 aside{position:fixed;left:0;right:0;bottom:0;top:auto;height:auto;border-left:0;border-top:1px solid var(--line);flex-direction:row;padding:6px 6px calc(6px + env(safe-area-inset-bottom));z-index:20}
 .brand,.me{display:none}
 nav{flex-direction:row;width:100%;gap:2px;overflow-x:auto;scrollbar-width:none}nav::-webkit-scrollbar{display:none}
 nav a{flex:1 0 62px;flex-direction:column;gap:2px;padding:7px 2px;font-size:11px;border-radius:10px;justify-content:center;text-align:center;position:relative;white-space:nowrap}
 .badge{position:absolute;top:2px;right:8px;margin:0}
 .chat{height:calc(100vh - 230px);height:calc(100dvh - 230px)}
 .mmboard{height:calc(100vh - 290px);height:calc(100dvh - 290px)}
 h1{font-size:21px}.live span#upd,#logout span{display:none}#logout{padding:8px}
 .panel{padding:16px}.tile{padding:14px 16px}.tile .v{font-size:23px}
 input,select,textarea,button.btn{font-size:16px}
 table.stack thead{display:none}
 table.stack,table.stack tbody{display:block;width:100%}
 table.stack tr{display:grid;grid-template-columns:1fr auto;grid-template-areas:"item status" "buyer price" "time qty";gap:2px 12px;padding:12px 0;border-bottom:1px solid var(--line)}
 table.stack tr:last-child{border-bottom:0}
 table.stack td{display:block;border:0;padding:0;text-align:left;white-space:normal!important;min-width:0;overflow-wrap:anywhere}
 table.stack td[data-label=Item]{grid-area:item;font-weight:600}
 table.stack td[data-label=Status]{grid-area:status;text-align:right}
 table.stack td[data-label=Buyer]{grid-area:buyer;color:var(--ink2)}
 table.stack td[data-label=Price]{grid-area:price;text-align:right}
 table.stack td[data-label=Time]{grid-area:time;font-size:12.5px}
 table.stack td[data-label=Qty]{grid-area:qty;text-align:right;font-size:12.5px;color:var(--muted)}
 table.stack td[data-label=Qty]::before{content:"Qty "}
}
@media(pointer:coarse){button.btn{min-height:42px}}
@media(max-width:560px){.tiles{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media(max-width:460px){.tiles{gap:10px}.tile{padding:12px 14px}.tile .v{font-size:19px}.tile .v small{font-size:12px}}

/* ---------- v2 additions ---------- */
.quote{text-align:center;color:var(--muted);font-size:13px;font-style:italic;margin:-8px 0 14px;letter-spacing:.1px}
.quote:before{content:"\201C"}.quote:after{content:"\201D"}
.grid2{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:14px;margin-bottom:14px}
.welcome{display:flex;flex-wrap:wrap;gap:6px 14px;align-items:center;justify-content:space-between;margin-bottom:14px;padding:16px 20px}
.welcome b{font-size:18px;letter-spacing:-.3px}.welcome .w2{color:var(--ink2);margin-top:2px}
.rec{display:inline-flex;align-items:center;gap:5px;padding:2px 10px;border-radius:999px;background:var(--amberbg);color:var(--amber);font-size:12px;font-weight:700;white-space:nowrap}
.rec:before{content:"\2605"}
.seg{display:inline-flex;border:1px solid var(--line);border-radius:10px;overflow:hidden;background:var(--panel)}
.seg button{background:none;border:0;color:var(--ink2);padding:7px 12px;font:inherit;cursor:pointer}
.seg button.on{background:var(--accentbg);color:var(--accent);font-weight:600}
.seg button+button{border-left:1px solid var(--line)}
select.sel{padding:7px 10px;border-radius:10px;background:var(--panel)}
.chips{display:flex;gap:6px;flex-wrap:wrap}
.chip{background:var(--panel2);border:1px solid var(--line);color:var(--ink2);border-radius:999px;padding:5px 13px;font:inherit;cursor:pointer}
.chip.on{border-color:var(--accent);color:var(--accent);background:var(--accentbg)}
.bar2{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:14px}
.bar2 input[type=search]{flex:1 1 220px;max-width:340px}
tr.click{cursor:pointer}tr.click:hover td{background:var(--panel2)}
a.lnk,button.lnk{background:none;border:0;padding:0;color:var(--accent);cursor:pointer;font:inherit;text-decoration:none}a.lnk:hover,button.lnk:hover{text-decoration:underline}
.sk{display:block;border-radius:8px;background:linear-gradient(100deg,var(--panel2) 30%,var(--line) 50%,var(--panel2) 70%);background-size:300% 100%;animation:sk 1.3s linear infinite}
.sk.tile{height:96px;border:1px solid var(--line)}.sk.line{height:14px;margin:14px 0}.sk.box{height:210px}
@keyframes sk{from{background-position:100% 0}to{background-position:0 0}}
body.hide .n,body.hide .tile .v,body.hide .tile .s,body.hide .big,body.hide td.mono,body.hide svg.ch,body.hide .row2 .e,body.hide .cal .cd b,body.hide .cal .cd s,body.hide .rows .v{filter:blur(7px);user-select:none}
body.hide .tip{display:none}
.cal{display:grid;grid-template-columns:repeat(7,minmax(0,1fr));gap:6px}
.cal .dh{color:var(--muted);font-size:12px;text-align:center;padding:2px 0 4px}
.cal .cd{position:relative;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:1px;min-height:62px;border-radius:10px;border:1px solid transparent;background:color-mix(in srgb,var(--accent) calc(var(--lv,0)*34%),var(--panel2));color:var(--ink);font:inherit;cursor:pointer;padding:4px 2px}
.cal .cd.off{background:none;cursor:default;pointer-events:none}
.cal .cd i{font-style:normal;font-size:11.5px;color:var(--ink2);position:absolute;top:4px;left:7px}
.cal .cd b{font-size:13px;margin-top:8px}.cal .cd s{text-decoration:none;font-size:10.5px;color:var(--muted)}
.cal .cd.today{border-color:var(--accent)}.cal .cd.sel{outline:2px solid var(--accent);outline-offset:1px}
.cal .cd.best:after{content:"\2605";position:absolute;top:3px;right:6px;color:var(--amber);font-size:12px}
.cal .cd:hover{border-color:var(--muted)}
.calhead{display:flex;align-items:center;justify-content:space-between;gap:8px;margin-bottom:12px}
.calhead b{font-size:15px;text-transform:capitalize}
.rows .r1{display:flex;justify-content:space-between;gap:10px;padding:10px 0;border-bottom:1px solid var(--line);align-items:center}.rows .r1:last-child{border-bottom:0}
.rows .r1 small{display:block;color:var(--muted);font-size:12px}
.rows .v{font-weight:650;text-align:right;white-space:nowrap}
.veil{position:fixed;inset:0;background:#0008;z-index:60;opacity:0;pointer-events:none;transition:opacity .15s}.veil.on{opacity:1;pointer-events:auto}
.drawer{position:fixed;top:0;right:0;bottom:0;width:min(440px,100vw);background:var(--panel);border-left:1px solid var(--line);z-index:61;transform:translateX(105%);transition:transform .2s;display:flex;flex-direction:column}
.drawer.on{transform:none}
.drawer .dh2{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:16px 18px;border-bottom:1px solid var(--line)}
.drawer .dh2 b{font-size:16px;overflow-wrap:anywhere}
.drawer .db{padding:16px 18px calc(24px + env(safe-area-inset-bottom));overflow-y:auto;flex:1}
.tl{list-style:none;margin:6px 0 4px;padding:0}.tl li{position:relative;padding:0 0 16px 28px;color:var(--muted)}
.tl li:before{content:"";position:absolute;left:5px;top:4px;width:10px;height:10px;border-radius:50%;border:2px solid var(--line);background:var(--panel)}
.tl li:after{content:"";position:absolute;left:9px;top:16px;bottom:-2px;width:2px;background:var(--line)}.tl li:last-child:after{display:none}
.tl li.done{color:var(--ink)}.tl li.done:before{background:var(--accent);border-color:var(--accent)}.tl li.done:after{background:var(--accent)}
.tl li small{display:block;color:var(--muted);font-size:12px}
.mini2{display:flex;gap:6px;flex-wrap:wrap;align-items:center}
.copy{font-size:12px;padding:3px 9px}
.drop{border:2px dashed var(--line);border-radius:14px;padding:18px;text-align:center;color:var(--muted);transition:border-color .12s,background .12s}
.drop.over{border-color:var(--accent);background:var(--accentbg);color:var(--accent)}
.dropall{position:fixed;inset:10px;border:3px dashed var(--accent);border-radius:20px;background:var(--accentbg);z-index:90;display:none;place-items:center;font-size:20px;font-weight:700;color:var(--accent);backdrop-filter:blur(3px);pointer-events:none}
.dropall.on{display:grid}
.pv{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0 0}
.toasts{position:fixed;right:16px;bottom:16px;z-index:80;display:flex;flex-direction:column;gap:8px;max-width:min(360px,calc(100vw - 32px))}
.toast2{background:var(--tip);color:#fff;border-radius:12px;padding:10px 14px;box-shadow:0 8px 24px #0006;animation:tin .18s;cursor:pointer}
.toast2 b{display:block;font-size:13px}.toast2 span{font-size:12.5px;opacity:.85}
@keyframes tin{from{transform:translateY(10px);opacity:0}}
.ptr{position:fixed;top:-48px;left:50%;margin-left:-18px;width:36px;height:36px;border-radius:50%;background:var(--panel);border:1px solid var(--line);display:grid;place-items:center;z-index:70;color:var(--accent);box-shadow:0 4px 14px #0004;transition:top .15s}
.ptr.spin svg{animation:spin .7s linear infinite}@keyframes spin{to{transform:rotate(360deg)}}
.sw{display:flex;gap:8px;flex-wrap:wrap;align-items:center}
.sw i{width:28px;height:28px;border-radius:50%;cursor:pointer;border:3px solid transparent;display:block;box-shadow:inset 0 0 0 1px #0003}.sw i.on{border-color:var(--ink)}
.sw input[type=color]{width:34px;height:34px;padding:0;border:0;border-radius:50%;background:none;cursor:pointer}
.field{display:flex;flex-direction:column;gap:5px;margin-bottom:14px}.field>label,.lab{font-size:13px;color:var(--muted)}
.tgl{display:flex;justify-content:space-between;gap:12px;align-items:center;padding:11px 0;border-bottom:1px solid var(--line)}.tgl:last-child{border-bottom:0}
.tgl small{display:block;color:var(--muted);font-size:12.5px}
.tgl input{width:20px;height:20px;accent-color:var(--accent)}
.typing{height:18px;font-size:12.5px;color:var(--muted);margin-top:4px}
.dotpill{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--line);margin-right:6px}.dotpill.on{background:var(--accent)}
.newdot{width:8px;height:8px;border-radius:50%;background:var(--red);margin-left:auto}
.nv{display:flex;gap:10px;align-items:baseline;flex-wrap:wrap}
.relnote{border-left:3px solid var(--accent);padding:2px 0 2px 14px;margin:0 0 22px}.relnote h3{margin:0 0 6px;font-size:15px}.relnote ul{margin:0;padding-left:18px}.relnote li{margin:3px 0}
.bigstat{display:flex;gap:28px;flex-wrap:wrap}
@media(max-width:820px){.toasts{bottom:84px}.drawer{width:100vw}.quote{margin:-4px 0 12px}.cal .cd{min-height:54px}.cal .cd s{display:none}.header-tools .seg button{padding:6px 9px}}
@media (prefers-reduced-motion:reduce){.sk,.drawer,.toast2{animation:none;transition:none}}

/* round 2 */
.hday{display:flex;justify-content:space-between;align-items:baseline;margin:14px 0 4px;padding-bottom:6px;border-bottom:1px solid var(--line);font-weight:600}.hday:first-child{margin-top:0}.hday span{font-weight:500;color:var(--muted);font-size:13px}
.hrow{display:flex;justify-content:space-between;gap:12px;align-items:center;padding:10px 0;border-bottom:1px solid var(--line)}.hrow:last-child{border-bottom:0}
.hrow .t small{display:block;color:var(--muted);font-size:12.5px}.hrow .amt{font-weight:700;font-variant-numeric:tabular-nums;text-align:right;white-space:nowrap}
.hrow .amt.add{color:var(--accent)}.hrow .amt.rem{color:var(--red)}.hrow .amt small{display:block;color:var(--muted);font-weight:400;font-size:12px}
.hrow .ic{width:30px;height:30px;border-radius:99px;display:grid;place-items:center;font-weight:700;flex:none;background:var(--accentbg);color:var(--accent)}.hrow .ic.rem{background:color-mix(in srgb,var(--red) 16%,transparent);color:var(--red)}
.hrow .l{display:flex;gap:12px;align-items:center;min-width:0}.hrow .t{min-width:0;overflow-wrap:anywhere}
body.hide .hrow .amt{filter:blur(7px);user-select:none}
.taxpot{display:flex;align-items:baseline;justify-content:center;gap:8px;flex-wrap:wrap;text-align:center;margin:-6px 0 16px;color:var(--ink2);font-size:14px}
.taxpot b{font-size:20px;color:var(--accent);font-variant-numeric:tabular-nums}.taxpot small{flex-basis:100%;color:var(--muted);font-size:12px}
.tile .v.bad{color:var(--red)}.tile .v.warn{color:var(--amber)}
body[data-bg=dots]{background-image:radial-gradient(color-mix(in srgb,var(--muted) 32%,transparent) 1px,transparent 1.3px);background-size:22px 22px;background-attachment:fixed}
body[data-bg=grid]{background-image:linear-gradient(color-mix(in srgb,var(--muted) 12%,transparent) 1px,transparent 1px),linear-gradient(90deg,color-mix(in srgb,var(--muted) 12%,transparent) 1px,transparent 1px);background-size:34px 34px;background-attachment:fixed}
body[data-bg=waves]{background-image:repeating-radial-gradient(circle at 0 100%,transparent 0 26px,color-mix(in srgb,var(--muted) 10%,transparent) 27px 28px);background-attachment:fixed}
body[data-bg=aurora]{background-image:radial-gradient(60% 50% at 8% 0%,color-mix(in srgb,var(--accent) 20%,transparent),transparent),radial-gradient(50% 45% at 100% 15%,color-mix(in srgb,#7c3aed 18%,transparent),transparent),radial-gradient(55% 45% at 60% 100%,color-mix(in srgb,#0ea5e9 14%,transparent),transparent);background-attachment:fixed}
body[data-bg=diagonal]{background-image:repeating-linear-gradient(45deg,transparent 0 14px,color-mix(in srgb,var(--muted) 9%,transparent) 14px 15px);background-attachment:fixed}
.calc{position:fixed;top:72px;right:20px;z-index:80;width:min(330px,calc(100vw - 32px));background:var(--panel);border:1px solid var(--line);border-radius:16px;padding:16px;box-shadow:0 18px 50px rgba(0,0,0,.4)}
.calc[hidden]{display:none}.calchead{display:flex;align-items:center;justify-content:space-between;margin-bottom:10px}
.calcrow{display:flex;gap:8px;align-items:center}.calcrow input,.calcres{flex:1;min-width:0;height:44px;border-radius:10px;background:var(--panel2);border:1px solid var(--line);color:var(--ink);padding:0 12px;font-size:18px;font-variant-numeric:tabular-nums;display:flex;align-items:center}
.calcrow select{height:44px}.calcmid{display:flex;justify-content:center;margin:6px 0}
.statrow{display:flex;justify-content:space-between;align-items:center;gap:10px;padding:10px 0;border-bottom:1px solid var(--line)}.statrow:last-child{border-bottom:0}.statrow small{display:block}
.men{color:var(--accent);font-weight:600}.m.tome .bub{box-shadow:0 0 0 2px var(--accent)}
.sugg{display:flex;gap:6px;flex-wrap:wrap;margin:6px 0 0}.sugg[hidden]{display:none}.sugg button{border:1px solid var(--line);background:var(--panel2);color:var(--ink);border-radius:99px;padding:5px 12px;font-size:13px;cursor:pointer}
.pv{display:inline-flex;align-items:center;gap:6px;font-weight:600}
.tsel .tgl{padding:8px 0}
.chips.wrap{flex-wrap:wrap}
body.hide .taxpot b,body.hide .calcres,body.hide .statrow .pill{filter:blur(7px);user-select:none}
@media(max-width:820px){.calc{top:12px;right:16px;left:16px;width:auto}}
</style></head><body><div class="app">
<main>
<div class="quote" id="quote" hidden></div>
<div class="taxpot dyn" id="taxpot" hidden></div>
<header><div><h1 id="title">Overview</h1><div class="sub">__SHOP__</div></div>
<div class="hr header-tools" style="flex-wrap:wrap;justify-content:flex-end">
<div class="live"><span class="dot" id="dot"></span><span id="upd"><span class="sk" style="width:84px;height:12px;display:inline-block;vertical-align:middle"></span></span></div>
<select class="sel" id="curSel" aria-label="Currency" title="Show amounts in"></select>
<div class="seg" id="gnSeg" title="Amounts after or before Eldorado's fees"><button type="button" data-g="0" class="on">Net</button><button type="button" data-g="1">Gross</button></div>
<button class="btn icon" id="calcbtn" title="Currency calculator" aria-label="Currency calculator"><svg class="i" viewBox="0 0 24 24"><rect x="5" y="3" width="14" height="18" rx="2"/><path d="M8 7h8M8 12h.01M12 12h.01M16 12h.01M8 16h.01M12 16h.01M16 16h.01"/></svg></button>
<button class="btn icon" id="hide" title="Hide all numbers" aria-label="Hide all numbers"><svg class="i" viewBox="0 0 24 24"><path d="M2 12s3.5-7 10-7 10 7 10 7-3.5 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/></svg></button>
<button class="btn" id="install" hidden><svg class="i" viewBox="0 0 24 24"><path d="M12 3v12M7 10l5 5 5-5M5 21h14"/></svg><span>Install app</span></button>
<button class="btn icon" id="theme" title="Light / dark" aria-label="Switch light or dark"><svg class="i" viewBox="0 0 24 24"><path d="M21 12.8A9 9 0 1111.2 3a7 7 0 009.8 9.8z"/></svg></button>
<button class="btn" id="logout"><svg class="i" viewBox="0 0 24 24"><path d="M9 21H5a2 2 0 01-2-2V5a2 2 0 012-2h4M16 17l5-5-5-5M21 12H9"/></svg><span>Sign out</span></button></div></header>
<div class="err" id="err"></div>
<div class="calc" id="calc" hidden role="dialog" aria-label="Currency calculator"><div class="calchead"><b>Currency calculator</b><button class="btn icon" id="calcx" type="button" aria-label="Close"><svg class="i" viewBox="0 0 24 24"><path d="M6 6l12 12M18 6L6 18"/></svg></button></div>
 <div class="calcrow"><input id="calca" type="text" inputmode="decimal" value="100" autocomplete="off" aria-label="Amount"><select id="calcf" aria-label="From"></select></div>
 <div class="calcmid"><button class="btn icon" id="calcsw" type="button" title="Swap" aria-label="Swap"><svg class="i" viewBox="0 0 24 24"><path d="M7 4v16M7 20l-3-3M7 20l3-3M17 20V4M17 4l-3 3M17 4l3 3"/></svg></button></div>
 <div class="calcrow"><div class="calcres" id="calcr">-</div><select id="calct" aria-label="To"></select></div>
 <div class="muted" id="calcn" style="font-size:12.5px;margin-top:10px"></div></div>

<section class="page" id="p-overview">
 <div class="panel welcome dyn" id="welcome"><div class="sk line" style="width:60%"></div></div>
 <div class="tiles dyn" id="tiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="grid">
  <div class="panel"><h2>Sales per month <span id="cur1"></span></h2><div class="chart dyn" id="chart1"><div class="sk box"></div></div></div>
  <div class="panel"><h2>Latest orders <a href="#orders">View all</a></h2><div class="dyn" id="latest"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div></div>
 </div>
 <div class="grid2">
  <div class="panel"><h2>Waiting to be completed <a href="#orders">Open</a></h2><div class="dyn" id="pend"><div class="sk line"></div><div class="sk line"></div></div></div>
  <div class="grid3 dyn" id="mini" style="grid-template-columns:repeat(auto-fit,minmax(150px,1fr))"><div class="sk tile"></div><div class="sk tile"></div></div>
 </div>
 <div class="panel" style="margin-top:14px"><h2>Eldorado connection <span id="statsum"></span></h2><div class="dyn" id="statbox"><div class="sk line"></div><div class="sk line"></div></div></div>
</section>

<section class="page" id="p-sales">
 <div class="tiles dyn" id="stiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="grid">
  <div class="panel"><h2>Sales per month <span id="cur2"></span></h2><div class="chart dyn" id="chart2"><div class="sk box"></div></div></div>
  <div class="panel"><h2>Records</h2><div class="rows dyn" id="recs"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div></div>
 </div>
 <div class="grid">
  <div class="panel"><div class="calhead"><button class="btn icon" id="calprev" aria-label="Previous month"><svg class="i" viewBox="0 0 24 24"><path d="M15 5l-7 7 7 7"/></svg></button><div style="text-align:center"><b id="calttl"></b><div class="muted" id="calsum" style="font-size:12.5px"></div></div><button class="btn icon" id="calnext" aria-label="Next month"><svg class="i" viewBox="0 0 24 24"><path d="M9 5l7 7-7 7"/></svg></button></div>
   <div class="cal dyn" id="cal"></div></div>
  <div class="panel"><h2>Day <span id="daydate"></span></h2><div class="dyn" id="dayd"><div class="empty">Pick a day in the calendar.</div></div></div>
 </div>
 <div class="grid">
  <div class="panel"><h2>Eldorado fees</h2><div class="rows dyn" id="fees"></div></div>
  <div class="panel"><h2>Monthly breakdown</h2><div class="scroll dyn" id="months"></div></div>
 </div>
</section>

<section class="page" id="p-history">
 <div class="tiles dyn" id="htiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="bar2"><div class="seg" id="hseg"><button type="button" data-h="all" class="on">All</button><button type="button" data-h="add">Added</button><button type="button" data-h="remove">Removed</button></div><span class="muted" id="hnote"></span></div>
 <div class="panel"><div class="dyn" id="hlist"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div>
  <div class="row" style="margin-top:12px"><button class="btn" id="hmore" type="button" hidden>Show more</button></div>
  <div class="muted" style="font-size:12.5px;margin-top:10px">Orders from before the history started are shown as added. Cancelled orders only show from when the history started.</div></div>
</section>

<section class="page" id="p-orders">
 <div class="panel" style="margin-bottom:14px"><h2>Waiting to be completed <span id="pendsum"></span></h2><div class="dyn" id="opend"></div></div>
 <div class="bar2"><input type="search" id="osearch" placeholder="Search buyer, item or order ID" autocomplete="off">
  <div class="chips" id="ochips"><button class="chip on" data-f="all">All</button><button class="chip" data-f="pending">Waiting</button><button class="chip" data-f="done">Completed</button></div>
  <span class="muted" id="ocount"></span></div>
 <div class="panel"><div class="scroll dyn" id="orders"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div></div>
</section>

<section class="page" id="p-stock"><div class="panel"><h2>Stock <span id="stocksum"></span></h2><div class="dyn" id="stock"><div class="sk line"></div><div class="sk line"></div></div></div></section>

<section class="page" id="p-reviews">
 <div class="panel" style="margin-bottom:14px"><div class="score dyn" id="revsum"></div></div>
 <div class="bar2"><div class="seg" id="rvseg"><button type="button" data-r="all" class="on">All</button><button type="button" data-r="good">Good</button><button type="button" data-r="bad">Bad</button></div></div>
 <div class="panel"><h2>Latest reviews <span id="rvnote"></span></h2><div class="dyn" id="reviews"><div class="sk line"></div><div class="sk line"></div></div></div>
</section>

<section class="page" id="p-keys"><div class="grid"><div>
 <div class="panel" style="margin-bottom:14px"><h2>Keys left</h2><div class="dyn" id="keyshead"></div></div>
 <div class="panel" id="addkeys" style="display:none;margin-bottom:14px"><h2>Add keys <span>one per line</span></h2>
  <div class="drop" id="dz">Drop a .txt file here, anywhere on the page, or <label class="lnk" for="kf" style="cursor:pointer">choose a file</label>.<input id="kf" type="file" accept=".txt,text/plain" hidden></div>
  <textarea id="kt" rows="6" spellcheck="false" style="margin-top:10px" placeholder="NETF-XXXX-XXXX-XXXX&#10;NETF-XXXX-XXXX-XXXX"></textarea>
  <div class="pv dyn" id="kprev"></div>
  <div class="row" style="align-items:center"><button class="btn primary" id="kadd" disabled>Add keys</button><span class="muted" id="kcount"></span></div>
  <div id="kmsg" style="margin-top:6px"></div></div>
 <div class="panel" id="findkey" style="display:none"><h2>Find a key <span>which order got it?</span></h2>
  <div class="row"><input id="fk" placeholder="Paste a key" autocomplete="off" spellcheck="false" style="flex:1 1 200px"><button class="btn" id="fkgo">Search</button></div>
  <div class="dyn" id="fkres"></div></div>
 </div><div class="panel"><h2>Refills</h2><div class="dyn" id="keys"></div></div></div></section>

<section class="page" id="p-warroom"><div class="panel chat">
 <div class="top"><b>War-Room <span class="muted" style="font-weight:400">· admins only</span></b><div class="onl dyn" id="onl"></div></div>
 <div class="tg" style="margin:10px 0 0"><button class="btn" id="tsound" type="button">Sound: on</button><button class="btn" id="tnote" type="button">Notifications: off</button></div>
 <div class="msgs dyn" id="msgs"></div>
 <div class="typing dyn" id="typing"></div>
 <div class="sugg dyn" id="wsugg" hidden></div>
 <form class="send" id="wform"><textarea id="wt" rows="1" maxlength="1000" placeholder="Write a message..." autocomplete="off"></textarea>
 <button class="btn primary" id="wsend" type="submit">Send</button></form>
 <div class="muted" id="wmsg" style="font-size:12.5px;min-height:18px;margin-top:4px">Enter sends, Shift+Enter for a new line.</div>
</div></section>

<section class="page" id="p-mindmap">
 <div class="mmbar"><button class="btn primary" id="mmadd"><svg class="i" viewBox="0 0 24 24"><path d="M12 5v14M5 12h14"/></svg>Add note</button>
 <div class="mmsw" id="mmsw"></div>
 <button class="btn" id="mmlink"><svg class="i" viewBox="0 0 24 24"><path d="M10 14a5 5 0 007 0l3-3a5 5 0 00-7-7l-1 1M14 10a5 5 0 00-7 0l-3 3a5 5 0 007 7l1-1"/></svg>Connect</button>
 <span class="muted" id="mmhint" style="font-size:12.5px">Drag a note by its top bar. Click the text to edit.</span></div>
 <div class="mmboard" id="mmboard"><div class="mmcv" id="mmcv"><svg class="mml" id="mml"></svg></div></div>
</section>

<section class="page" id="p-profit">
 <div class="tiles dyn" id="ptiles"></div>
 <div class="grid">
  <div class="panel"><h2>Add a cost <span>VPS, domain, keys...</span></h2>
   <div class="row"><input id="cn" placeholder="What is it for?" maxlength="60" style="flex:2 1 160px" autocomplete="off">
    <input id="ca" type="number" min="0" step="0.01" placeholder="Amount" style="flex:1 1 90px" inputmode="decimal">
    <select id="cc"><option>DKK</option><option>USD</option><option>EUR</option></select></div>
   <div class="row"><select id="ck"><option value="once">One time</option><option value="monthly">Every month</option></select>
    <input id="cd" type="date" style="flex:1 1 180px;min-width:180px"><button class="btn primary" id="cadd">Add cost</button></div>
   <div class="muted" id="cmsg" style="min-height:20px"></div>
   <h2 style="margin-top:14px">Price of one key <span>counted for every unit sold</span></h2>
   <div class="row"><input id="kcamt" type="number" min="0" step="0.01" placeholder="0.00" style="flex:1 1 90px" inputmode="decimal"><select id="kccur"><option>DKK</option><option>USD</option><option>EUR</option></select><button class="btn" id="kcsave">Save</button></div>
  </div>
  <div class="panel"><h2>Your costs</h2><div class="dyn" id="clist"></div></div>
 </div>
 <div class="panel"><h2>Profit per month <span id="pnote"></span></h2><div class="scroll dyn" id="pmonths"></div></div>
</section>

<section class="page" id="p-users"><div class="grid">
 <div class="panel"><h2>Users</h2><div class="dyn" id="ulist"></div><div class="muted" id="umsg" style="margin-top:8px"></div></div>
 <div class="panel"><h2>Add user</h2><div class="row"><input id="nu" placeholder="Username" autocomplete="off" style="flex:1 1 140px">
 <input id="np" type="password" placeholder="Password (8+ characters)" autocomplete="new-password" style="flex:1 1 140px">
 <select id="nr"><option value="viewer">Viewer</option><option value="admin">Admin</option></select></div>
 <div class="row"><button class="btn primary" id="addu">Add user</button></div></div>
</div>
<div class="grid">
 <div class="panel"><h2>Logged-in devices</h2><div class="dyn" id="devall"></div></div>
 <div class="panel"><h2>Recent sign-ins</h2><div class="dyn" id="loglist"></div></div>
</div></section>

<section class="page" id="p-settings"><div class="grid2">
 <div>
  <div class="panel" style="margin-bottom:14px"><h2>Language</h2><div class="seg" id="langSeg"><button type="button" data-l="da">Dansk</button><button type="button" data-l="en">English</button></div></div>
  <div class="panel" style="margin-bottom:14px"><h2>Amounts</h2>
   <div class="field"><label>Show amounts in</label><div class="seg" id="curSeg"></div><div class="muted" id="curnote" style="font-size:12.5px"></div></div>
   <div class="field"><label>Fees</label><div class="seg" id="gnSeg2"><button type="button" data-g="0">Net (after fees)</button><button type="button" data-g="1">Gross (before fees)</button></div></div>
   <div class="tgl"><div>Hide all numbers<small>Blurs every amount. Good when someone looks over your shoulder. Only on this device.</small></div><input type="checkbox" id="setHide"></div>
  </div>
  <div class="panel" style="margin-bottom:14px"><h2>Look</h2>
   <div class="field"><label>Accent colour</label><div class="sw" id="sw"></div></div>
   <div class="field"><label>Background</label><div class="chips" id="bgSeg"></div></div>
   <div class="field" style="margin-bottom:0"><label>Light or dark</label><div class="seg" id="thSeg"><button type="button" data-t="dark">Dark</button><button type="button" data-t="light">Light</button></div></div>
  </div>
  <div class="panel" style="margin-top:14px"><h2>Overview</h2><div class="muted" style="font-size:12.5px;margin-bottom:6px">Choose what is shown on the overview.</div><div id="tilesel"></div></div>
 </div>
 <div>
  <div class="panel" style="margin-bottom:14px" id="notifybox"><h2>Notifications <span>admins</span></h2>
   <div class="field"><label>Sound</label><div class="row" style="margin:0"><select id="sndsel"><option value="ding">Ding</option><option value="bell">Bell</option><option value="pop">Pop</option><option value="chime">Chime</option><option value="none">No sound</option></select><button class="btn" id="sndtest" type="button">Play</button></div></div>
   <div class="tgl"><div>War-Room messages</div><input type="checkbox" data-n="warroom"></div>
   <div class="tgl"><div>New orders</div><input type="checkbox" data-n="orders"></div>
   <div class="tgl"><div>Bad reviews</div><input type="checkbox" data-n="reviews"></div>
   <div class="tgl"><div>Keys running low<small>10 or fewer keys left, and when they run out.</small></div><input type="checkbox" data-n="keys"></div>
   <div class="row" style="margin-top:12px"><button class="btn" id="setnote" type="button">Notifications: off</button></div>
   <div class="muted" style="font-size:12.5px">The switch above turns notifications on for this device. The boxes decide which ones you get.</div>
  </div>
  <div class="panel" style="margin-bottom:14px" id="profbox"><h2>Profile <span>admins</span></h2>
   <div class="field"><label>Emoji</label><input id="pemoji" maxlength="4" placeholder="🙂" autocomplete="off" style="width:90px;text-align:center"></div>
   <div class="field"><label>Name colour</label><div class="sw" id="pcol"></div></div>
   <div class="muted" style="font-size:12.5px;margin-bottom:6px">How you look in the War-Room:</div><div class="dyn" id="pprev"></div></div>
  <div class="panel" style="margin-bottom:14px" id="taxbox"><h2>Tax pot <span>admins</span></h2>
   <div class="field" style="margin-bottom:6px"><label>Tax percent</label><div class="row" style="margin:0;align-items:center"><input type="number" id="taxpct" min="0" max="80" step="0.5" inputmode="decimal" style="width:100px"> <span>%</span></div></div>
   <div class="muted" style="font-size:12.5px">Counted on profit (sales after fees − costs) and shown in kroner at the top of every page.</div></div>
  <div class="panel" style="margin-bottom:14px"><h2>Today widget</h2>
   <div class="muted" style="font-size:13px;margin-bottom:10px">A small page with today's sales, number of orders and time since the last order. Add it to your home screen. On Android you can also hold the app icon and pick “Today”.</div>
   <a class="btn" href="/widget" target="_blank" rel="noopener">Open the widget page</a></div>
  <div class="panel"><h2>My devices</h2><div class="dyn" id="mydev"></div></div>
 </div>
</div></section>

<section class="page" id="p-news"><div class="panel"><h2>What's new in the dashboard</h2><div id="newsbox"></div></div></section>
</main>

<aside>
 <div class="brand"><div class="logo" id="logo">N</div><span>__SHOP__</span></div>
 <nav id="nav">
  <a href="#overview" data-p="overview"><svg class="i" viewBox="0 0 24 24"><path d="M3 11l9-8 9 8"/><path d="M5 10v10h14V10"/></svg>Overview</a>
  <a href="#sales" data-p="sales"><svg class="i" viewBox="0 0 24 24"><path d="M5 20V11M12 20V4M19 20v-6"/></svg>Sales</a>
  <a href="#history" data-p="history"><svg class="i" viewBox="0 0 24 24"><path d="M3 12a9 9 0 109-9 9 9 0 00-7 3.4M3 4v4h4"/><path d="M12 8v4l3 2"/></svg>History</a>
  <a href="#orders" data-p="orders"><svg class="i" viewBox="0 0 24 24"><path d="M6 3h12v18l-3-2-3 2-3-2-3 2z"/><path d="M9 8h6M9 12h6"/></svg>Orders</a>
  <a href="#stock" data-p="stock"><svg class="i" viewBox="0 0 24 24"><path d="M21 8l-9-5-9 5v8l9 5 9-5z"/><path d="M3 8l9 5 9-5M12 13v8"/></svg>Stock</a>
  <a href="#reviews" data-p="reviews"><svg class="i" viewBox="0 0 24 24"><path d="M12 3l2.7 5.6 6.1.9-4.4 4.3 1 6.1L12 17l-5.4 2.9 1-6.1L3.2 9.5l6.1-.9z"/></svg>Reviews</a>
  <a href="#keys" data-p="keys"><svg class="i" viewBox="0 0 24 24"><circle cx="8" cy="15" r="4"/><path d="M11 12l9-9M16 7l3 3"/></svg>Keys</a>
  <a href="#warroom" data-p="warroom" id="navwar" hidden><svg class="i" viewBox="0 0 24 24"><path d="M21 12a8 8 0 01-11.6 7.1L4 20l1-4.6A8 8 0 1121 12z"/></svg>War-Room<span class="badge" id="wbadge" style="display:none"></span></a>
  <a href="#mindmap" data-p="mindmap" id="navmind" hidden><svg class="i" viewBox="0 0 24 24"><circle cx="12" cy="12" r="2.5"/><circle cx="4.5" cy="5.5" r="2"/><circle cx="19.5" cy="6" r="2"/><circle cx="6" cy="19" r="2"/><path d="M10 10.5L6 7M14 10.5l4-3M10.5 14l-3 3.5"/></svg>Mindmap</a>
  <a href="#profit" data-p="profit" id="navprofit" hidden><svg class="i" viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 7v10M9.5 9.5c0-1 1-1.5 2.5-1.5s2.5.6 2.5 1.7c0 2.3-5 1.3-5 3.6 0 1.1 1 1.7 2.5 1.7s2.5-.5 2.5-1.5"/></svg>Profit</a>
  <a href="#users" data-p="users" id="navusers" hidden><svg class="i" viewBox="0 0 24 24"><circle cx="9" cy="8" r="3.5"/><path d="M2 20c0-4 3-6 7-6s7 2 7 6M17 5a3.5 3.5 0 010 7M22 20c0-3-2-5-4-5.5"/></svg>Users</a>
  <a href="#settings" data-p="settings"><svg class="i" viewBox="0 0 24 24"><path d="M4 6h10M18 6h2M4 12h4M12 12h8M4 18h12M20 18h0"/><circle cx="16" cy="6" r="2"/><circle cx="10" cy="12" r="2"/><circle cx="18" cy="18" r="2"/></svg>Settings</a>
  <a href="#news" data-p="news"><svg class="i" viewBox="0 0 24 24"><path d="M12 3l1.8 4.7L18.5 9.5l-4.7 1.8L12 16l-1.8-4.7L5.5 9.5l4.7-1.8z"/><path d="M19 15l.8 2 2 .8-2 .8-.8 2-.8-2-2-.8 2-.8z"/></svg>What's new<span class="newdot" id="newdot" hidden></span></a>
 </nav>
 <div class="me"><div class="av" id="av"></div><div style="min-width:0"><b id="who"></b><small id="role"></small></div></div>
</aside>
</div>
<div class="veil" id="veil"></div>
<div class="drawer" id="drawer" aria-hidden="true"><div class="dh2"><b id="dtitle"></b><div class="mini2"><button class="btn" id="dback" hidden>Back</button><button class="btn icon" id="dclose" aria-label="Close"><svg class="i" viewBox="0 0 24 24"><path d="M6 6l12 12M18 6L6 18"/></svg></button></div></div><div class="db dyn" id="dbody"></div></div>
<div class="dropall" id="dropall">Drop the keys file here</div>
<div class="toasts" id="toasts"></div>
<div class="ptr" id="ptr"><svg class="i" viewBox="0 0 24 24"><path d="M21 12a9 9 0 11-3-6.7M21 4v5h-5"/></svg></div>
<script>
const DA={
"10 or fewer keys left, and when they run out.": "10 eller færre keys tilbage, og når de er løbet tør.",
"Accent colour": "Farve",
"Add": "Tilføj",
"Add a cost": "Tilføj en omkostning",
"Add cost": "Tilføj omkostning",
"Add keys": "Tilføj keys",
"Add note": "Tilføj note",
"Add user": "Tilføj bruger",
"Added": "Tilføjet",
"Admin": "Admin",
"All": "Alle",
"All offers stocked": "Alle tilbud er på lager",
"All orders from this buyer": "Alle ordrer fra denne køber",
"All time": "Hele tiden",
"Amount": "Beløb",
"Amounts": "Beløb",
"Amounts after or before Eldorado's fees": "Beløb efter eller før Eldorados gebyrer",
"Average order": "Gennemsnitlig ordre",
"Back": "Tilbage",
"Bad": "Dårlige",
"Bad review": "Dårlig anmeldelse",
"Bad reviews": "Dårlige anmeldelser",
"Before fees": "Før gebyrer",
"Bell": "Klokke",
"Best day": "Bedste dag",
"Best day ever": "Bedste dag nogensinde",
"Best day ever!": "Bedste dag nogensinde!",
"Best month": "Bedste måned",
"Best month ever!": "Bedste måned nogensinde!",
"Best week": "Bedste uge",
"Best week ever!": "Bedste uge nogensinde!",
"Blurs every amount. Good when someone looks over your shoulder. Only on this device.": "Slører alle beløb. Godt når nogen kigger med over skulderen. Kun på denne enhed.",
"Browsers only allow notifications on https:// pages (or localhost).": "Browsere tillader kun notifikationer på https://-sider (eller localhost).",
"Buyer": "Køber",
"Cancel": "Annuller",
"Chime": "Klang",
"Close": "Luk",
"Colour": "Farve",
"Completed": "Gennemført",
"Connect": "Forbind",
"Connect mode: click the top bar of one note, then another. Click a line to remove it.": "Forbind-tilstand: klik på toppen af én note, derefter en anden. Klik på en streg for at fjerne den.",
"Connection lost": "Forbindelse mistet",
"Converted with rough rates (live rates could not be fetched). Eldorado pays out in": "Omregnet med omtrentlige kurser (de aktuelle kurser kunne ikke hentes). Eldorado udbetaler i",
"Converted with today's rates": "Omregnet med dagens kurser",
"Copied": "Kopieret",
"Copy": "Kopiér",
"Copy name": "Kopiér navn",
"Copy order ID": "Kopiér ordre-ID",
"Cost added.": "Omkostning tilføjet.",
"Costs": "Omkostninger",
"Costs all time": "Omkostninger i alt",
"Could not load.": "Kunne ikke indlæse.",
"Could not reach the server.": "Kunne ikke nå serveren.",
"Currency": "Valuta",
"Dark": "Mørk",
"Day": "Dag",
"Default": "Standard",
"Delete": "Slet",
"Delete user": "Slet bruger",
"Delete?": "Slet?",
"Deleted.": "Slettet.",
"Delivered": "Leveret",
"Drag a note by its top bar. Click the text to edit.": "Træk en note i toppen. Klik på teksten for at redigere.",
"Drop a .txt file here, anywhere on the page, or": "Slip en .txt-fil her, eller hvor som helst på siden, eller",
"Drop the keys file here": "Slip keys-filen her",
"Edit": "Rediger",
"Eldorado fee": "Eldorado-gebyr",
"Eldorado fees": "Eldorado-gebyrer",
"Eldorado keeps about": "Eldorado beholder cirka",
"Eldorado pays out in": "Eldorado udbetaler i",
"Enter sends, Shift+Enter for a new line.": "Enter sender, Shift+Enter giver ny linje.",
"Every month": "Hver måned",
"Fees": "Gebyrer",
"File too large.": "Filen er for stor.",
"Find a key": "Find en key",
"First order": "Første ordre",
"Good": "Gode",
"Good evening": "God aften",
"Good morning": "God morgen",
"Good night": "God nat",
"Good review": "God anmeldelse",
"Gross": "Brutto",
"Gross (before fees)": "Brutto (før gebyrer)",
"Hello": "Goddag",
"Hide all numbers": "Skjul alle tal",
"In stock": "På lager",
"Install app": "Installér app",
"Install the app": "Installér appen",
"Item": "Vare",
"Keys left": "Keys tilbage",
"Keys running low": "Keys er ved at løbe tør",
"Label": "Mærkat",
"Language": "Sprog",
"Latest order": "Seneste ordre",
"Latest orders": "Seneste ordrer",
"Latest reviews": "Seneste anmeldelser",
"Light": "Lys",
"Light / dark": "Lys / mørk",
"Light or dark": "Lys eller mørk",
"Logged-in devices": "Enheder der er logget ind",
"Look": "Udseende",
"Month": "Måned",
"Monthly breakdown": "Måned for måned",
"My devices": "Mine enheder",
"Name": "Navn",
"Net": "Netto",
"Net (after fees)": "Netto (efter gebyrer)",
"New": "Ny",
"New order": "Ny ordre",
"New orders": "Nye ordrer",
"New password": "Ny adgangskode",
"New record!": "Ny rekord!",
"Next month": "Næste måned",
"No bad reviews. Nice.": "Ingen dårlige anmeldelser. Flot.",
"No costs added yet.": "Ingen omkostninger tilføjet endnu.",
"No devices.": "Ingen enheder.",
"No fee is set up, so net and gross are the same.": "Der er ikke sat et gebyr op, så netto og brutto er det samme.",
"No messages yet. Say hi.": "Ingen beskeder endnu. Sig hej.",
"No order found for this key.": "Ingen ordre fundet for denne key.",
"No orders found.": "Ingen ordrer fundet.",
"No orders match.": "Ingen ordrer matcher.",
"No orders yet.": "Ingen ordrer endnu.",
"No refills logged yet.": "Ingen genopfyldninger endnu.",
"No reviews yet.": "Ingen anmeldelser endnu.",
"No sales this day.": "Intet salg denne dag.",
"No sound": "Ingen lyd",
"No written message": "Ingen skrevet besked",
"Not a key": "Ikke en key",
"Not in the queue": "Ikke i køen",
"Not uploaded yet": "Ikke uploadet endnu",
"Nothing in stock right now.": "Intet på lager lige nu.",
"Nothing is waiting. All orders are completed.": "Intet venter. Alle ordrer er gennemført.",
"Nothing yet.": "Intet endnu.",
"Notifications": "Notifikationer",
"Notifications are on while the page is open.": "Notifikationer er slået til mens siden er åben.",
"Notifications: off": "Notifikationer: fra",
"On iPhone/iPad: tap the Share button in Safari, then \"Add to Home Screen\".": "På iPhone/iPad: tryk på Del-knappen i Safari og vælg derefter \"Føj til hjemmeskærm\".",
"One time": "En gang",
"Only orders the dashboard has seen are listed.": "Kun ordrer som dashboardet har set vises.",
"Open": "Åbn",
"Order": "Ordre",
"Order ID": "Ordre-ID",
"Orders": "Ordrer",
"Orders this month": "Ordrer denne måned",
"Out of keys": "Ingen keys tilbage",
"Overview": "Overblik",
"Paid": "Betalt",
"Password (8+ characters)": "Adgangskode (mindst 8 tegn)",
"Password changed. That user was signed out on all devices.": "Adgangskoden er ændret. Brugeren er logget ud på alle enheder.",
"Paste a key": "Indsæt en key",
"Pick a day in the calendar.": "Vælg en dag i kalenderen.",
"Pick any colour": "Vælg en farve",
"Placed": "Afgivet",
"Play": "Afspil",
"Previous month": "Forrige måned",
"Price": "Pris",
"Price of one key": "Pris på én key",
"Profit all time": "Profit i alt",
"Profit per month": "Profit pr. måned",
"Profit this month": "Profit denne måned",
"Qty": "Antal",
"Quantity": "Antal",
"Received": "Modtaget",
"Recent sign-ins": "Seneste logins",
"Records": "Rekorder",
"Records are counted after fees.": "Rekorder tælles efter gebyrer.",
"Refills": "Genopfyldninger",
"Reviews": "Anmeldelser",
"Running low": "Ved at løbe tør",
"Sales": "Salg",
"Sales per month": "Salg pr. måned",
"Save": "Gem",
"Saved.": "Gemt.",
"Search": "Søg",
"Search buyer, item or order ID": "Søg efter køber, vare eller ordre-ID",
"Set": "Sæt",
"Settings": "Indstillinger",
"Show amounts in": "Vis beløb i",
"Showing the last known values.": "Viser de sidst kendte værdier.",
"Sign out": "Log ud",
"Some data could not be loaded from Eldorado": "Nogle data kunne ikke hentes fra Eldorado",
"Sound": "Lyd",
"Sound: on": "Lyd: til",
"Spent": "Brugt",
"Stock": "Lager",
"Sure?": "Sikker?",
"Sure? Delete": "Sikker? Slet",
"Switch light or dark": "Skift mellem lys og mørk",
"The switch above turns notifications on for this device. The boxes decide which ones you get.": "Knappen ovenfor slår notifikationer til på denne enhed. Boksene bestemmer hvilke du får.",
"This device": "Denne enhed",
"This month": "Denne måned",
"This only works if Eldorado shows the delivered key inside the order, and only for orders the dashboard has seen": "Det virker kun hvis Eldorado viser den leverede key inde i ordren, og kun for ordrer som dashboardet har set",
"Time": "Tid",
"Timeline": "Tidslinje",
"Times after payment are when the dashboard first saw the new status.": "Tidspunkter efter betaling er hvornår dashboardet første gang så den nye status.",
"To write to them: find this order on Eldorado with the order ID.": "For at skrive til dem: find ordren på Eldorado med ordre-ID'et.",
"Today": "I dag",
"Type at least 6 characters of the key.": "Skriv mindst 6 tegn af keyen.",
"Uploaded to Eldorado (in stock or sold)": "Uploadet til Eldorado (på lager eller solgt)",
"User added.": "Bruger tilføjet.",
"Username": "Brugernavn",
"Users": "Brugere",
"VPS, domain, keys...": "VPS, domæne, keys...",
"View all": "Se alle",
"Viewer": "Seer",
"Waiting": "Venter",
"Waiting in the queue": "Venter i køen",
"Waiting to be completed": "Venter på at blive gennemført",
"War-Room messages": "War-Room-beskeder",
"Week": "Uge",
"What is it for?": "Hvad er det til?",
"What's new": "Nyt",
"What's new in the dashboard": "Nyt i dashboardet",
"When": "Hvornår",
"Write a message...": "Skriv en besked...",
"Yesterday": "I går",
"You": "Dig",
"You keep": "Du beholder",
"You will get notifications even when the app is closed.": "Du får notifikationer, også når appen er lukket.",
"Your costs": "Dine omkostninger",
"Your sales are counted in": "Dit salg tælles i",
"added.": "tilføjet.",
"after fees": "efter gebyrer",
"all time": "i alt",
"already exist": "findes allerede",
"already existed.": "fandtes allerede.",
"are typing...": "skriver...",
"bad": "dårlige",
"before fees": "før gebyrer",
"blocked in browser": "blokeret i browseren",
"buyer confirmed receipt": "køber har bekræftet modtagelse",
"choose a file": "vælg en fil",
"costs": "omkostninger",
"counted for every unit sold": "tælles for hver solgt enhed",
"edited": "redigeret",
"every month": "hver måned",
"failed": "fejlede",
"found": "fundet",
"good": "gode",
"gross": "brutto",
"h ago": "t siden",
"in stock": "på lager",
"incl. keys": "inkl. keys",
"install the app first": "installér appen først",
"invalid": "ugyldige",
"is typing...": "skriver...",
"just now": "lige nu",
"keys used so far": "keys brugt indtil nu",
"last seen": "sidst set",
"left": "tilbage",
"low": "lav",
"min ago": "min siden",
"more": "flere",
"needs https": "kræver https",
"net": "netto",
"never seen": "aldrig set",
"new": "nye",
"not supported": "ikke understøttet",
"not yet": "ikke endnu",
"of every order (rounded up to the cent). You keep": "af hver ordre (rundet op til nærmeste cent). Du beholder",
"of what buyers paid.": "af det køberne betalte.",
"off": "fra",
"on": "til",
"on (also when closed)": "til (også når lukket)",
"one per line": "én pr. linje",
"one time": "en gang",
"online now": "online nu",
"pasted": "indsat",
"positive": "positive",
"sales after fees − costs": "salg efter gebyrer − omkostninger",
"signed in": "logget ind",
"skipped (bad format).": "sprunget over (forkert format).",
"time not tracked": "tidspunkt ikke registreret",
"today": "i dag",
"tracked": "registreret",
"units": "enheder",
"used so far": "brugt indtil nu",
"waiting": "venter",
"waiting in total.": "venter i alt.",
"waiting to be completed": "venter på at blive gennemført",
"which order got it?": "hvilken ordre fik den?",
"· admins only": "· kun admins",
"admin": "admin",
"viewer": "seer",
"Blue": "Blå",
"Purple": "Lilla",
"Pink": "Pink",
"Orange": "Orange",
"Red": "Rød",
"Teal": "Turkis",
"Yellow": "Gul",
"Important": "Vigtigt",
"Idea": "Idé",
"Todo": "Skal gøres",
"Done": "Færdig",
"Profit": "Profit",
"Install": "Installér",
"Today widget": "I dag-widget",
"Open the widget page": "Åbn widget-siden",
"A small page with today's sales, number of orders and time since the last order. Add it to your home screen. On Android you can also hold the app icon and pick “Today”.": "En lille side med dagens salg, antal ordrer og tid siden seneste ordre. Føj den til din startskærm. På Android kan du også holde fingeren på app-ikonet og vælge “I dag”.",
"Choose what is shown on the overview.": "Vælg hvad der vises på overblikket.",
"Background": "Baggrund",
"Profile": "Profil",
"Emoji": "Emoji",
"Name colour": "Navnefarve",
"How you look in the War-Room:": "Sådan ser du ud i War-Room:",
"Tax pot": "Skattepotte",
"Tax percent": "Skatteprocent",
"Counted on profit (sales after fees − costs) and shown in kroner at the top of every page.": "Regnes af profit (salg efter gebyrer − omkostninger) og vises i kroner øverst på alle sider.",
"Currency calculator": "Valutaregner",
"Swap": "Byt",
"From": "Fra",
"To": "Til",
"Eldorado connection": "Eldorado-forbindelse",
"ago": "siden",
"Reviews per order": "Anmeldelser pr. ordre",
"of": "af",
"We have avoided paying": "Vi har sluppet for at betale",
"of profit": "af profit",
"this month": "denne måned",
"rough rate": "omtrentlig kurs",
"Lasts about": "Rækker til ca.",
"hours": "timer",
"days": "dage",
"per day": "pr. dag",
"No sales in the last 7 days": "Ingen salg de seneste 7 dage",
"Connected": "Forbundet",
"Error": "Fejl",
"Waiting for first fetch": "Venter på første hentning",
"Not updated lately": "Ikke opdateret for nylig",
"Last fetched": "Sidst hentet",
"Problem": "Problem",
"Check": "Tjek",
"The dashboard tries again automatically.": "Dashboardet prøver igen automatisk.",
"mentioned you": "nævnte dig",
"today's rates": "dagens kurser",
"rough rates": "omtrentlige kurser",
"None": "Ingen",
"Dots": "Prikker",
"Grid": "Gitter",
"Waves": "Bølger",
"Aurora": "Nordlys",
"Diagonal": "Diagonal",
"History": "Historik",
"Removed": "Fratrukket",
"Added today": "Tilføjet i dag",
"Removed today": "Fratrukket i dag",
"Net this month": "Netto denne måned",
"Balance now": "Saldo nu",
"Balance": "Saldo",
"Cancelled": "Annulleret",
"Show more": "Vis flere",
"Orders from before the history started are shown as added. Cancelled orders only show from when the history started.": "Ordrer fra før historikken startede vises som tilføjet. Annullerede ordrer vises kun fra det tidspunkt, historikken startede.",
"Big update": "Stor opdatering",
"More tools": "Flere værktøjer"
};

const $=id=>document.getElementById(id);
const qs=(s,r)=>(r||document).querySelector(s),qsa=(s,r)=>[...(r||document).querySelectorAll(s)];
const esc=s=>String(s==null?"":s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const lsGet=(k,def)=>{try{const v=localStorage.getItem(k);return v===null?def:v;}catch(e){return def;}};
const lsSet=(k,v)=>{try{localStorage.setItem(k,v);}catch(e){}};
const SHOP=qs(".brand span").textContent;
const VERSION="2026-10-27";

// ---------- language ----------
let LANG=lsGet("lang","")||((navigator.language||"").toLowerCase().startsWith("da")?"da":"en");
const t=s=>(LANG==="da"&&Object.prototype.hasOwnProperty.call(DA,s))?DA[s]:s;
const LOC=()=>LANG==="da"?"da-DK":"en-GB";
const DAPL={order:["ordre","ordrer"],key:["key","keys"],offer:["tilbud","tilbud"],unit:["enhed","enheder"],review:["anmeldelse","anmeldelser"],device:["enhed","enheder"],day:["dag","dage"],event:["hændelse","hændelser"]};
const plural=(n,w)=>LANG==="da"?n+" "+(DAPL[w]||[w,w+"s"])[n===1?0:1]:n+" "+w+(n===1?"":"s");
const fmt=(n,d=2)=>Number(n).toLocaleString(LOC(),{minimumFractionDigits:d,maximumFractionDigits:d});
const tm=iso=>new Date(iso).toLocaleTimeString(LOC(),{hour:"2-digit",minute:"2-digit"});
const full=iso=>iso?new Date(iso).toLocaleString(LOC()):"";
function ago(iso){const s=Math.max(0,(Date.now()-new Date(iso))/1000);
 if(s<60)return t("just now");if(s<3600)return Math.floor(s/60)+" "+t("min ago");if(s<86400)return Math.floor(s/3600)+" "+t("h ago");
 return new Date(iso).toLocaleDateString(LOC(),{day:"numeric",month:"short"});}
function waited(iso){const m=Math.max(0,Math.floor((Date.now()-new Date(iso))/60000));
 if(m<60)return m+" min";const h=Math.floor(m/60);if(h<48)return h+" h "+(m%60)+" min";return plural(Math.floor(h/24),"day");}
const monthLabel=(key,short)=>{const [y,m]=key.split("-").map(Number);return new Date(y,m-1,1).toLocaleDateString(LOC(),short?{month:"short"}:{month:"long",year:"numeric"});};
const dayLabel2=key=>{const [y,m,d]=key.split("-").map(Number);return new Date(y,m-1,d).toLocaleDateString(LOC(),{weekday:"short",day:"numeric",month:"short",year:"numeric"});};
const weekLabel=k=>t("Week")+" "+Number((k||"").split("W")[1]||0);

// ---------- settings (kept on the server per user, mirrored in this browser) ----------
let PREFS={lang:"",accent:"",currency:"",sound:"ding",gross:null,tax:37,emoji:"",color:"",bg:"",hide:[],notify:{warroom:true,orders:false,reviews:true,keys:true}};
const hid=k=>(PREFS.hide||[]).includes(k);
const BGS=[["","None"],["dots","Dots"],["grid","Grid"],["waves","Waves"],["aurora","Aurora"],["diagonal","Diagonal"]];
function applyBg(){document.body.dataset.bg=PREFS.bg||"";lsSet("bg",PREFS.bg||"");}
let GROSS=lsGet("gross","0")==="1",HIDE=lsGet("hide","0")==="1",CURSEL=lsGet("cur","");
let MAIN="USD",RATES={},RATES_LIVE=false,RATES_DATE=null,isAdmin=false,prefsApplied=false,saveTimer=null;
const post=(url,body,method)=>fetch(url,{method:method||"POST",headers:{"X-Requested-With":"dashboard","Content-Type":"application/json"},body:body?JSON.stringify(body):undefined});
function syncLocal(){lsSet("lang",PREFS.lang||LANG);lsSet("accent",PREFS.accent);lsSet("cur",PREFS.currency);lsSet("sound",PREFS.sound);}
function savePrefs(){clearTimeout(saveTimer);saveTimer=setTimeout(()=>{post("/api/prefs",PREFS,"PUT").catch(()=>{});},300);}
function applyServerPrefs(p){
 if(!p)return;let push=false;
 PREFS.sound=p.sound||"ding";PREFS.notify={...PREFS.notify,...(p.notify||{})};
 for(const k of ["lang","accent","currency"]){
  const local=k==="currency"?lsGet("cur",""):lsGet(k,"");
  if(p[k])PREFS[k]=p[k];else if(local&&k!=="lang"){PREFS[k]=local;push=true;}else PREFS[k]=k==="lang"?LANG:"";
 }
 PREFS.tax=p.tax==null?37:p.tax;PREFS.emoji=p.emoji||"";PREFS.color=p.color||"";PREFS.bg=p.bg||"";PREFS.hide=p.hide||[];
 if(p.gross===null||p.gross===undefined){PREFS.gross=GROSS;push=true;}else{PREFS.gross=!!p.gross;GROSS=PREFS.gross;lsSet("gross",GROSS?"1":"0");}
 applyBg();
 if(!p.lang)push=true;
 LANG=PREFS.lang||LANG;CURSEL=PREFS.currency;syncLocal();applyAccent();
 if(push)savePrefs();
}

// ---------- accent colour ----------
const ACCENTS=[["","",""],["#60a5fa","#2563eb","Blue"],["#a78bfa","#7c3aed","Purple"],["#f472b6","#db2777","Pink"],["#fb923c","#ea580c","Orange"],["#f87171","#dc2626","Red"],["#2dd4bf","#0d9488","Teal"],["#fbbf24","#b45309","Yellow"]];
const isLight=()=>document.documentElement.dataset.theme==="light";
function lum(hex){const n=parseInt(hex.slice(1),16);return (0.299*(n>>16)+0.587*((n>>8)&255)+0.114*(n&255))/255;}
function applyAccent(){
 const r=document.documentElement.style;let hex=PREFS.accent;
 if(!hex){["--accent","--accent2","--accentbg","--onaccent"].forEach(k=>r.removeProperty(k));return;}
 const pre=ACCENTS.find(a=>a[0]===hex||a[1]===hex);if(pre)hex=isLight()?pre[1]:pre[0];
 r.setProperty("--accent",hex);r.setProperty("--accent2","color-mix(in srgb,"+hex+" 60%,var(--panel))");
 r.setProperty("--accentbg","color-mix(in srgb,"+hex+" 14%,transparent)");r.setProperty("--onaccent",lum(hex)>.55?"#0b0d12":"#ffffff");
}

// ---------- amounts: currency, gross/net, hide ----------
const shownCur=()=>{const c=CURSEL||MAIN;return RATES[c]?c:MAIN;};
function money(a,c,d=2){c=c||MAIN;const to=shownCur(),rf=RATES[c],rt=RATES[to];
 if(!rf||!rt||c===to)return fmt(a,d)+" "+esc(c);return fmt(Number(a)/rf*rt,d)+" "+esc(to);}
const mv=a=>{const rt=RATES[shownCur()],rf=RATES[MAIN]||1;return rt?Number(a)/rf*rt:Number(a);};   // main currency -> shown currency
const amtOf=o=>GROSS&&o.gross!=null?o.gross:o.amount;
const dayAmt=x=>GROSS?x.g:x.a;
const ordAmt=o=>GROSS?o.price.amount:o.net;
const feeNote=()=>GROSS?t("before fees"):t("after fees");
const reduceMotion=()=>window.matchMedia&&matchMedia("(prefers-reduced-motion: reduce)").matches;
const CU={};
const cuHtml=(key,v,d=2)=>`<span class="cu" data-k="${key}" data-v="${v}" data-d="${d}">${fmt(v,d)}</span>`;
function runCountUps(root){
 qsa(".cu",root).forEach(el=>{const k=el.dataset.k,to=+el.dataset.v,d=+el.dataset.d,from=CU[k]===undefined?0:CU[k];CU[k]=to;
  if(from===to||reduceMotion()||HIDE){el.textContent=fmt(to,d);return;}
  const t0=performance.now(),dur=550;
  const step=now=>{const p=Math.min(1,(now-t0)/dur),e=1-Math.pow(1-p,3);el.textContent=fmt(from+(to-from)*e,d);if(p<1&&el.isConnected)requestAnimationFrame(step);else el.textContent=fmt(to,d);};
  el.textContent=fmt(from,d);requestAnimationFrame(step);});
}
const stateName=s=>({Paid:t("Paid"),Delivered:t("Delivered"),Received:t("Received"),Completed:t("Completed")}[s]||s||"");
const stClass=s=>({Paid:"warn",Delivered:"",Received:"good",Completed:"good"}[s]||"");

// ---------- small helpers ----------
const ORD={};
const remember=list=>(list||[]).forEach(o=>{ORD[o.id]=o;});
function toast(title,body,onclick){
 const box=$("toasts"),el=document.createElement("div");el.className="toast2";
 el.innerHTML=`<b>${esc(title)}</b>${body?`<span>${esc(body)}</span>`:""}`;
 el.onclick=()=>{el.remove();if(onclick)onclick();};box.appendChild(el);setTimeout(()=>el.remove(),7000);
 while(box.children.length>4)box.firstChild.remove();
}
function copyText(text,btn){
 const done=()=>{if(!btn)return;const o=btn.dataset.o||btn.textContent;btn.dataset.o=o;btn.textContent=t("Copied");setTimeout(()=>{btn.textContent=o;},1300);};
 try{if(navigator.clipboard&&window.isSecureContext){navigator.clipboard.writeText(text).then(done,()=>fb());return;}}catch(e){}
 fb();
 function fb(){const ta=document.createElement("textarea");ta.value=text;ta.style.cssText="position:fixed;opacity:0;top:0";document.body.appendChild(ta);ta.select();try{document.execCommand("copy");}catch(e){}ta.remove();done();}
}

// ---------- pages ----------
const PAGES=["overview","sales","history","orders","stock","reviews","keys","warroom","mindmap","profit","users","settings","news"];
const ADMIN_PAGES=["warroom","mindmap","profit","users"];
const TITLES={overview:"Overview",sales:"Sales",history:"History",orders:"Orders",stock:"Stock",reviews:"Reviews",keys:"Keys",warroom:"War-Room",mindmap:"Mindmap",profit:"Profit",users:"Users",settings:"Settings",news:"What's new"};
const page=()=>{const h=(location.hash||"#overview").slice(1);return PAGES.includes(h)?h:"overview";};
const seen={};
function once(name,key,fn){const k=JSON.stringify(key)+"|"+Math.floor(Date.now()/60000);if(seen[name]===k)return;seen[name]=k;fn();}


// ================= overview =================
function recBadge(rec){return rec?`<span class="rec">${t("New record!")}</span>`:"";}
function welcome(d){
 const h=new Date().getHours(),s=d.sales,td=s.today;
 const hi=h<5?t("Good night"):h<11?t("Good morning"):h<18?t("Hello"):t("Good evening");
 const todayStr=new Date().toDateString();
 const revs=d.reviews.items.filter(r=>new Date(r.time).toDateString()===todayStr),bad=revs.filter(r=>r.rating==="Negative").length;
 const parts=[`${plural(td.orders,"order")} ${t("today")}${td.orders?" ("+money(amtOf(td),s.currency)+")":""}`];
 if(revs.length)parts.push(`${plural(revs.length,"review")} ${t("today")}${bad?" · "+bad+" "+t("bad"):""}`);
 if(d.pending.n)parts.push(`${d.pending.n} ${t("waiting to be completed")}`);
 if(d.keys.left<=10)parts.push(`<span style="color:var(--amber)">${d.keys.left===0?t("Out of keys"):plural(d.keys.left,"key")+" "+t("left")}</span>`);
 const r=s.records,badges=[r.day.record?t("Best day ever!"):"",r.week.record?t("Best week ever!"):"",r.month.record?t("Best month ever!"):""].filter(Boolean);
 $("welcome").innerHTML=`<div><b>${hi}, ${esc(d.user.name)}!</b><div class="w2">${parts.join(" · ")}</div></div><div class="mini2">${badges.map(b=>`<span class="rec">${b}</span>`).join("")}</div>`;
}
function tiles(d){
 const s=d.sales,cur=esc(shownCur()),r=s.records;
 const tile0=(l,key,v,sub,extra)=>`<div class="tile"><div class="l">${l} ${extra||""}</div><div class="v">${cuHtml(key,mv(v))} <small>${cur}</small></div><div class="s">${sub}</div></div>`;
 const other=o=>s.fee_percent?` · ${GROSS?t("net"):t("gross")} ${fmt(mv(GROSS?o.amount:o.gross))}`:"";
 const avg=o=>o.orders?amtOf(o)/o.orders:0;
 const tile=(id,...a)=>hid(id)?"":tile0(...a);
 let h=tile("today",t("Today"),"t-today",amtOf(s.today),plural(s.today.orders,"order")+other(s.today),recBadge(r.day.record))
  +tile("month",t("This month"),"t-month",amtOf(s.month),plural(s.month.orders,"order")+other(s.month),recBadge(r.month.record))
  +tile("all",t("All time"),"t-all",amtOf(s.all),plural(s.all.orders,"order")+other(s.all))
  +tile("avg",t("Average order"),"t-avg",avg(s.all),t("Today")+": "+(s.today.orders?fmt(mv(avg(s.today))):"-")+" "+cur)
  +(hid("stock")?"":`<div class="tile"><div class="l">${t("In stock")}</div><div class="v">${cuHtml("t-stock",d.stock.units,0)} <small>${t("units")}</small></div><div class="s">${plural(d.stock.offers.length,"offer")}</div></div>`);
 if(d.profit)h+=tile("profit",t("Profit this month"),"t-profit",d.profit.month,t("All time")+": "+fmt(mv(d.profit.all))+" "+cur);
 if(!hid("lastorder")){const lo=d.orders[0],mins=lo?(Date.now()-new Date(lo.time))/6e4:0,cls=!lo?"":mins>360?"bad":mins>120?"warn":"";
  h+=`<div class="tile"><div class="l">${t("Latest order")}</div><div class="v ${cls}">${lo?esc(waited(lo.time)):"-"}${lo?` <small>${t("ago")}</small>`:""}</div><div class="s">${lo?esc(lo.buyer)+" · "+esc(tm(lo.time)):t("No orders yet.")}</div></div>`;}
 if(!hid("revrate")){const rv=d.reviews,tot=rv.positive+rv.negative,n=s.all.orders,pc=n?Math.min(100,tot*100/n):null;
  h+=`<div class="tile"><div class="l">${t("Reviews per order")}</div><div class="v">${pc===null?"-":fmt(pc,0)} <small>%</small></div><div class="s">${plural(tot,"review")} ${t("of")} ${plural(n,"order")}</div></div>`;}
 s.others.forEach(o=>{h+=`<div class="tile"><div class="l">${esc(o.currency)} (${t("all time")})</div><div class="v">${fmt(o.all.amount)} <small>${esc(o.currency)}</small></div><div class="s">${plural(o.all.orders,"order")}</div></div>`;});
 $("tiles").innerHTML=h;runCountUps($("tiles"));
}
function taxpot(d){
 const el=$("taxpot");if(!isAdmin||!d.profit||hid("taxpot")){el.hidden=true;return;}
 const pct=PREFS.tax==null?37:PREFS.tax,all=Math.max(0,d.profit.all_dkk)*pct/100,mo=Math.max(0,d.profit.month_dkk)*pct/100;
 el.hidden=false;
 el.innerHTML=`<span>${t("We have avoided paying")}:</span> <b>${fmt(all,0)} kr.</b><small>${fmt(pct,pct%1?1:0)}% ${t("of profit")} · ${t("this month")}: ${fmt(mo,0)} kr.${d.profit.dkk_live?"":" · "+t("rough rate")}</small>`;
}
function fcText(k){
 const f=k.forecast;if(!k.left)return "";
 if(!f||f.days===null)return t("No sales in the last 7 days");
 const x=f.days<1?fmt(f.days*24,0)+" "+t("hours"):fmt(f.days,1)+" "+t("days");
 return t("Lasts about")+" "+x+" · "+fmt(f.per_day,1)+" "+t("per day");
}
function statusPanel(d){
 const st=d.status||{},nm={orders:t("Orders"),stock:t("Stock"),reviews:t("Reviews")};let bad=0,warn=0;
 const rows=["orders","stock","reviews"].map(k=>{const s=st[k]||{},age=s.ok?(Date.now()-new Date(s.ok))/1000:null;let cls="good",txt=t("Connected");
  if(s.fails>0){cls="bad";bad++;txt=t("Error")+(s.err?": "+s.err:"");}
  else if(age===null){cls="warn";warn++;txt=t("Waiting for first fetch");}
  else if(age>300){cls="warn";warn++;txt=t("Not updated lately");}
  return `<div class="statrow"><div>${esc(nm[k])}<small class="muted">${s.ok?t("Last fetched")+" "+esc(ago(s.ok)):"-"}</small></div><span class="pill ${cls}">${esc(txt)}</span></div>`;}).join("");
 $("statsum").innerHTML=bad?`<span class="pill bad">${t("Problem")}</span>`:warn?`<span class="pill warn">${t("Check")}</span>`:`<span class="pill good">OK</span>`;
 $("statbox").innerHTML=rows+(bad?`<div class="muted" style="font-size:12.5px;padding-top:8px">${t("The dashboard tries again automatically.")}</div>`:"");
}
function applyHides(){
 [["chart1","chart"],["latest","latest"],["pend","pending"]].forEach(([id,k])=>{const p=$(id).closest(".panel");if(p)p.style.display=hid(k)?"none":"";});
}
function niceStep(peak){for(const s of [5,10,20,25,50,100,200,250,500,1000,2000,2500,5000,10000,20000,50000]) if(peak/s<=4)return s;return 100000;}
function chart(d,boxId,count){
 const box=$(boxId);if(!box||!box.clientWidth)return;
 const c=shownCur();let m=d.sales.months.slice(-count).map(x=>({...x,v:mv(GROSS?x.gross:x.amount),label:monthLabel(x.key),short:monthLabel(x.key,true)}));
 const cw=Math.max(260,Math.floor(box.clientWidth)),small=cw<520;if(small)m=m.slice(-6);
 const W=cw,H=small?220:260,L=small?40:46,R=8,T=18,B=28,iw=W-L-R,ih=H-T-B,n=m.length;
 const peak=Math.max(1,...m.map(x=>x.v)),step=niceStep(peak),top=Math.max(step,Math.ceil(peak*1.1/step)*step);
 const y=v=>T+ih-(v/top)*ih,bw=Math.min(small?34:count>6?30:46,iw/n*0.52),best=m.reduce((b,x,i)=>x.v>m[b].v?i:b,0);
 let g="";
 for(let v=0;v<=top;v+=step){g+=`<line class="gl" x1="${L}" x2="${W-R}" y1="${y(v)}" y2="${y(v)}" opacity="${v?1:0}"/><text class="tx" x="${L-8}" y="${y(v)+4}" text-anchor="end">${fmt(v,0)}</text>`;}
 g+=`<line class="gl" x1="${L}" x2="${W-R}" y1="${T+ih}" y2="${T+ih}"/>`;
 m.forEach((x,i)=>{
  const cx=L+iw/n*(i+.5),x0=cx-bw/2,h=Math.max(0,(x.v/top)*ih),last=i===n-1,r=Math.min(6,h/2);
  if(x.v>0){const yt=y(x.v);
   g+=`<path class="bar${last?" cur":""}" d="M${x0},${T+ih}L${x0},${yt+r}Q${x0},${yt} ${x0+r},${yt}L${x0+bw-r},${yt}Q${x0+bw},${yt} ${x0+bw},${yt+r}L${x0+bw},${T+ih}Z"/>`;
   if(last||i===best){const lab=fmt(x.v,0)+" "+c,w=lab.length*7.4,edge=cx+w/2>W-R,left=cx-w/2<L-6;
    g+=`<text class="val" x="${edge?W-R:left?L-6:cx}" y="${yt-7}" text-anchor="${edge?"end":left?"start":"middle"}">${esc(lab)}</text>`;}}
  g+=`<text class="tx" x="${cx}" y="${H-8}" text-anchor="middle">${esc(x.short)}</text>`;
  g+=`<rect class="hit" data-i="${i}" x="${cx-iw/n/2}" y="${T}" width="${iw/n}" height="${ih}" fill="transparent"/>`;
 });
 box.innerHTML=`<svg class="ch" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" role="img" aria-label="${esc(t("Sales per month"))}">${g}</svg><div class="tip"></div>`;
 const tip=box.querySelector(".tip");
 const show=(el,e)=>{const x=m[+el.dataset.i],b=box.getBoundingClientRect();
  tip.textContent=`${x.label} · ${fmt(x.v)} ${c} · ${plural(x.orders,"order")}`;
  tip.style.left=Math.min(Math.max(e.clientX-b.left,90),b.width-90)+"px";tip.style.top=Math.max(24,e.clientY-b.top-10)+"px";tip.style.opacity=1;};
 box.querySelectorAll(".hit").forEach(el=>{
  el.addEventListener("pointermove",e=>{if(e.pointerType==="mouse")show(el,e);});
  el.addEventListener("pointerdown",e=>show(el,e));
  el.addEventListener("pointerleave",e=>{if(e.pointerType==="mouse")tip.style.opacity=0;});
 });
}
document.addEventListener("pointerdown",e=>{document.querySelectorAll(".tip").forEach(t=>{if(!t.parentNode.contains(e.target))t.style.opacity=0;});});
function latest(d){
 remember(d.orders);
 $("latest").innerHTML=d.orders.length?d.orders.slice(0,5).map(o=>`<div class="row2 click" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item)}<small>${esc(o.buyer)} · ${esc(ago(o.time))}</small></div><div class="e mono">${money(ordAmt(o),o.price.currency)}</div></div>`).join(""):`<div class="empty">${t("No orders yet.")}</div>`;
}
function pendHtml(d,limit){
 const p=d.pending;remember(p.rows);
 if(!p.n)return `<div class="empty">${t("Nothing is waiting. All orders are completed.")}</div>`;
 return p.rows.slice(0,limit||8).map(o=>`<div class="row2" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item)}<small>${esc(o.buyer)} · ${t("waiting")} ${esc(waited(o.time))}</small></div><div class="e"><div class="mono">${money(ordAmt(o),o.price.currency)}</div><span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span></div></div>`).join("")
  +(p.n>(limit||8)?`<div class="muted" style="padding-top:8px">+ ${p.n-(limit||8)} ${t("more")}</div>`:"");
}
function pending(d){
 $("pend").innerHTML=pendHtml(d,5);
}
function mini(d){
 const r=d.reviews,tot=r.positive+r.negative,pct=tot?Math.round(r.positive*100/tot):null,k=d.keys,low=k.left<=10;
 const lowStock=d.stock.offers.filter(o=>o.quantity<=5).length;
 $("mini").innerHTML=
  (hid("reviews")?"":`<div class="panel"><h2>${t("Reviews")} <a href="#reviews">${t("Open")}</a></h2><div class="big">${pct===null?"-":pct+"%"}</div><div class="muted">${r.positive} ${t("good")} · ${r.negative} ${t("bad")}</div></div>`)
  +(hid("keys")?"":`<div class="panel"><h2>${t("Keys left")} <a href="#keys">${t("Open")}</a></h2><div class="big">${fmt(k.left,0)}</div><div style="margin-top:4px">${low?`<span class="pill ${k.left===0?"bad":"warn"}">${k.left===0?t("Out of keys"):t("Running low")}</span>`:`<span class="muted">${fmt(k.used,0)} ${t("used so far")}</span>`}</div><div class="muted" style="font-size:12.5px;margin-top:6px">${fcText(k)}</div></div>`)
  +`<div class="panel"><h2>${t("Stock")} <a href="#stock">${t("Open")}</a></h2><div class="big">${fmt(d.stock.units,0)}</div><div style="margin-top:4px">${lowStock?`<span class="pill warn">${plural(lowStock,"offer")} ${t("low")}</span>`:`<span class="muted">${t("All offers stocked")}</span>`}</div></div>`;
}

// ================= sales =================
let calMonth=null,selDay=null;
function salesTiles(d){
 const s=d.sales,r=s.records,cur=esc(shownCur());
 const avg=o=>o.orders?amtOf(o)/o.orders:0;
 const bd=r.day.key?s.days[r.day.key]:null;
 $("stiles").innerHTML=
  `<div class="tile"><div class="l">${t("Average order")}</div><div class="v">${cuHtml("s-avg",mv(avg(s.all)))} <small>${cur}</small></div><div class="s">${t("This month")}: ${s.month.orders?fmt(mv(avg(s.month))):"-"} ${cur}</div></div>`
  +`<div class="tile"><div class="l">${t("Best day ever")} ${recBadge(r.day.record)}</div><div class="v">${cuHtml("s-best",mv(bd?dayAmt(bd):0))} <small>${cur}</small></div><div class="s">${r.day.key?esc(dayLabel2(r.day.key)):"-"}${r.day.orders?" · "+plural(r.day.orders,"order"):""}</div></div>`
  +`<div class="tile"><div class="l">${t("Orders this month")}</div><div class="v">${cuHtml("s-ords",s.month.orders,0)}</div><div class="s">${t("All time")}: ${fmt(s.all.orders,0)}</div></div>`;
 runCountUps($("stiles"));
}
function records(d){
 const r=d.sales.records,cur=shownCur();
 const row=(l,sub,x)=>`<div class="r1"><div>${l}<small>${sub}</small></div><div class="v">${x.key?fmt(mv(x.amount))+" "+esc(cur):"-"} ${recBadge(x.record)}</div></div>`;
 $("recs").innerHTML=row(t("Best day"),r.day.key?esc(dayLabel2(r.day.key)):"",r.day)+row(t("Best week"),r.week.key?esc(weekLabel(r.week.key)+" · "+r.week.key.slice(0,4)):"",r.week)+row(t("Best month"),r.month.key?esc(monthLabel(r.month.key)):"",r.month)
  +`<div class="muted" style="font-size:12px;padding-top:8px">${t("Records are counted after fees.")}</div>`;
}
const wdNames=()=>[...Array(7)].map((_,i)=>new Date(2024,0,1+i).toLocaleDateString(LOC(),{weekday:"short"}));
function calendar(d){
 const s=d.sales,days=s.days,cur=s.date.slice(0,7);
 if(!calMonth)calMonth=cur;
 const [y,m]=calMonth.split("-").map(Number),first=(new Date(y,m-1,1).getDay()+6)%7,dim=new Date(y,m,0).getDate();
 const keys=Object.keys(days).sort(),minM=(keys[0]||s.date).slice(0,7);
 $("calprev").disabled=calMonth<=minM;$("calnext").disabled=calMonth>=cur;
 $("calttl").textContent=monthLabel(calMonth);
 let max=0,sum=0,cnt=0;
 for(let i=1;i<=dim;i++){const k=calMonth+"-"+String(i).padStart(2,"0"),x=days[k];if(x){max=Math.max(max,dayAmt(x));sum+=dayAmt(x);cnt+=x.n;}}
 $("calsum").textContent=fmt(mv(sum))+" "+shownCur()+" · "+plural(cnt,"order");
 let h=wdNames().map(w=>`<div class="dh">${esc(w)}</div>`).join("");
 for(let i=0;i<first;i++)h+=`<div class="cd off"></div>`;
 for(let i=1;i<=dim;i++){const k=calMonth+"-"+String(i).padStart(2,"0"),x=days[k],a=x?dayAmt(x):0;
  const cls=["cd",k===s.date?"today":"",k===selDay?"sel":"",s.records.day.key===k?"best":""].join(" ");
  h+=`<button class="${cls}" data-day="${k}" style="--lv:${max?(a/max).toFixed(2):0}" aria-label="${esc(dayLabel2(k))}"><i>${i}</i><b>${x?fmt(mv(a),0):""}</b><s>${x?x.n:""}</s></button>`;}
 $("cal").innerHTML=h;
}
async function loadDay(date){
 selDay=date;$("daydate").textContent=dayLabel2(date);qsa("#cal .cd").forEach(b=>b.classList.toggle("sel",b.dataset.day===date));
 const x=window.__last&&window.__last.sales.days[date];
 $("dayd").innerHTML=`<div class="sk line"></div><div class="sk line"></div>`;
 try{const r=await fetch("/api/day/"+date);const j=await r.json();if(selDay!==date)return;remember(j.orders);
  const cur=window.__last.sales.currency,rows=j.orders;
  const sum=x?`<div class="rows"><div class="r1"><div>${t("Orders")}</div><div class="v">${x.n}</div></div>
   <div class="r1"><div>${t("Sales")} <small>${t("after fees")}</small></div><div class="v">${money(x.a,cur)}</div></div>
   <div class="r1"><div>${t("Before fees")}</div><div class="v">${money(x.g,cur)}</div></div>
   <div class="r1"><div>${t("Eldorado fees")}</div><div class="v">${money(x.g-x.a,cur)}</div></div>
   <div class="r1"><div>${t("Average order")}</div><div class="v">${money((GROSS?x.g:x.a)/x.n,cur)}</div></div></div>`:`<div class="empty">${t("No sales this day.")}</div>`;
  $("dayd").innerHTML=sum+(rows.length?`<div style="margin-top:12px">${rows.map(o=>`<div class="row2" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item||"?")}<small>${esc(o.buyer||"?")}${o.time?" · "+esc(tm(o.time)):""}</small></div><div class="e mono">${money(ordAmt(o),o.price.currency)}</div></div>`).join("")}</div>`:"");
 }catch(e){$("dayd").innerHTML=`<div class="empty">${t("Could not load.")}</div>`;}
}
function fees(d){
 const s=d.sales;
 if(!s.fee_percent){$("fees").innerHTML=`<div class="empty">${t("No fee is set up, so net and gross are the same.")}</div>`;return;}
 const row=(l,o)=>`<div class="r1"><div>${l}<small>${plural(o.orders,"order")}</small></div><div class="v">${money(o.gross-o.amount,s.currency)}</div></div>`;
 $("fees").innerHTML=row(t("Today"),s.today)+row(t("This month"),s.month)+row(t("All time"),s.all)
  +`<div class="muted" style="font-size:12.5px;padding-top:10px">${t("Eldorado keeps about")} ${s.fee_percent}% ${t("of every order (rounded up to the cent). You keep")} ${s.all.gross?fmt(s.all.amount*100/s.all.gross,1):"-"}% ${t("of what buyers paid.")}</div>`;
}
function months(d){
 const rows=[...d.sales.months].reverse().filter((x,i)=>x.orders>0||i<3),c=d.sales.currency;
 $("months").innerHTML=`<table><thead><tr><th>${t("Month")}</th><th class="r">${t("Sales")}</th><th class="r">${t("Fees")}</th><th class="r">${t("Orders")}</th></tr></thead><tbody>${
  rows.map(x=>`<tr><td>${esc(monthLabel(x.key))}</td><td class="r mono">${money(GROSS?x.gross:x.amount,c)}</td><td class="r mono muted">${money(x.gross-x.amount,c)}</td><td class="r muted">${x.orders}</td></tr>`).join("")}</tbody></table>`;
}

// ================= stock / reviews / keys =================
function stock(d){
 $("stocksum").textContent=fmt(d.stock.units,0)+" "+t("units");
 $("stock").innerHTML=d.stock.offers.length?d.stock.offers.map(o=>{const w=Math.min(100,o.quantity);
  return `<div class="row2"><div class="t">${esc(o.title)}<small>${esc(o.category)}</small><div class="qbar ${o.quantity<=5?"warn":""}"><i style="width:${w}%"></i></div></div>
  <div class="e"><div class="mono">${money(o.price.amount,o.price.currency)}</div><span class="pill ${o.quantity<=5?"warn":""}">${fmt(o.quantity,0)} ${t("in stock")}</span></div></div>`;}).join(""):`<div class="empty">${t("Nothing in stock right now.")}</div>`;
}
let RV="all";
function reviews(d){
 const r=d.reviews,tot=r.positive+r.negative,pct=tot?Math.round(r.positive*100/tot):null;
 $("revsum").innerHTML=`<div><div class="big">${pct===null?"-":pct+"%"}</div><small>${t("positive")}</small></div><div><div class="big" style="color:var(--accent)">${r.positive}</div><small>${t("good")}</small></div><div><div class="big" style="color:var(--red)">${r.negative}</div><small>${t("bad")}</small></div>`;
 const items=r.items.filter(x=>RV==="all"||(RV==="good"?x.rating==="Positive":x.rating==="Negative"));
 $("rvnote").textContent=items.length?plural(items.length,"review"):"";
 $("reviews").innerHTML=items.length?items.map(x=>{const good=x.rating==="Positive",isNew=Date.now()-new Date(x.time)<864e5;
  return `<div class="rev"><div class="m"><span class="pill ${good?"good":"bad"}">${good?t("Good review"):t("Bad review")}</span>${isNew?`<span class="pill warn">${t("New")}</span>`:""}
   <b${good?"":' style="font-size:15px"'}><button class="lnk" data-buyer="${esc(x.buyer)}">${esc(x.buyer)}</button></b><span class="muted" title="${esc(full(x.time))}">${esc(ago(x.time))}</span></div>
  <div class="q">${x.text?esc(x.text):'<span class="muted">'+t("No written message")+'</span>'}</div>${x.tags.length?`<div class="muted" style="margin-top:6px;font-size:12.5px">${x.tags.map(esc).join(" · ")}</div>`:""}
  ${good?"":`<div class="mini2" style="margin-top:10px"><button class="btn copy" data-copy="${esc(x.buyer)}">${t("Copy name")}</button>${x.order_id?`<button class="btn copy" data-copy="${esc(x.order_id)}">${t("Copy order ID")}</button>`:""}</div>
  <div class="muted" style="font-size:12px;margin-top:6px">${t("To write to them: find this order on Eldorado with the order ID.")}</div>`}</div>`;}).join(""):`<div class="empty">${RV==="bad"?t("No bad reviews. Nice."):t("No reviews yet.")}</div>`;
}
function keys(d){
 $("addkeys").style.display=isAdmin?"":"none";$("findkey").style.display=isAdmin?"":"none";
 const k=d.keys,low=k.left<=10;
 $("keyshead").innerHTML=`<div class="big">${fmt(k.left,0)}</div><div style="margin-top:6px">${low?`<span class="pill ${k.left===0?"bad":"warn"}">${k.left===0?t("Out of keys"):t("Running low")}</span> `:""}<span class="muted">${fmt(k.used,0)} ${t("keys used so far")}</span></div>`;
 if(fcText(k))$("keyshead").insertAdjacentHTML("beforeend",`<div class="muted" style="margin-top:8px">${fcText(k)}</div>`);
 $("keys").innerHTML=k.refills.length?`<table><thead><tr><th>${t("When")}</th><th>${t("Added")}</th><th class="r">${t("Stock")}</th></tr></thead><tbody>${
  k.refills.map(x=>`<tr><td class="muted" title="${esc(full(x.time))}">${esc(ago(x.time))}</td><td>+${esc(x.added)}</td><td class="r mono">${esc(x.before)} → ${esc(x.after)}</td></tr>`).join("")}</tbody></table>`
  :`<div class="empty">${t("No refills logged yet.")}</div>`;
}

// ================= render =================
const KNOWN={orders:null,neg:null,keys:null};
function detectEvents(d){
 if(!isAdmin)return;
 const n=PREFS.notify;
 if(KNOWN.orders){d.orders.filter(o=>!KNOWN.orders.has(o.id)&&Date.now()-new Date(o.time)<72e5).forEach(o=>{
   if(n.orders){ding();toast(t("New order"),money(ordAmt(o),o.price.currency)+" · "+o.buyer,()=>openOrder(o.id));}});}
 KNOWN.orders=new Set(d.orders.map(o=>o.id));
 const neg=d.reviews.items.filter(r=>r.rating==="Negative"),sig=r=>r.order_id+"|"+r.time;
 if(KNOWN.neg){neg.filter(r=>!KNOWN.neg.has(sig(r))).forEach(r=>{if(n.reviews){ding();toast(t("Bad review"),r.buyer+(r.text?": "+r.text.slice(0,80):""),()=>{location.hash="#reviews";});}});}
 KNOWN.neg=new Set(neg.map(sig));
 const ks=d.keys.left===0?"out":d.keys.left<=10?"low":"ok";
 if(KNOWN.keys&&ks!==KNOWN.keys&&ks!=="ok"&&n.keys){ding();toast(ks==="out"?t("Out of keys"):t("Keys running low"),plural(d.keys.left,"key")+" "+t("left"),()=>{location.hash="#keys";});}
 KNOWN.keys=ks;
}
function curUi(){
 const opts=[...(CURRENCIES_ALL().filter((c,i,a)=>a.indexOf(c)===i))];
 const cur=shownCur();
 const sel=$("curSel");
 if(sel.dataset.sig!==opts.join()){sel.innerHTML=opts.map(c=>`<option value="${c}">${c}</option>`).join("");sel.dataset.sig=opts.join();}
 sel.value=cur;
 $("curSeg").innerHTML=opts.map(c=>`<button type="button" data-c="${c}" class="${c===cur?"on":""}">${c}</button>`).join("");
 $("curnote").textContent=cur===MAIN?`${t("Your sales are counted in")} ${MAIN}.`:(RATES_LIVE?`${t("Converted with today's rates")}${RATES_DATE?" ("+RATES_DATE+")":""}. ${t("Eldorado pays out in")} ${MAIN}.`:t("Converted with rough rates (live rates could not be fetched). Eldorado pays out in")+" "+MAIN+".");
}
const CURRENCIES_ALL=()=>[MAIN,"DKK","USD","EUR"];
const K0=()=>[LANG,HIDE];
function render(d){
 isAdmin=d.user.role==="admin";
 ["navusers","navwar","navmind","navprofit"].forEach(id=>{$(id).hidden=!isAdmin;});
 if(ADMIN_PAGES.includes(page())&&!isAdmin){location.hash="#overview";return;}
 MAIN=d.rates.base;RATES=d.rates.rates;RATES_LIVE=d.rates.live;RATES_DATE=d.rates.date;
 if(!prefsApplied){prefsApplied=true;applyServerPrefs(d.prefs);translateStatic();setTitle();settingsUi();}
 const q=$("quote");q.hidden=!d.quote;q.textContent=d.quote||"";
 $("who").textContent=d.user.name;$("role").textContent=t(d.user.role==="admin"?"admin":"viewer");$("av").textContent=d.user.name.slice(0,1);
 curUi();detectEvents(d);newsNav();once("tax",[d.profit,PREFS.tax,PREFS.hide,K0()],()=>taxpot(d));
 const p=page(),K=[GROSS,shownCur(),HIDE,LANG];
 if(p==="overview"){applyHides();once("status",[d.status,K],()=>statusPanel(d));once("welcome",[d.sales,d.reviews,d.pending.n,d.keys.left,K],()=>welcome(d));
  once("tiles",[d.sales,d.stock.units,d.stock.offers.length,d.profit,d.orders[0],d.reviews,PREFS.hide,K],()=>tiles(d));$("cur1").textContent=shownCur()+" · "+feeNote();
  once("c1",[d.sales.months,$("chart1").clientWidth,K],()=>chart(d,"chart1",6));once("latest",[d.orders,K],()=>latest(d));
  once("pend",[d.pending,K],()=>pending(d));once("mini",[d.reviews,d.keys,d.stock,PREFS.hide,K],()=>mini(d));}
 if(p==="sales"){$("cur2").textContent=shownCur()+" · "+feeNote();
  once("stiles",[d.sales,K],()=>salesTiles(d));once("c2",[d.sales.months,$("chart2").clientWidth,K],()=>chart(d,"chart2",12));
  once("recs",[d.sales.records,K],()=>records(d));once("cal",[d.sales.days,calMonth,selDay,K],()=>calendar(d));
  once("fees",[d.sales,K],()=>fees(d));once("months",[d.sales.months,K],()=>months(d));
  if(!selDay){selDay=d.sales.date;loadDay(selDay);}}
 if(p==="orders"){once("opend",[d.pending,K],()=>{$("opend").innerHTML=pendHtml(d,8);$("pendsum").textContent=d.pending.n?plural(d.pending.n,"order")+" · "+money(GROSS?d.pending.gross:d.pending.net,d.pending.currency):"";});}
 if(p==="stock")once("stock",[d.stock,K],()=>stock(d));
 if(p==="reviews")once("reviews",[d.reviews,RV,K],()=>reviews(d));
 if(p==="keys")once("keys",[d.keys,K],()=>keys(d));
 if(p==="profit")once("ptiles",[d.profit,K],()=>{});
 const errs=Object.entries(d.errors||{});
 $("err").style.display=errs.length?"block":"none";
 $("err").textContent=errs.length?t("Some data could not be loaded from Eldorado")+" ("+errs.map(e=>e[0]+": "+e[1]).join(", ")+"). "+t("Showing the last known values."):"";
}
function rerender(){for(const k in seen)delete seen[k];if(window.__last)render(window.__last);pageLoad(true);}


// ================= orders page =================
let OF="all",OQ="",oTimer=null,oBusy=false;
async function loadOrders(){
 if(oBusy)return;oBusy=true;
 try{const r=await fetch("/api/orders?filter="+OF+"&q="+encodeURIComponent(OQ));if(r.status===401){location="/login";return;}
  const j=await r.json();remember(j.orders);
  $("ocount").textContent=(OQ||OF!=="all")?plural(j.matched,"order")+" "+t("found"):plural(j.total,"order")+" "+t("tracked");
  $("orders").innerHTML=j.orders.length?`<table class="stack"><thead><tr><th>${t("Time")}</th><th>${t("Item")}</th><th>${t("Qty")}</th><th>${t("Price")}</th><th>${t("Buyer")}</th><th class="r">${t("Status")}</th></tr></thead><tbody>${
   j.orders.map(o=>`<tr class="click" data-oid="${esc(o.id)}"><td data-label="Time" title="${esc(full(o.time))}" class="muted" style="white-space:nowrap">${esc(ago(o.time))}</td><td data-label="Item">${esc(o.item)}</td><td data-label="Qty">${esc(o.quantity)}</td>
   <td data-label="Price" class="mono" style="white-space:nowrap">${money(ordAmt(o),o.price.currency)}</td><td data-label="Buyer"><button class="lnk" data-buyer="${esc(o.buyer)}">${esc(o.buyer)}</button></td><td data-label="Status" class="r"><span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span></td></tr>`).join("")}</tbody></table>`
   :`<div class="empty">${(OQ||OF!=="all")?t("No orders match."):t("No orders yet.")}</div>`;
 }catch(e){}
 oBusy=false;
}
$("osearch").oninput=e=>{OQ=e.target.value.trim();clearTimeout(oTimer);oTimer=setTimeout(loadOrders,250);};
$("ochips").onclick=e=>{const b=e.target.closest("[data-f]");if(!b)return;OF=b.dataset.f;qsa("#ochips .chip").forEach(c=>c.classList.toggle("on",c===b));loadOrders();};

// ================= drawer: one order, or one buyer =================
let dstack=[];
const drawerIsOpen=()=>$("drawer").classList.contains("on");
function drawerShow(){$("veil").classList.add("on");$("drawer").classList.add("on");$("drawer").setAttribute("aria-hidden","false");}
function drawerClose(){dstack=[];$("veil").classList.remove("on");$("drawer").classList.remove("on");$("drawer").setAttribute("aria-hidden","true");}
function drawerPush(v){if(!drawerIsOpen())dstack=[];dstack.push(v);drawerShow();drawerDraw();}
function drawerDraw(){
 const v=dstack[dstack.length-1];$("dback").hidden=dstack.length<2;if(!v)return;
 if(v.t==="order")orderView(ORD[v.id]);else buyerView(v.name);
 $("dbody").scrollTop=0;
}
const openOrder=id=>{if(ORD[id])drawerPush({t:"order",id});};
const openBuyer=name=>drawerPush({t:"buyer",name});
$("dclose").onclick=drawerClose;$("veil").onclick=drawerClose;
$("dback").onclick=()=>{dstack.pop();drawerDraw();};
document.addEventListener("keydown",e=>{if(e.key==="Escape"&&drawerIsOpen())drawerClose();});
function orderView(o){
 if(!o){$("dbody").innerHTML=`<div class="empty">${t("Could not load.")}</div>`;return;}
 const cur=o.price.currency,idx={Paid:0,Delivered:1,Received:1,Completed:2}[o.state];
 $("dtitle").textContent=o.item||t("Order");
 let h=`<div class="rows">
  <div class="r1"><div>${t("Status")}</div><div class="v">${o.state?`<span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span>`:"-"}</div></div>
  <div class="r1"><div>${t("Price")}<small>${t("before fees")}</small></div><div class="v">${money(o.price.amount,cur)}</div></div>
  <div class="r1"><div>${t("Eldorado fee")}</div><div class="v">${money(o.fee,cur)}</div></div>
  <div class="r1"><div>${t("You keep")}<small>${t("after fees")}</small></div><div class="v">${money(o.net,cur)}</div></div>
  <div class="r1"><div>${t("Quantity")}</div><div class="v">${esc(o.quantity)}</div></div>
  <div class="r1"><div>${t("Buyer")}</div><div class="v"><button class="lnk" data-buyer="${esc(o.buyer)}">${esc(o.buyer)}</button> <button class="btn copy" data-copy="${esc(o.buyer)}">${t("Copy")}</button></div></div>
  <div class="r1"><div>${t("Placed")}</div><div class="v" style="font-weight:500">${esc(full(o.time))}</div></div>
  <div class="r1"><div>${t("Order ID")}<small style="overflow-wrap:anywhere;max-width:230px">${esc(o.id)}</small></div><div class="v"><button class="btn copy" data-copy="${esc(o.id)}">${t("Copy")}</button></div></div></div>`;
 if(idx!==undefined){
  const steps=[["Paid",t("Paid")],["Delivered",t("Delivered")],["Completed",t("Completed")]],log=o.log||{};
  h+=`<h2 style="margin:18px 0 8px;font-size:15px">${t("Timeline")}</h2><ul class="tl">${steps.map(([k,l],i)=>{
   const done=idx>=i;let when=i===0?o.time:(log[k]&&o.first!==k?log[k]:"");
   let sub=when?esc(full(when)):(done?t("time not tracked"):t("not yet"));
   if(i===1&&(o.state==="Received"||log.Received))sub+=" · "+t("buyer confirmed receipt");
   return `<li class="${done?"done":""}">${l}<small>${sub}</small></li>`;}).join("")}</ul>
   <div class="muted" style="font-size:12px">${t("Times after payment are when the dashboard first saw the new status.")}</div>`;}
 $("dbody").innerHTML=h;
}
async function buyerView(name){
 $("dtitle").textContent=name;$("dbody").innerHTML=`<div class="sk line"></div><div class="sk line"></div><div class="sk line"></div>`;
 try{const r=await fetch("/api/buyer?name="+encodeURIComponent(name));const j=await r.json();
  const v=dstack[dstack.length-1];if(!v||v.t!=="buyer"||v.name!==name)return;
  remember(j.orders);
  const first=j.orders.length?j.orders[j.orders.length-1].time:"",last=j.orders.length?j.orders[0].time:"";
  $("dbody").innerHTML=`<div class="rows"><div class="r1"><div>${t("Orders")}</div><div class="v">${j.count}</div></div>
   <div class="r1"><div>${t("Spent")}<small>${feeNote()}</small></div><div class="v">${money(GROSS?j.gross:j.net,j.currency)}</div></div>
   <div class="r1"><div>${t("First order")}</div><div class="v" style="font-weight:500">${first?esc(full(first)):"-"}</div></div>
   <div class="r1"><div>${t("Latest order")}</div><div class="v" style="font-weight:500">${last?esc(full(last)):"-"}</div></div>
   <div class="r1"><div>${t("Name")}</div><div class="v"><button class="btn copy" data-copy="${esc(name)}">${t("Copy name")}</button></div></div></div>
   <h2 style="margin:18px 0 6px;font-size:15px">${t("All orders from this buyer")}</h2>
   ${j.orders.map(o=>`<div class="row2" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item||"?")}<small>${esc(full(o.time))}</small></div><div class="e"><div class="mono">${money(ordAmt(o),o.price.currency)}</div>${o.state?`<span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span>`:""}</div></div>`).join("")||`<div class="empty">${t("No orders found.")}</div>`}
   <div class="muted" style="font-size:12px;margin-top:10px">${t("Only orders the dashboard has seen are listed.")}</div>`;
 }catch(e){$("dbody").innerHTML=`<div class="empty">${t("Could not load.")}</div>`;}
}

// ================= sales page controls =================
$("calprev").onclick=()=>{const [y,m]=calMonth.split("-").map(Number),d=new Date(y,m-2,1);calMonth=d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0");delete seen.cal;render(window.__last);};
$("calnext").onclick=()=>{const [y,m]=calMonth.split("-").map(Number),d=new Date(y,m,1);calMonth=d.getFullYear()+"-"+String(d.getMonth()+1).padStart(2,"0");delete seen.cal;render(window.__last);};
$("rvseg").onclick=e=>{const b=e.target.closest("[data-r]");if(!b)return;RV=b.dataset.r;qsa("#rvseg button").forEach(x=>x.classList.toggle("on",x===b));delete seen.reviews;render(window.__last);};

// ================= keys: upload with preview, find a key =================
const keyLines=()=>$("kt").value.split(/\r?\n/).map(s=>s.trim()).filter(s=>s&&!s.startsWith("#"));
let kTimer=null,kSeq=0;
function kPreviewSoon(){clearTimeout(kTimer);const n=keyLines().length;$("kcount").textContent=n?plural(n,"key")+" "+t("pasted"):"";$("kadd").disabled=true;
 if(!n){$("kprev").innerHTML="";return;}kTimer=setTimeout(kPreview,350);}
async function kPreview(){
 const my=++kSeq,n=keyLines().length;if(!n)return;
 try{const r=await post("/api/keys",{text:$("kt").value,dry:true});const j=await r.json();if(my!==kSeq)return;
  if(!r.ok){$("kprev").innerHTML=`<span class="pill bad">${esc(j.error||"Error")}</span>`;return;}
  $("kprev").innerHTML=`<span class="pill good">${j.added} ${t("new")}</span><span class="pill ${j.duplicates?"warn":""}">${j.duplicates} ${t("already exist")}</span><span class="pill ${j.invalid?"bad":""}">${j.invalid} ${t("invalid")}</span>`
   +(j.invalid_samples.length?`<span class="muted" style="font-size:12.5px;width:100%">${t("Not a key")}: ${j.invalid_samples.map(esc).join(" · ")}</span>`:"");
  $("kadd").disabled=!j.added;$("kadd").textContent=j.added?t("Add")+" "+plural(j.added,"key"):t("Add keys");
 }catch(e){}
}
$("kt").oninput=kPreviewSoon;
function loadKeyFiles(files){
 const list=[...files].filter(f=>f.size<=400000).slice(0,5);if(!list.length){toast(t("File too large."),"");return;}
 if(page()!=="keys")location.hash="#keys";
 Promise.all(list.map(f=>f.text())).then(texts=>{const add=texts.join("\n");
  $("kt").value=($("kt").value?$("kt").value.replace(/\s*$/,"\n"):"")+add;kPreviewSoon();$("kt").scrollIntoView({block:"nearest"});});
}
$("kf").onchange=e=>{loadKeyFiles(e.target.files);e.target.value="";};
$("kadd").onclick=async()=>{
 if(!keyLines().length)return;$("kadd").disabled=true;
 try{const r=await post("/api/keys",{text:$("kt").value});const j=await r.json();
  if(!r.ok){$("kmsg").innerHTML=`<span style="color:var(--red)">${esc(j.error||"Error")}</span>`;}
  else{$("kmsg").innerHTML=`<span style="color:var(--accent)">${plural(j.added,"key")} ${t("added.")}</span>`+(j.duplicates?` <span class="muted">${j.duplicates} ${t("already existed.")}</span>`:"")+(j.invalid?` <span style="color:var(--amber)">${j.invalid} ${t("skipped (bad format).")}</span>`:"")+` <span class="muted">${fmt(j.left,0)} ${t("waiting in total.")}</span>`;
   $("kt").value="";$("kcount").textContent="";$("kprev").innerHTML="";$("kadd").textContent=t("Add keys");load(true);}
 }catch(e){$("kmsg").innerHTML=`<span style="color:var(--red)">${t("Could not reach the server.")}</span>`;}
};
async function findKey(){
 const k=$("fk").value.trim();if(k.length<6){$("fkres").innerHTML=`<div class="muted" style="margin-top:8px">${t("Type at least 6 characters of the key.")}</div>`;return;}
 $("fkres").innerHTML=`<div class="sk line"></div>`;
 try{const r=await post("/api/keys/find",{key:k});const j=await r.json();
  if(!r.ok){$("fkres").innerHTML=`<div class="muted" style="margin-top:8px">${esc(j.error||"Error")}</div>`;return;}
  remember(j.orders);
  let h=`<div class="pv"><span class="pill ${j.queued?"good":""}">${j.queued?t("Waiting in the queue"):t("Not in the queue")}</span><span class="pill ${j.uploaded?"good":""}">${j.uploaded?t("Uploaded to Eldorado (in stock or sold)"):t("Not uploaded yet")}</span></div>`;
  if(j.orders.length)h+=`<div style="margin-top:10px">${j.orders.map(o=>`<div class="row2" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item)}<small>${esc(o.buyer)} · ${esc(full(o.time))}</small></div><div class="e"><span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span></div></div>`).join("")}</div>`;
  else h+=`<div class="muted" style="margin-top:10px;font-size:13px">${t("No order found for this key.")} ${t("This only works if Eldorado shows the delivered key inside the order, and only for orders the dashboard has seen")} (${fmt(j.tracked,0)}).</div>`;
  $("fkres").innerHTML=h;
 }catch(e){$("fkres").innerHTML=`<div class="muted">${t("Could not reach the server.")}</div>`;}
}
$("fkgo").onclick=findKey;$("fk").onkeydown=e=>{if(e.key==="Enter")findKey();};
// drag a file anywhere on the page
let dragDepth=0;
const hasFiles=e=>e.dataTransfer&&[...(e.dataTransfer.types||[])].includes("Files");
window.addEventListener("dragenter",e=>{if(!hasFiles(e))return;e.preventDefault();dragDepth++;if(isAdmin)$("dropall").classList.add("on");});
window.addEventListener("dragover",e=>{if(hasFiles(e))e.preventDefault();});
window.addEventListener("dragleave",e=>{if(!hasFiles(e))return;dragDepth=Math.max(0,dragDepth-1);if(!dragDepth)$("dropall").classList.remove("on");});
window.addEventListener("drop",e=>{if(!hasFiles(e))return;e.preventDefault();dragDepth=0;$("dropall").classList.remove("on");if(isAdmin)loadKeyFiles(e.dataTransfer.files);});

// ================= profit =================
let PF=null,pfBusy=false;
async function loadProfit(){
 if(pfBusy)return;pfBusy=true;
 try{const r=await fetch("/api/costs");if(r.ok){PF=await r.json();profitDraw();}}catch(e){}
 pfBusy=false;
}
const kindName=k=>k==="monthly"?t("every month"):t("one time");
function profitDraw(){
 if(!PF)return;const p=PF.profit,c=p.currency,cur=esc(shownCur()),m=p.this_month;
 const pill=v=>`<span style="color:${v<0?"var(--red)":"inherit"}">${fmt(mv(v))}</span>`;
 $("ptiles").innerHTML=`<div class="tile"><div class="l">${t("Profit this month")}</div><div class="v">${pill(m.profit)} <small>${cur}</small></div><div class="s">${t("Sales")} ${fmt(mv(m.sales))} − ${t("costs")} ${fmt(mv(m.costs+m.keys))}</div></div>
  <div class="tile"><div class="l">${t("Profit all time")}</div><div class="v">${pill(p.total.profit)} <small>${cur}</small></div><div class="s">${plural(p.total.orders,"order")}</div></div>
  <div class="tile"><div class="l">${t("Costs all time")}</div><div class="v">${fmt(mv(p.total.costs+p.total.keys))} <small>${cur}</small></div><div class="s">${t("incl. keys")} ${fmt(mv(p.total.keys))}</div></div>`;
 $("clist").innerHTML=PF.items.length?PF.items.map(i=>`<div class="row2"><div class="t">${esc(i.name)}<small>${kindName(i.kind)} · ${esc(i.date||"")}</small></div><div class="e"><div class="mono">${fmt(i.amount)} ${esc(i.currency)}</div>${i.currency!==c?`<small class="muted">≈ ${money(i.main,c)}</small><br>`:""}<button class="btn copy" data-delcost="${esc(i.id)}">${t("Delete")}</button></div></div>`).join(""):`<div class="empty">${t("No costs added yet.")}</div>`;
 $("pmonths").innerHTML=`<table><thead><tr><th>${t("Month")}</th><th class="r">${t("Sales")}</th><th class="r">${t("Costs")}</th><th class="r">${t("Keys")}</th><th class="r">${t("Profit")}</th></tr></thead><tbody>${p.months.map(x=>`<tr><td>${esc(monthLabel(x.key))}</td><td class="r mono">${money(x.sales,c)}</td><td class="r mono muted">${money(x.costs,c)}</td><td class="r mono muted">${money(x.keys,c)}</td><td class="r mono" style="font-weight:650;${x.profit<0?"color:var(--red)":""}">${money(x.profit,c)}</td></tr>`).join("")}</tbody></table>`;
 $("pnote").textContent=t("sales after fees − costs");
 if(document.activeElement!==$("kcamt")&&document.activeElement!==$("kccur")){$("kcamt").value=PF.key_cost.amount||"";$("kccur").value=PF.key_cost.currency;}
}
$("cadd").onclick=async()=>{
 const body={name:$("cn").value,amount:$("ca").value,currency:$("cc").value,kind:$("ck").value,date:$("cd").value||undefined};
 const r=await post("/api/costs",body);const j=await r.json();
 if(!r.ok){$("cmsg").style.color="var(--red)";$("cmsg").textContent=j.error||"Error";return;}
 $("cmsg").style.color="var(--accent)";$("cmsg").textContent=t("Cost added.");$("cn").value="";$("ca").value="";PF=j;profitDraw();
};
$("kcsave").onclick=async()=>{
 const r=await post("/api/keycost",{amount:$("kcamt").value||0,currency:$("kccur").value},"PUT");const j=await r.json();
 if(r.ok){PF=j;profitDraw();$("cmsg").style.color="var(--accent)";$("cmsg").textContent=t("Saved.");}else{$("cmsg").style.color="var(--red)";$("cmsg").textContent=j.error||"Error";}
};
$("clist").onclick=async e=>{const b=e.target.closest("[data-delcost]");if(!b)return;
 if(!b.classList.contains("sure")){b.classList.add("sure");b.textContent=t("Sure? Delete");setTimeout(()=>{if(b.isConnected){b.classList.remove("sure");b.textContent=t("Delete");}},3000);return;}
 const r=await post("/api/costs/"+encodeURIComponent(b.dataset.delcost),null,"DELETE");if(r.ok){PF=await r.json();profitDraw();}};

// ================= users + devices =================
async function users(){
 const r=await fetch("/api/users");if(!r.ok)return;const us=await r.json();
 $("ulist").innerHTML=us.map(u=>`<div class="urow"><div><span class="dotpill ${u.online?"on":""}"></span>${esc(u.name)} <span class="pill">${esc(t(u.role))}</span><div class="muted" style="font-size:12px;margin-left:14px">${u.online?t("online now"):u.last_seen?t("last seen")+" "+esc(ago(u.last_seen)):t("never seen")}</div></div>
  <div class="row" style="margin:0"><input type="password" placeholder="${esc(t("New password"))}" data-pw="${esc(u.name)}" autocomplete="new-password" style="width:150px">
  <button class="btn" data-setpw="${esc(u.name)}">${t("Set")}</button><button class="btn" data-del="${esc(u.name)}">${t("Delete")}</button></div></div>`).join("");
}
$("addu").onclick=async()=>{
 const r=await post("/api/users",{username:$("nu").value,password:$("np").value,role:$("nr").value});
 const j=await r.json();$("umsg").textContent=r.ok?t("User added."):(j.error||"Error");
 if(r.ok){$("nu").value="";$("np").value="";users();}
};
$("ulist").onclick=async e=>{
 const del=e.target.dataset.del,set=e.target.dataset.setpw;
 if(del){if(!confirm(t("Delete user")+" "+del+"?"))return;const r=await post("/api/users/"+encodeURIComponent(del),null,"DELETE");
  const j=await r.json();$("umsg").textContent=r.ok?t("Deleted."):(j.error||"Error");users();loadDevices();}
 if(set){const el=document.querySelector('[data-pw="'+CSS.escape(set)+'"]');const r=await post("/api/users/"+encodeURIComponent(set),{password:el.value});
  const j=await r.json();$("umsg").textContent=r.ok?t("Password changed. That user was signed out on all devices."):(j.error||"Error");if(r.ok){el.value="";loadDevices();}}
};
let DEV=null;
function devRow(d,showUser){return `<div class="row2"><div class="t">${esc(d.label)}${d.current?` <span class="pill good">${t("This device")}</span>`:""}<small>${showUser?esc(d.user)+" · ":""}${esc(d.ip||"")} · ${t("signed in")} ${esc(ago(d.created))} · ${t("last seen")} ${esc(ago(d.seen))}</small></div><div class="e"><button class="btn copy" data-devout="${esc(d.id)}">${t("Sign out")}</button></div></div>`;}
async function loadDevices(){
 try{const r=await fetch("/api/devices");if(!r.ok)return;DEV=await r.json();devDraw();}catch(e){}
}
function devDraw(){
 if(!DEV||!window.__last)return;const me=window.__last.user.name.toLowerCase();
 const mine=DEV.devices.filter(d=>d.user===me);
 $("mydev").innerHTML=mine.length?mine.map(d=>devRow(d,false)).join(""):`<div class="empty">${t("No devices.")}</div>`;
 if(isAdmin){
  $("devall").innerHTML=DEV.devices.length?DEV.devices.map(d=>devRow(d,true)).join(""):`<div class="empty">${t("No devices.")}</div>`;
  $("loglist").innerHTML=DEV.log.length?DEV.log.map(l=>`<div class="row2"><div class="t">${esc(l.user)} <span class="pill ${l.ok?"good":"bad"}">${l.ok?t("signed in"):t("failed")}</span><small>${esc(l.label)} · ${esc(l.ip||"")}</small></div><div class="e muted" title="${esc(full(l.time))}">${esc(ago(l.time))}</div></div>`).join(""):`<div class="empty">${t("Nothing yet.")}</div>`;}
}
document.addEventListener("click",async e=>{const b=e.target.closest("[data-devout]");if(!b)return;
 if(!b.classList.contains("sure")){b.classList.add("sure");b.textContent=t("Sure?");setTimeout(()=>{if(b.isConnected){b.classList.remove("sure");b.textContent=t("Sign out");}},3000);return;}
 const r=await post("/api/devices/"+encodeURIComponent(b.dataset.devout),null,"DELETE");const j=await r.json().catch(()=>({}));
 if(j.me){location="/login";return;}loadDevices();});

// ================= history =================
let HF="all",HN=100,HLAST=null;
async function loadHistory(){
 try{const r=await fetch("/api/history?filter="+HF+"&limit="+HN);if(!r.ok)return;HLAST=await r.json();histRender();}catch(e){$("hlist").innerHTML=`<div class="empty">${t("Could not load.")}</div>`;}
}
function histRender(){
 const j=HLAST;if(!j)return;const c=j.currency;
 const tile=(l,v,sub,cls)=>`<div class="tile"><div class="l">${l}</div><div class="v ${cls||""}">${v}</div><div class="s">${sub}</div></div>`;
 const sg=(v,s)=>(Math.abs(v)<0.005?"":s>0?"+":"−")+fmt(mv(Math.abs(v)));
 $("htiles").innerHTML=
  tile(t("Added today"),sg(j.added_today,1)+" <small>"+esc(shownCur())+"</small>",plural(j.n_added_today,"order"))
  +tile(t("Removed today"),sg(j.removed_today,-1)+" <small>"+esc(shownCur())+"</small>",plural(j.n_removed_today,"order"),j.removed_today?"bad":"")
  +tile(t("Net this month"),sg(j.added_month-j.removed_month,j.added_month-j.removed_month>=0?1:-1)+" <small>"+esc(shownCur())+"</small>",t("Added")+" "+fmt(mv(j.added_month))+" · "+t("Removed")+" "+fmt(mv(j.removed_month)))
  +tile(t("Balance now"),fmt(mv(j.balance))+" <small>"+esc(shownCur())+"</small>",feeNote());
 const ev=j.events;
 $("hnote").textContent=j.total?plural(j.total,"event"):"";
 if(!ev.length){$("hlist").innerHTML=`<div class="empty">${t("Nothing yet.")}</div>`;$("hmore").hidden=true;return;}
 let html="",day="",rows=[];
 const flush=()=>{if(!rows.length)return;html+=rows.join("");rows=[];};
 const sums={};
 ev.forEach(e=>{const k=new Date(e.t).toDateString();if(e.currency===c)sums[k]=(sums[k]||0)+(e.k==="add"?1:-1)*(GROSS?e.gross:e.net);});
 ev.forEach(e=>{
  const k=new Date(e.t).toDateString();
  if(k!==day){flush();day=k;const s=sums[k]||0;html+=`<div class="hday"><div>${esc(dayLabel(e.t))}</div><span>${s>=0?"+":"−"}${fmt(mv(Math.abs(s)))} ${esc(shownCur())}</span></div>`;}
  const add=e.k==="add",amt=GROSS?e.gross:e.net;
  html+=`<div class="hrow"><div class="l"><div class="ic ${add?"":"rem"}">${add?"+":"−"}</div><div class="t">${esc(e.item||"?")}${add?"":` <span class="pill bad">${t("Cancelled")}</span>`}<small>${e.est?esc(t("time not tracked"))+" · ":""}<button class="lnk" data-buyer="${esc(e.buyer)}">${esc(e.buyer||"?")}</button> · ${esc(tm(e.t))}${e.id?` · <button class="lnk" data-copy="${esc(e.id)}" title="${esc(t("Copy order ID"))}">${esc(e.id.slice(0,8))}</button>`:""}</small></div></div>
   <div class="amt ${add?"add":"rem"}">${add?"+":"−"}${money(amt,e.currency)}${e.bal!=null?`<small>${t("Balance")} ${fmt(mv(e.bal))}</small>`:""}</div></div>`;
 });
 $("hlist").innerHTML=html;$("hmore").hidden=!j.more;
}
$("hseg").onclick=e=>{const b=e.target.closest("[data-h]");if(!b)return;HF=b.dataset.h;HN=100;qsa("#hseg button").forEach(x=>x.classList.toggle("on",x===b));loadHistory();};
$("hmore").onclick=()=>{HN+=100;loadHistory();};

// ================= settings =================
function setTheme(th){document.documentElement.dataset.theme=th;lsSet("theme",th);
 const m=document.querySelector('meta[name=theme-color]');if(m)m.content=th==="light"?"#f4f5f8":"#0e1014";applyAccent();settingsUi();rerender();}
function setLang(l){LANG=l;PREFS.lang=l;syncLocal();savePrefs();translateStatic();setTitle();settingsUi();newsRender();rerender();users_ui_refresh();}
function users_ui_refresh(){if(page()==="users"&&isAdmin){users();devDraw();}else devDraw();}
function setCur(c){CURSEL=c===MAIN?"":c;PREFS.currency=CURSEL;syncLocal();savePrefs();settingsUi();rerender();}
function setGross(b){GROSS=!!b;lsSet("gross",GROSS?"1":"0");PREFS.gross=GROSS;savePrefs();settingsUi();rerender();}
function setHide(b){HIDE=!!b;lsSet("hide",HIDE?"1":"0");document.body.classList.toggle("hide",HIDE);settingsUi();rerender();}
function setAccent(hex){PREFS.accent=hex;syncLocal();savePrefs();applyAccent();settingsUi();rerender();}
function settingsUi(){
 qsa("#gnSeg button,#gnSeg2 button").forEach(b=>b.classList.toggle("on",(b.dataset.g==="1")===GROSS));
 qsa("#langSeg button").forEach(b=>b.classList.toggle("on",b.dataset.l===LANG));
 qsa("#thSeg button").forEach(b=>b.classList.toggle("on",b.dataset.t===document.documentElement.dataset.theme));
 $("setHide").checked=HIDE;$("hide").classList.toggle("on",HIDE);
 $("sndsel").value=PREFS.sound||"ding";
 qsa("[data-n]").forEach(c=>{c.checked=!!PREFS.notify[c.dataset.n];});
 $("notifybox").style.display=isAdmin?"":"none";
 const acc=PREFS.accent;
 $("sw").innerHTML=ACCENTS.map(a=>`<i data-a="${a[0]}" class="${(acc===a[0]||(acc&&acc===a[1]))?"on":""}" style="background:${a[0]||"var(--accent)"}" title="${a[2]?esc(t(a[2])):esc(t("Default"))}"></i>`).join("")
  +`<input type="color" id="accpick" value="${/^#[0-9a-f]{6}$/i.test(acc)?acc:"#34d399"}" title="${esc(t("Pick any colour"))}" aria-label="${esc(t("Pick any colour"))}">`;
 $("accpick").oninput=e=>{PREFS.accent=e.target.value;syncLocal();applyAccent();};
 $("accpick").onchange=e=>setAccent(e.target.value);
 curUi();tglUi();
 $("bgSeg").innerHTML=BGS.map(b=>`<button type="button" class="chip${(PREFS.bg||"")===b[0]?" on":""}" data-bg="${b[0]}">${esc(t(b[1]))}</button>`).join("");
 const defs=[["today","Today"],["month","This month"],["all","All time"],["avg","Average order"],["stock","In stock"],["profit","Profit this month",1],["taxpot","Tax pot",1],["lastorder","Latest order"],["revrate","Reviews per order"],["chart","Sales per month"],["latest","Latest orders"],["pending","Waiting to be completed"],["reviews","Reviews"],["keys","Keys left"]];
 $("tilesel").innerHTML=defs.filter(x=>!x[2]||isAdmin).map(x=>`<label class="tgl"><div>${esc(t(x[1]))}</div><input type="checkbox" data-tile="${x[0]}"${hid(x[0])?"":" checked"}></label>`).join("");
 $("profbox").style.display=isAdmin?"":"none";$("taxbox").style.display=isAdmin?"":"none";
 if(document.activeElement!==$("pemoji"))$("pemoji").value=PREFS.emoji||"";
 if(document.activeElement!==$("taxpct"))$("taxpct").value=PREFS.tax==null?37:PREFS.tax;
 const pc=PREFS.color;
 $("pcol").innerHTML=["","#60a5fa","#a78bfa","#f472b6","#fb923c","#f87171","#2dd4bf","#fbbf24"].map(c=>`<i data-pc="${c}" class="${pc===c?"on":""}" style="background:${c||"var(--ink2)"}" title="${c?"":esc(t("Default"))}"></i>`).join("")
  +`<input type="color" id="pcpick" value="${/^#[0-9a-f]{6}$/i.test(pc)?pc:"#34d399"}" aria-label="${esc(t("Pick any colour"))}">`;
 $("pcpick").onchange=e=>setProfile({color:e.target.value});
 $("pprev").innerHTML=`<span class="pv" style="${PREFS.color?"color:"+esc(PREFS.color):""}">${esc(PREFS.emoji||"")} ${esc(window.__last?window.__last.user.name:"")}</span>`;
}
function setProfile(o){Object.assign(PREFS,o);savePrefs();settingsUi();if(typeof wrRender==="function"){wrStyles={...wrStyles,[wrMe]:{emoji:PREFS.emoji,color:PREFS.color}};wrRender();}}
function setBg(b){PREFS.bg=b;applyBg();savePrefs();settingsUi();}
$("bgSeg").onclick=e=>{const b=e.target.closest("[data-bg]");if(b)setBg(b.dataset.bg);};
$("tilesel").onchange=e=>{const c=e.target.closest("[data-tile]");if(!c)return;const k=c.dataset.tile,h=new Set(PREFS.hide||[]);c.checked?h.delete(k):h.add(k);PREFS.hide=[...h];savePrefs();rerender();};
$("pcol").onclick=e=>{const i=e.target.closest("i[data-pc]");if(i)setProfile({color:i.dataset.pc});};
$("pemoji").onchange=e=>setProfile({emoji:[...e.target.value.trim()].slice(0,2).join("")});
$("taxpct").onchange=e=>{let v=parseFloat(String(e.target.value).replace(",","."));if(!(v>=0))v=37;v=Math.min(80,Math.max(0,v));PREFS.tax=v;e.target.value=v;savePrefs();rerender();};

// ================= currency calculator =================
function calcList(){const o=CURRENCIES_ALL().filter((c,i,a)=>a.indexOf(c)===i&&RATES[c]);return o.length?o:["USD","DKK","EUR"];}
function calcRun(){
 const list=calcList(),f=$("calcf"),to=$("calct");
 if(f.dataset.sig!==list.join()){const opt=list.map(c=>`<option value="${c}">${c}</option>`).join("");f.innerHTML=opt;to.innerHTML=opt;f.dataset.sig=list.join();
  f.value=list.includes(lsGet("calc_f",""))?lsGet("calc_f",""):MAIN;to.value=list.includes(lsGet("calc_t",""))?lsGet("calc_t",""):(list.find(c=>c!==f.value)||f.value);}
 const a=parseFloat(String($("calca").value).replace(/\s/g,"").replace(",","."));
 lsSet("calc_f",f.value);lsSet("calc_t",to.value);
 const rf=RATES[f.value],rt=RATES[to.value];
 if(!(a>=0)||!rf||!rt){$("calcr").textContent="-";$("calcn").textContent="";return;}
 $("calcr").textContent=fmt(a/rf*rt,2);
 $("calcn").textContent="1 "+f.value+" = "+fmt(rt/rf,4)+" "+to.value+" · "+(RATES_LIVE?t("today's rates")+(RATES_DATE?" ("+RATES_DATE+")":""):t("rough rates"));
}
function calcOpen(open){const c=$("calc");c.hidden=!open;if(open){calcRun();setTimeout(()=>{$("calca").focus();$("calca").select();},30);}}
$("calcbtn").onclick=e=>{e.stopPropagation();calcOpen($("calc").hidden);};
$("calcx").onclick=()=>calcOpen(false);
$("calcsw").onclick=()=>{const f=$("calcf"),to=$("calct"),x=f.value;f.value=to.value;to.value=x;calcRun();};
["calca"].forEach(id=>$(id).oninput=calcRun);["calcf","calct"].forEach(id=>$(id).onchange=calcRun);
document.addEventListener("pointerdown",e=>{if(!$("calc").hidden&&!e.target.closest("#calc,#calcbtn"))calcOpen(false);});
document.addEventListener("keydown",e=>{if(e.key==="Escape"&&!$("calc").hidden)calcOpen(false);});
$("gnSeg").onclick=e=>{const b=e.target.closest("[data-g]");if(b)setGross(b.dataset.g==="1");};
$("gnSeg2").onclick=e=>{const b=e.target.closest("[data-g]");if(b)setGross(b.dataset.g==="1");};
$("langSeg").onclick=e=>{const b=e.target.closest("[data-l]");if(b)setLang(b.dataset.l);};
$("thSeg").onclick=e=>{const b=e.target.closest("[data-t]");if(b)setTheme(b.dataset.t);};
$("curSeg").onclick=e=>{const b=e.target.closest("[data-c]");if(b)setCur(b.dataset.c);};
$("curSel").onchange=e=>setCur(e.target.value);
$("setHide").onchange=e=>setHide(e.target.checked);
$("hide").onclick=()=>setHide(!HIDE);
$("theme").onclick=()=>setTheme(document.documentElement.dataset.theme==="light"?"dark":"light");
$("sw").onclick=e=>{const i=e.target.closest("i[data-a]");if(i)setAccent(i.dataset.a);};
$("sndsel").onchange=e=>{PREFS.sound=e.target.value;syncLocal();savePrefs();playSound(PREFS.sound==="none"?"ding":PREFS.sound,true);};
$("sndtest").onclick=()=>playSound(PREFS.sound==="none"?"ding":PREFS.sound,true);
qsa("[data-n]").forEach(c=>{c.onchange=()=>{PREFS.notify[c.dataset.n]=c.checked;savePrefs();};});
$("logout").onclick=async()=>{await post("/logout");location="/login";};

// ================= what's new =================
const NEWS=[{v:"2026-10-27",d:"2026-10-27",title:["History","Historik"],items:[
 ["New History page: every time an order is added (+) or cancelled and taken off (−), with the amount and the balance after it","Ny Historik-side: hver gang en ordre lægges til (+) eller annulleres og trækkes fra (−), med beløbet og saldoen efter"],
 ["Filter on added or removed, see totals for today and this month","Filtrér på tilføjet eller fratrukket, se totaler for i dag og denne måned"],
 ["Note: cancelled orders show from the moment the history started. Update order_alerts.py too","Bemærk: annullerede ordrer vises fra det tidspunkt, historikken startede. Opdatér også order_alerts.py"]]},
{v:"2026-10-26 · 2",d:"2026-10-26",title:["More tools","Flere værktøjer"],items:[
 ["Tax pot under the quote: how much we have avoided paying, in kroner (the percent is set in Settings and starts at 37% of profit)","Skattepotte under citatet: hvor meget vi har sluppet for at betale, i kroner (procenten sættes i Indstillinger og starter på 37% af profit)"],
 ["Stock forecast: how many days the keys last at the current pace","Lagerprognose: hvor mange dage keysene rækker ved nuværende tempo"],
 ["Eldorado connection status on the overview","Status for forbindelsen til Eldorado på overblikket"],
 ["Time since the latest order, amber after 2 hours and red after 6","Tid siden seneste ordre, gul efter 2 timer og rød efter 6"],
 ["Share of orders that get a review","Andel af ordrer der får en anmeldelse"],
 ["War-Room: write @name to notify a person, with suggestions while you type","War-Room: skriv @navn for at give en person besked, med forslag mens du skriver"],
 ["Currency calculator in the top bar","Valutaregner i den øverste bjælke"],
 ["Choose a background: dots, grid, waves, aurora or diagonal","Vælg en baggrund: prikker, gitter, bølger, nordlys eller diagonal"],
 ["Today widget page for your home screen","I dag-widgetside til din startskærm"],
 ["Your own emoji and name colour in the War-Room","Din egen emoji og navnefarve i War-Room"],
 ["Your currency, net/gross choice and which overview boxes you see now follow your account on every device","Din valuta, netto/brutto-valg og hvilke felter du ser på overblikket følger nu din konto på alle enheder"],
 ["News like this disappears 7 days after it was added","Nyheder som disse forsvinder 7 dage efter de er tilføjet"]]},
{v:"2026-10-26",d:"2026-10-26",title:["Big update","Stor opdatering"],items:[
 ["Welcome line with the day's essentials, and the quote at the top","Velkomstlinje med dagens vigtigste tal, og citatet øverst"],
 ["Calendar: every day shows its sales, click a day to see its orders","Kalender: hver dag viser sit salg, klik på en dag for at se ordrerne"],
 ["Average order value, best day / week / month and a “New record!” marker","Gennemsnitlig ordre, bedste dag / uge / måned og et “Ny rekord!”-mærke"],
 ["Fees overview and a Net / Gross button","Overblik over gebyrer og en Netto / Brutto-knap"],
 ["Show amounts in DKK, USD or EUR","Vis beløb i DKK, USD eller EUR"],
 ["Profit page: add your costs (VPS, domain, keys) and see the real profit per month","Profit-side: tilføj dine omkostninger (VPS, domæne, keys) og se den rigtige fortjeneste pr. måned"],
 ["Click an order for details and a timeline, click a buyer to see all their orders, search buyers and orders","Klik på en ordre for detaljer og tidslinje, klik på en køber for alle deres ordrer, søg efter købere og ordrer"],
 ["List of orders waiting to be completed, with how long they have waited","Liste over ordrer der venter på at blive gennemført, og hvor længe de har ventet"],
 ["Good / bad review button, and the buyer's name on bad reviews with copy buttons","Knap til gode / dårlige anmeldelser, og købers navn på dårlige anmeldelser med kopiér-knapper"],
 ["Drag a keys file onto the page: you get a preview (new, duplicates, invalid) before anything is added","Træk en keys-fil ind på siden: du får en forhåndsvisning (nye, dubletter, ugyldige) før noget tilføjes"],
 ["Find which order a key belongs to","Find hvilken ordre en key hører til"],
 ["War-Room: typing indicator, choose your sound, see who is online and when others were last seen","War-Room: “skriver…”-visning, vælg din lyd, se hvem der er online og hvornår andre sidst var der"],
 ["Notification settings per person: War-Room, new orders, bad reviews, keys running low","Notifikationsindstillinger pr. person: War-Room, nye ordrer, dårlige anmeldelser, keys ved at løbe tør"],
 ["See every login and device, and sign a device out","Se alle logins og enheder, og log en enhed ud"],
 ["Danish and English, your own accent colour, a button that hides all numbers","Dansk og engelsk, din egen farve, og en knap der skjuler alle tal"],
 ["Loading placeholders, pull down to refresh on your phone, small number animations","Pladsholdere mens der indlæses, træk ned for at opdatere på mobilen, små tal-animationer"]]}];
const newsActive=()=>NEWS.filter(n=>{const [y,m,d]=n.d.split("-").map(Number);return (Date.now()-new Date(y,m-1,d).getTime())/864e5<7;});
function newsNav(){
 const on=newsActive().length>0,a=qs('[data-p="news"]');
 qsa('[data-p="news"]').forEach(x=>{x.hidden=!on;});
 if(!on){$("newdot").hidden=true;if(page()==="news")location.hash="#overview";}
 else $("newdot").hidden=lsGet("seen_ver","")===VERSION;
}
function newsRender(){
 $("newsbox").innerHTML=newsActive().map(n=>`<div class="relnote"><h3>${esc(n.title[LANG==="da"?1:0])} <span class="muted" style="font-weight:400;font-size:13px">${esc(n.v)}</span></h3><ul>${n.items.map(i=>`<li>${esc(i[LANG==="da"?1:0])}</li>`).join("")}</ul></div>`).join("");
 lsSet("seen_ver",VERSION);$("newdot").hidden=true;
}

// ================= translate the fixed text on the page =================
const ORIG=new WeakMap();
function translateStatic(){
 const w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT,{acceptNode:n=>{const p=n.parentElement;
  if(!p||p.closest("script,style,.dyn,textarea"))return NodeFilter.FILTER_REJECT;return n.nodeValue.trim()?NodeFilter.FILTER_ACCEPT:NodeFilter.FILTER_REJECT;}});
 let n;while((n=w.nextNode())){if(!ORIG.has(n))ORIG.set(n,n.nodeValue);const o=ORIG.get(n),k=o.trim(),tr=t(k);n.nodeValue=tr===k?o:o.replace(k,tr);}
 qsa("[placeholder],[title],[aria-label]").forEach(el=>{["placeholder","title","aria-label"].forEach(a=>{if(!el.hasAttribute(a))return;
  const key="o"+a.replace("-","");if(el.dataset[key]===undefined)el.dataset[key]=el.getAttribute(a);el.setAttribute(a,t(el.dataset[key]));});});
 document.documentElement.lang=LANG;
}

// ================= page switching, loading =================
function setTitle(){const p=page();$("title").textContent=t(TITLES[p]);document.title=t(TITLES[p])+" · "+SHOP;}
const TT={orders:0,profit:0,users:0,dev:0,hist:0};
function pageLoad(force){
 const p=page(),now=Date.now();
 if(p==="orders"&&(force||now-TT.orders>4500)){TT.orders=now;loadOrders();}
 if(p==="profit"&&isAdmin&&(force||now-TT.profit>15000)){TT.profit=now;loadProfit();}
 if(p==="history"&&(force||now-TT.hist>6000)){TT.hist=now;loadHistory();}
 if(p==="users"&&isAdmin&&(force||now-TT.users>10000)){TT.users=now;users();loadDevices();}
 if(p==="settings"&&(force||now-TT.dev>15000)){TT.dev=now;loadDevices();}
 if(p==="settings")settingsUi();
 if(p==="news")newsRender();
}
function show(){
 const p=page();
 document.querySelectorAll(".page").forEach(s=>s.classList.toggle("on",s.id==="p-"+p));
 document.querySelectorAll("#nav a").forEach(a=>a.classList.toggle("on",a.dataset.p===p));
 setTitle();
 for(const k in seen)delete seen[k];
 if(window.__last)render(window.__last);
 pageLoad(true);
 if(p==="users"&&isAdmin){}
 if(p==="mindmap")mmPoll(true);
 if(p==="warroom"){wrRender(true);wrMarkRead();wrPoll();setTimeout(()=>$("wt").focus({preventScroll:true}),50);}
 window.scrollTo(0,0);
}
window.addEventListener("hashchange",()=>{drawerClose();show();});
let lastOk=0,lastHash="";
async function load(force){
 try{const r=await fetch("/api/data"+(force||!lastHash?"":"?h="+lastHash));if(r.status===401){location="/login";return;}
  const j=await r.json();
  if(!j.same){lastHash=j.h||"";window.__render(j);}
  lastOk=Date.now();}catch(e){}
 const stale=Date.now()-lastOk>20000;$("dot").classList.toggle("stale",stale);
 $("upd").textContent=lastOk?(stale?t("Connection lost"):t("Live")+" · "+new Date(lastOk).toLocaleTimeString(LOC())):"";
 pageLoad(false);
}
async function refreshAll(){const p=$("ptr");p.classList.add("spin");p.style.top="14px";await Promise.all([load(true),Promise.resolve(pageLoad(true))]);setTimeout(()=>{p.classList.remove("spin");p.style.top="";},600);}

// ---------- pull down to refresh (phones) ----------
(function(){
 let st=null;const p=$("ptr");
 document.addEventListener("touchstart",e=>{
  if(window.scrollY>0||e.touches.length!==1||["warroom","mindmap"].includes(page())||drawerIsOpen()||e.target.closest("textarea,input,select,.mmboard,.msgs,.drawer"))return;
  st={y:e.touches[0].clientY,dy:0};},{passive:true});
 document.addEventListener("touchmove",e=>{if(!st)return;const dy=e.touches[0].clientY-st.y;st.dy=dy;
  if(dy<=0||window.scrollY>0){p.style.top="";return;}p.style.transition="none";p.style.top=Math.min(dy*.5,70)-34+"px";},{passive:true});
 document.addEventListener("touchend",()=>{if(!st)return;const go=st.dy>110;st=null;p.style.transition="";
  if(go)refreshAll();else p.style.top="";});
})();

// ---------- War-Room ----------
let wrStyles={},wrPeople=[];let wrLast=0,wrRev=-1,wrMsgs=[],wrSeen=null,wrMe="",wrStarted=false,wrEdit=null,wrSure=null,wrUnreadTitle=0;
const BASE_TITLE=document.title;
const hhmm=tm;
const dayKey=iso=>new Date(iso).toDateString();
function dayLabel(iso){const d=new Date(iso),n=new Date(),y=new Date(Date.now()-864e5);
 return d.toDateString()===n.toDateString()?t("Today"):d.toDateString()===y.toDateString()?t("Yesterday"):d.toLocaleDateString(LOC(),{weekday:"short",day:"numeric",month:"short"});}
let soundOn=lsGet("wr_sound","1")==="1",noteOn=lsGet("wr_note","0")==="1";
let actx=null;
function audio(){try{if(!actx){const C=window.AudioContext||window.webkitAudioContext;if(C)actx=new C();}if(actx&&actx.state==="suspended")actx.resume();}catch(e){}return actx;}
const SND={ding:[[880,0],[1318,.12]],bell:[[1568,0],[1175,.2],[784,.4]],pop:[[420,0],[700,.07]],chime:[[659,0],[784,.1],[988,.2],[1319,.3]]};
function playSound(name,force){
 if(!force&&!soundOn)return;const c=audio();if(!c)return;const seq=SND[name]||SND.ding;
 try{const t0=c.currentTime;seq.forEach(([f,o])=>{const os=c.createOscillator(),g=c.createGain();os.type=name==="pop"?"triangle":"sine";os.frequency.value=f;
  g.gain.setValueAtTime(0.0001,t0+o);g.gain.exponentialRampToValueAtTime(.22,t0+o+.02);g.gain.exponentialRampToValueAtTime(.0001,t0+o+.35);
  os.connect(g);g.connect(c.destination);os.start(t0+o);os.stop(t0+o+.4);});}catch(e){}
}
function ding(){if(PREFS.sound==="none")return;playSound(PREFS.sound||"ding");}
const iosWeb=/iphone|ipad|ipod/i.test(navigator.userAgent)&&!(window.matchMedia("(display-mode: standalone)").matches||navigator.standalone===true);
const notifyOK=()=>typeof Notification!=="undefined"&&window.isSecureContext;
let pushOn=false;
const b64u8=s=>{s=s.replace(/-/g,"+").replace(/_/g,"/");s+="=".repeat((4-s.length%4)%4);const r=atob(s);return Uint8Array.from(r,c=>c.charCodeAt(0));};
async function pushSubscribe(){
 pushOn=false;
 try{
  if(!("serviceWorker" in navigator)||!("PushManager" in window))return;
  const k=await (await fetch("/api/push/key")).json();if(!k.enabled)return;
  const reg=await navigator.serviceWorker.ready;let sub=await reg.pushManager.getSubscription();
  if(sub){const cur=sub.options&&sub.options.applicationServerKey;
   if(cur&&btoa(String.fromCharCode(...new Uint8Array(cur))).replace(/\+/g,"-").replace(/\//g,"_").replace(/=+$/,"")!==k.key){await sub.unsubscribe();sub=null;}}
  if(!sub)sub=await reg.pushManager.subscribe({userVisibleOnly:true,applicationServerKey:b64u8(k.key)});
  const r=await post("/api/push/subscribe",{subscription:sub.toJSON()});pushOn=r.ok;
 }catch(e){pushOn=false;}
 tglUi();
}
async function pushUnsubscribe(){
 try{const reg=await navigator.serviceWorker.ready;const sub=await reg.pushManager.getSubscription();
  if(sub){await post("/api/push/unsubscribe",{endpoint:sub.endpoint});await sub.unsubscribe();}}catch(e){}
 pushOn=false;
}
function tglUi(){
 $("tsound").textContent=t("Sound")+": "+(soundOn?t("on"):t("off"));$("tsound").classList.toggle("on",soundOn);
 [$("tnote"),$("setnote")].forEach(n=>{
  if(!n)return;
  if(!window.isSecureContext){n.textContent=t("Notifications")+": "+t("needs https");n.disabled=true;n.title=t("Browsers only allow notifications on https:// pages (or localhost).");return;}
  if(typeof Notification==="undefined"){n.textContent=t("Notifications")+": "+(iosWeb?t("install the app first"):t("not supported"));n.disabled=true;return;}
  const ok=noteOn&&Notification.permission==="granted";
  n.textContent=t("Notifications")+": "+(Notification.permission==="denied"?t("blocked in browser"):ok?(pushOn?t("on (also when closed)"):t("on")):t("off"));n.classList.toggle("on",ok);
 });
}
$("tsound").onclick=()=>{soundOn=!soundOn;lsSet("wr_sound",soundOn?"1":"0");audio();tglUi();if(soundOn)ding();};
async function toggleNotifications(){
 if(!notifyOK())return;
 if(noteOn&&Notification.permission==="granted"){noteOn=false;lsSet("wr_note","0");await pushUnsubscribe();tglUi();return;}
 let p=Notification.permission;if(p==="default")p=await Notification.requestPermission();
 noteOn=p==="granted";lsSet("wr_note",noteOn?"1":"0");tglUi();
 if(noteOn){await pushSubscribe();
  try{const reg=await navigator.serviceWorker.getRegistration();const o={body:pushOn?t("You will get notifications even when the app is closed."):t("Notifications are on while the page is open."),icon:"/icon-192.png"};
   if(reg)await reg.showNotification("War-Room",o);else new Notification("War-Room",o);}catch(e){}}
}
$("tnote").onclick=toggleNotifications;$("setnote").onclick=toggleNotifications;
document.addEventListener("pointerdown",()=>audio(),{once:true});
document.addEventListener("keydown",()=>audio(),{once:true});
function wrAlert(msgs){
 const others=msgs.filter(m=>m.user!==wrMe);if(!others.length||!PREFS.notify.warroom)return;
 ding();
 others.filter(m=>(m.mentions||[]).includes(wrMe)).forEach(m=>toast(m.user+" "+t("mentioned you"),m.text.slice(0,90),()=>{location.hash="#warroom";}));
 try{if(navigator.vibrate)navigator.vibrate(80);}catch(e){}
 const away=document.hidden||page()!=="warroom";
 if(away){wrUnreadTitle+=others.length;document.title="("+wrUnreadTitle+") "+t("War-Room");}
 if(away&&noteOn&&notifyOK()&&Notification.permission==="granted"){
  const m=others[others.length-1];
  const title="War-Room · "+m.user,opts={body:m.text.slice(0,140),tag:"warroom",renotify:true,icon:"/icon-192.png",badge:"/icon-192.png"};
  const plain=()=>{try{const n=new Notification(title,opts);n.onclick=()=>{window.focus();location.hash="#warroom";n.close();};}catch(e){}};
  if(navigator.serviceWorker&&navigator.serviceWorker.getRegistration)navigator.serviceWorker.getRegistration().then(r=>r?r.showNotification(title,opts):plain()).catch(plain);else plain();
 }
}
document.addEventListener("visibilitychange",()=>{if(!document.hidden&&page()==="warroom"){wrUnreadTitle=0;document.title=t(TITLES.warroom)+" · "+SHOP;wrMarkRead();}});
function nameHtml(n,mine){const s=wrStyles[n]||{};return `<span${s.color?` style="color:${esc(s.color)};font-weight:600"`:""}>${s.emoji?esc(s.emoji)+" ":""}${mine?t("You"):esc(n)}</span>`;}
function mentionHtml(text){
 let h=esc(text);if(!wrPeople.length)return h;
 const names=wrPeople.map(n=>n.replace(/[.*+?^${}()|[\]\\]/g,"\\$&")).sort((a,b)=>b.length-a.length).join("|");
 return h.replace(new RegExp("(^|[^\\w@])@("+names+")(?![\\w-])","gi"),(m,p,n)=>p+'<span class="men">@'+n+"</span>");
}
function wrRender(forceBottom){
 const box=$("msgs");if(!box)return;
 const near=box.scrollHeight-box.scrollTop-box.clientHeight<80;
 const ed=wrEdit&&document.getElementById("ed-"+wrEdit.id);if(ed)wrEdit.text=ed.value;
 let html="",lastDay="",lastUser="";
 for(const m of wrMsgs.slice(-300)){
  const dk=dayKey(m.time);if(dk!==lastDay){html+=`<div class="day">${esc(dayLabel(m.time))}</div>`;lastDay=dk;lastUser="";}
  const mine=m.user===wrMe,editing=wrEdit&&wrEdit.id===m.id,tome=(m.mentions||[]).includes(wrMe);
  const head=m.user!==lastUser||!lastUser?`<div class="w">${nameHtml(m.user,mine)} · ${esc(hhmm(m.time))}</div>`:"";
  let body;
  if(editing)body=`<div class="bub"><div class="editbox"><textarea id="ed-${m.id}" rows="2" maxlength="1000">${esc(wrEdit.text)}</textarea><div class="row"><button class="btn" data-a="cancel">${t("Cancel")}</button><button class="btn primary" data-a="save" data-id="${m.id}">${t("Save")}</button></div></div></div>`;
  else body=`<div class="bub" title="${esc(full(m.time))}">${mentionHtml(m.text)}${m.edited?'<span class="edited">('+t("edited")+')</span>':""}</div>`
   +(mine?`<div class="acts"><button data-a="edit" data-id="${m.id}">${t("Edit")}</button><button class="del${wrSure===m.id?" sure":""}" data-a="del" data-id="${m.id}">${wrSure===m.id?t("Sure? Delete"):t("Delete")}</button></div>`:"");
  html+=`<div class="m${mine?" mine":""}${tome?" tome":""}">${head}${body}</div>`;
  lastUser=m.user;
 }
 box.innerHTML=html||'<div class="empty" style="margin:auto">'+t("No messages yet. Say hi.")+'</div>';
 const e2=wrEdit&&document.getElementById("ed-"+wrEdit.id);if(e2&&!e2.dataset.f){e2.dataset.f=1;e2.focus();e2.setSelectionRange(e2.value.length,e2.value.length);}
 if(forceBottom||near)box.scrollTop=box.scrollHeight;
}
$("msgs").onclick=async e=>{
 const b=e.target.closest("button[data-a]");if(!b)return;const a=b.dataset.a,id=+b.dataset.id;
 if(a==="edit"){const m=wrMsgs.find(x=>x.id===id);if(m){wrEdit={id,text:m.text};wrSure=null;wrRender();}}
 else if(a==="cancel"){wrEdit=null;wrRender();}
 else if(a==="save"){const t=$("ed-"+id).value.trim();if(!t)return;
  const r=await post("/api/warroom/"+id,{text:t},"PATCH");const j=await r.json();
  if(r.ok){wrEdit=null;await wrPoll();}else $("wmsg").textContent=j.error||"Error";}
 else if(a==="del"){
  if(wrSure!==id){wrSure=id;wrRender();setTimeout(()=>{if(wrSure===id){wrSure=null;wrRender();}},3000);return;}
  wrSure=null;const r=await post("/api/warroom/"+id,null,"DELETE");if(r.ok)await wrPoll();else{const j=await r.json();$("wmsg").textContent=j.error||"Error";}}
};
function wrBadge(){
 const n=wrSeen===null?0:wrMsgs.filter(m=>m.id>wrSeen&&m.user!==wrMe).length;
 const b=$("wbadge");b.style.display=n&&page()!=="warroom"?"":"none";b.textContent=n>99?"99+":n;
}
function wrMarkRead(){if(wrMsgs.length)wrSeen=wrMsgs[wrMsgs.length-1].id;wrUnreadTitle=0;if(page()==="warroom")document.title=t(TITLES.warroom)+" · "+SHOP;wrBadge();}
async function wrPoll(){
 if(!isAdmin)return;
 try{const r=await fetch("/api/warroom?after="+wrLast+"&rev="+wrRev);if(!r.ok)return;const j=await r.json();
  wrMe=j.me;const first=!wrStarted;wrStarted=true;wrRev=j.rev;
  wrStyles=j.styles||{};wrPeople=j.people||[];
  $("onl").innerHTML=j.online.map(n=>`<span><i></i>${nameHtml(n,false)}</span>`).join("")+Object.entries(j.away||{}).map(([n,ts])=>`<span style="opacity:.8" title="${esc(full(ts))}">${esc(n)}: ${t("last seen")} ${esc(ago(ts))}</span>`).join("");
  $("typing").textContent=j.typing&&j.typing.length?j.typing.join(", ")+" "+(j.typing.length>1?t("are typing..."):t("is typing...")):"";
  if(j.reset){
   const known=new Set(wrMsgs.map(m=>m.id));
   const fresh=first?[]:j.messages.filter(m=>!known.has(m.id)&&m.id>wrLast);
   wrMsgs=j.messages;wrLast=wrMsgs.length?Math.max(wrLast,wrMsgs[wrMsgs.length-1].id):wrLast;
   if(first&&page()!=="warroom")wrSeen=wrLast;if(wrSeen===null)wrSeen=0;
   if(fresh.length)wrAlert(fresh);
   if(page()==="warroom"){wrRender(first);if(!document.hidden)wrMarkRead();}else wrBadge();
  }else if(j.messages.length){
   wrMsgs=wrMsgs.concat(j.messages);wrLast=wrMsgs[wrMsgs.length-1].id;
   wrAlert(j.messages);
   if(page()==="warroom"){wrRender();if(!document.hidden)wrMarkRead();}else wrBadge();}
 }catch(e){}
}
function wrLoop(){wrPoll().finally(()=>setTimeout(wrLoop,document.hidden?4000:page()==="warroom"?1500:4000));}
async function wrSend(){
 const txt=$("wt").value.trim();if(!txt)return;$("wsend").disabled=true;$("wmsg").textContent="";
 try{const r=await post("/api/warroom",{text:txt});const j=await r.json();
  if(r.ok){$("wt").value="";$("wt").style.height="";await wrPoll();$("msgs").scrollTop=$("msgs").scrollHeight;}
  else $("wmsg").textContent=j.error||"Error";
 }catch(e){$("wmsg").textContent=t("Could not reach the server.");}
 $("wsend").disabled=false;$("wt").focus();
}
$("wform").onsubmit=e=>{e.preventDefault();wrSend();};
function suggList(){
 const ta=$("wt"),before=ta.value.slice(0,ta.selectionStart),m=before.match(/(^|[^\w@])@([\w-]*)$/);
 if(!m)return null;const q=m[2].toLowerCase();
 const list=wrPeople.filter(n=>n!==wrMe&&n.toLowerCase().startsWith(q));
 return list.length?{list,start:before.length-m[2].length-1}:null;}
function suggUi(){const s=suggList(),box=$("wsugg");
 if(!s){box.hidden=true;box.innerHTML="";return;}
 box.hidden=false;box.innerHTML=s.list.map(n=>`<button type="button" data-n="${esc(n)}">${wrStyles[n]&&wrStyles[n].emoji?esc(wrStyles[n].emoji)+" ":""}@${esc(n)}</button>`).join("");}
function suggPick(n){const ta=$("wt"),s=suggList();if(!s)return;
 const after=ta.value.slice(ta.selectionStart);ta.value=ta.value.slice(0,s.start)+"@"+n+" "+after;
 const pos=s.start+n.length+2;ta.setSelectionRange(pos,pos);ta.focus();suggUi();}
$("wsugg").onclick=e=>{const b=e.target.closest("[data-n]");if(b)suggPick(b.dataset.n);};
$("wt").onkeydown=e=>{
 if((e.key==="Tab"||e.key==="Enter")&&!e.shiftKey&&!e.isComposing){const s=suggList();if(s){e.preventDefault();suggPick(s.list[0]);return;}}
 if(e.key==="Enter"&&!e.shiftKey&&!e.isComposing){e.preventDefault();wrSend();}};
$("wt").onkeyup=e=>{if(!["Enter","Tab"].includes(e.key))suggUi();};
$("wt").onclick=suggUi;
let typedAt=0;
$("wt").oninput=()=>{const ta=$("wt");ta.style.height="auto";ta.style.height=Math.min(120,ta.scrollHeight)+"px";
 if(ta.value.trim()&&Date.now()-typedAt>2500){typedAt=Date.now();post("/api/warroom/typing").catch(()=>{});}};
setTimeout(()=>{if(noteOn&&typeof Notification!=="undefined"&&Notification.permission==="granted")pushSubscribe();},1500);setTimeout(wrLoop,800);

// ---------- Mindmap ----------
const MMC={yellow:"#ffe27a",green:"#9be8c0",blue:"#9cc9ff",pink:"#ffb3c7",orange:"#ffc58a",purple:"#d4b8ff"},MMCN=Object.keys(MMC);
const MMTAGS=["","Important","Idea","Todo","Done"],mmTag=x=>x?t(x):"";
let mmRev=-1,mmNotes=[],mmLinks=[],mmColor="yellow",mmLink=false,mmPick=null,mmDrag=null;
const mmEls={},mmDirty=new Set(),mmTimers={};
const mmGet=id=>mmNotes.find(n=>n.id===id);
function mmSw(){$("mmsw").innerHTML=MMCN.map(k=>`<i data-c="${k}" class="${k===mmColor?"on":""}" style="background:${MMC[k]}" title="${k}"></i>`).join("");}
$("mmsw").onclick=e=>{const c=e.target.dataset.c;if(c){mmColor=c;mmSw();}};
async function mmPoll(force){
 if(!isAdmin||mmDrag!==null)return;
 try{const r=await fetch("/api/mindmap?rev="+(force?-1:mmRev));if(!r.ok)return;const j=await r.json();if(j.same)return;
  mmRev=j.rev;mmMerge(j.notes,j.links);}catch(e){}
}
function mmBusy(id){const el=mmEls[id];return mmDirty.has(id)||mmDrag===id||(el&&el.contains(document.activeElement));}
function mmMerge(notes,links){
 const local=Object.fromEntries(mmNotes.map(n=>[n.id,n]));
 mmNotes=notes.map(n=>mmBusy(n.id)&&local[n.id]?{...n,text:local[n.id].text,x:local[n.id].x,y:local[n.id].y}:n);
 mmLinks=links;mmRender();
}
const mmTime=iso=>{const d=new Date(iso);return d.toDateString()===new Date().toDateString()?hhmm(iso):d.toLocaleDateString(LOC(),{day:"numeric",month:"short"});};
function mmMake(n){
 const id=n.id,el=document.createElement("div");el.className="note";el.dataset.id=id;
 el.innerHTML=`<span class="tag" hidden></span><div class="h"><span class="who"></span><span class="nb"><button data-a="tag" title="${t("Label")}">#</button><button data-a="col" title="${t("Colour")}">●</button><button data-a="del" title="${t("Delete")}">✕</button></span></div><textarea rows="2" spellcheck="false" maxlength="1000"></textarea>`;
 const ta=el.querySelector("textarea"),h=el.querySelector(".h");
 ta.addEventListener("input",()=>{const m=mmGet(id);if(!m)return;m.text=ta.value;mmFit(ta);mmDraw();mmDirty.add(id);
  clearTimeout(mmTimers[id]);mmTimers[id]=setTimeout(async()=>{try{await post("/api/mindmap/notes/"+id,{text:m.text},"PATCH");}catch(e){}mmDirty.delete(id);},500);});
 ta.addEventListener("blur",()=>{if(mmDirty.has(id)){clearTimeout(mmTimers[id]);const m=mmGet(id);if(m)post("/api/mindmap/notes/"+id,{text:m.text},"PATCH").finally(()=>mmDirty.delete(id));}});
 el.querySelector(".nb").addEventListener("click",async e=>{
  const b=e.target.closest("button");if(!b)return;const m=mmGet(id);if(!m)return;
  if(b.dataset.a==="tag"){m.tag=MMTAGS[(MMTAGS.indexOf(m.tag||"")+1)%MMTAGS.length];mmRender();post("/api/mindmap/notes/"+id,{tag:m.tag},"PATCH");}
  else if(b.dataset.a==="col"){m.color=MMCN[(MMCN.indexOf(m.color)+1)%MMCN.length];mmRender();post("/api/mindmap/notes/"+id,{color:m.color},"PATCH");}
  else if(b.dataset.a==="del"){
   if(!b.classList.contains("sure")){b.classList.add("sure");b.textContent=t("Delete?");setTimeout(()=>{b.classList.remove("sure");b.textContent="✕";},3000);return;}
   mmNotes=mmNotes.filter(x=>x.id!==id);mmLinks=mmLinks.filter(l=>!l.includes(id));mmRender();await post("/api/mindmap/notes/"+id,null,"DELETE");}
 });
 let sx,sy,ox,oy;
 h.addEventListener("pointerdown",e=>{if(e.target.closest(".nb"))return;const m=mmGet(id);if(!m)return;
  if(mmLink){e.preventDefault();
   if(mmPick===null)mmPick=id;
   else if(mmPick!==id){const a=mmPick;mmPick=null;if(!mmLinks.some(l=>l.includes(a)&&l.includes(id)))mmLinks.push([a,id]);post("/api/mindmap/links",{a,b:id});}
   else mmPick=null;
   mmRender();return;}
  h.setPointerCapture(e.pointerId);mmDrag=id;el.classList.add("drag");sx=e.clientX;sy=e.clientY;ox=m.x;oy=m.y;});
 h.addEventListener("pointermove",e=>{if(mmDrag!==id)return;const m=mmGet(id);if(!m)return;
  m.x=Math.max(0,Math.min(1800-230,ox+e.clientX-sx));m.y=Math.max(0,Math.min(1200-90,oy+e.clientY-sy));el.style.left=m.x+"px";el.style.top=m.y+"px";mmDraw();});
 h.addEventListener("pointerup",()=>{if(mmDrag!==id)return;mmDrag=null;el.classList.remove("drag");const m=mmGet(id);if(m)post("/api/mindmap/notes/"+id,{x:m.x,y:m.y},"PATCH");});
 h.addEventListener("pointercancel",()=>{mmDrag=null;el.classList.remove("drag");});
 return el;
}
function mmFit(ta){ta.style.height="auto";ta.style.height=ta.scrollHeight+"px";}
function mmRender(){
 const cv=$("mmcv"),ids=new Set(mmNotes.map(n=>n.id));
 for(const k in mmEls){if(!ids.has(+k)){mmEls[k].remove();delete mmEls[k];}}
 mmNotes.forEach(n=>{
  let el=mmEls[n.id];if(!el){el=mmMake(n);cv.appendChild(el);mmEls[n.id]=el;}
  if(mmDrag!==n.id){el.style.left=n.x+"px";el.style.top=n.y+"px";}
  el.style.background=MMC[n.color]||MMC.yellow;el.style.setProperty("--r",(n.r||0)+"deg");
  el.classList.toggle("pick",mmPick===n.id);
  const tag=el.querySelector(".tag");tag.hidden=!n.tag;tag.textContent=mmTag(n.tag);
  el.querySelector(".who").innerHTML=`<b>${esc(n.by)}</b> · ${esc(mmTime(n.time))}`;
  const ta=el.querySelector("textarea");if(ta.value!==n.text&&document.activeElement!==ta){ta.value=n.text;}mmFit(ta);
 });
 mmDraw();
}
function mmCenter(n){const el=mmEls[n.id];return {x:n.x+(el?el.offsetWidth:218)/2,y:n.y+(el?el.offsetHeight:110)/2};}
function mmDraw(){
 let s="";
 mmLinks.forEach(([a,b],i)=>{const A=mmGet(a),B=mmGet(b);if(!A||!B)return;const p=mmCenter(A),q=mmCenter(B),dx=Math.max(60,Math.abs(q.x-p.x)/2),sg=q.x>p.x?1:-1;
  s+=`<path data-a="${a}" data-b="${b}" d="M${p.x},${p.y} C${p.x+sg*dx},${p.y} ${q.x-sg*dx},${q.y} ${q.x},${q.y}"/><circle cx="${q.x}" cy="${q.y}" r="4"/>`;});
 $("mml").innerHTML=s;
}
$("mml").addEventListener("click",e=>{const p=e.target.closest("path[data-a]");if(!p||!mmLink)return;
 const a=+p.dataset.a,b=+p.dataset.b;mmLinks=mmLinks.filter(l=>!(l.includes(a)&&l.includes(b)));mmDraw();post("/api/mindmap/links?a="+a+"&b="+b,null,"DELETE");});
$("mmlink").onclick=()=>{mmLink=!mmLink;mmPick=null;$("mmlink").classList.toggle("on",mmLink);$("mml").classList.toggle("on",mmLink);
 $("mmhint").textContent=mmLink?t("Connect mode: click the top bar of one note, then another. Click a line to remove it."):t("Drag a note by its top bar. Click the text to edit.");mmRender();};
$("mmadd").onclick=async()=>{
 const b=$("mmboard");
 const body={x:b.scrollLeft+60+Math.random()*140,y:b.scrollTop+50+Math.random()*90,r:Math.round((Math.random()*3-1.5)*10)/10,color:mmColor,text:""};
 try{const r=await post("/api/mindmap/notes",body);const j=await r.json();
  if(!r.ok){$("mmhint").textContent=j.error||"Error";return;}
  mmNotes.push(j.note);mmRender();const ta=mmEls[j.note.id].querySelector("textarea");ta.focus();}catch(e){}
};
window.addEventListener("resize",()=>{if(page()==="mindmap")mmDraw();});
setInterval(()=>{if(page()==="mindmap"&&!document.hidden)mmPoll(false);},2000);
mmSw();


// ================= app install + service worker =================
let installEv=null;
const standalone=()=>window.matchMedia("(display-mode: standalone)").matches||navigator.standalone===true;
if("serviceWorker" in navigator&&window.isSecureContext)navigator.serviceWorker.register("/sw.js").catch(()=>{});
const isIOS=/iphone|ipad|ipod/i.test(navigator.userAgent)||(navigator.platform==="MacIntel"&&navigator.maxTouchPoints>1);
function installUi(){$("install").hidden=standalone()||!(installEv||isIOS);}
window.addEventListener("beforeinstallprompt",e=>{e.preventDefault();installEv=e;installUi();});
window.addEventListener("appinstalled",()=>{installEv=null;installUi();});
$("install").onclick=async()=>{
 if(installEv){installEv.prompt();await installEv.userChoice.catch(()=>{});installEv=null;installUi();return;}
 toast(t("Install the app"),t("On iPhone/iPad: tap the Share button in Safari, then \"Add to Home Screen\"."));
};
installUi();

// ================= start =================
let rt;window.addEventListener("resize",()=>{clearTimeout(rt);rt=setTimeout(()=>{if(window.__last){delete seen.c1;delete seen.c2;delete seen.cal;render(window.__last);}},150);});
window.__render=d=>{window.__last=d;render(d);};
document.addEventListener("click",e=>{
 const c=e.target.closest("[data-copy]");if(c){e.preventDefault();copyText(c.dataset.copy,c);return;}
 const b=e.target.closest("[data-buyer]");if(b){e.preventDefault();e.stopPropagation();openBuyer(b.dataset.buyer);return;}
 const o=e.target.closest("[data-oid]");if(o){openOrder(o.dataset.oid);return;}
 const d=e.target.closest("#cal .cd[data-day]");if(d){loadDay(d.dataset.day);}
});
document.addEventListener("visibilitychange",()=>{if(!document.hidden)load(true);});
$("logo").textContent=(SHOP.trim().slice(0,1)||"N");
PREFS.bg=lsGet("bg","");applyBg();PREFS.accent=lsGet("accent","");PREFS.sound=lsGet("sound","ding")||"ding";PREFS.lang=lsGet("lang","");PREFS.currency=CURSEL;
document.body.classList.toggle("hide",HIDE);
newsNav();
applyAccent();translateStatic();settingsUi();setTitle();
show();load(true);setInterval(load,5000);
setInterval(()=>{if(window.__last&&!document.hidden)render(window.__last);},30000);

</script></body></html>"""


# ======================= command line =======================

def main():
    global DEMO
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", nargs="?", default="run", choices=["run", "demo", "adduser"])
    ap.add_argument("name", nargs="?")
    ap.add_argument("--admin", action="store_true")
    ap.add_argument("--show", action="store_true", help="show the password while typing")
    a = ap.parse_args()

    if a.cmd == "adduser":
        if not a.name:
            raise SystemExit("Usage: py dashboard.py adduser NAME [--admin]")
        if a.show:
            pw = input("Password (8+ characters, you can see it): ")
            again = pw
        else:
            print("Type the password and press Enter. You will NOT see anything while typing - that is normal.")
            print("(Or run again with --show to see what you type.)")
            pw = getpass.getpass("Password (8+ characters): ")
            again = getpass.getpass("Repeat the password: ")
        if pw != again:
            raise SystemExit("The passwords do not match.")
        try:
            add_user(a.name, pw, "admin" if a.admin else "viewer")
        except ValueError as e:
            raise SystemExit(str(e))
        print(f"User '{a.name}' saved ({'admin' if a.admin else 'viewer'}).")
        return

    app.secret_key = _secret_key()
    if a.cmd == "demo":
        DEMO = True
        _demo_users["demo"] = {"name": "demo", "role": "admin", "hash": generate_password_hash("demodemo")}
        print("DEMO mode with fake data. Log in with  demo / demodemo")
    else:
        if not load_users():
            raise SystemExit("No users yet. Create the first one:  py dashboard.py adduser YOURNAME --admin")
        threading.Thread(target=poll_loop, daemon=True).start()

    print(f"Dashboard on http://localhost:{PORT}  (stop with Ctrl+C)")
    try:
        from waitress import serve
        serve(app, host=HOST, port=PORT, threads=8)
    except ImportError:
        print("Tip: py -m pip install waitress   (a sturdier server for many visitors)")
        app.run(host=HOST, port=PORT, threaded=True)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nStopped.")
