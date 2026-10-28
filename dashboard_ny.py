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
import fnmatch
import shutil
import platform
import ctypes
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
import zipfile
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
PREVIEW = False   # the new design running next to the old dashboard: no pushes, no backups, no programs
ORDERS_DB, COSTS_FILE, PREFS_FILE = Path("orders_db.json"), Path("costs.json"), Path("prefs.json")
PRESENCE_FILE, DEVICES_FILE = Path("presence.json"), Path("devices.json")
CURRENCIES = ("DKK", "USD", "EUR")
SOUNDS = ("ding", "bell", "pop", "chime", "none")
NOTIFY_KINDS = ("warroom", "orders", "reviews", "keys")
OVERVIEW_TILES = ("today", "month", "all", "avg", "stock", "profit", "taxpot", "lastorder", "revrate", "pending", "reviews", "keys", "latest", "chart", "stockp", "status", "others", "stockval", "forecast")
NAV_PAGES = ("overview", "sales", "history", "orders", "stock", "reviews", "keys", "warroom", "mindmap", "profit", "programs", "server", "users", "settings", "news")
BACKGROUNDS = ("", "dots", "grid", "waves", "aurora", "diagonal")
DEFAULT_PREFS = {"lang": "", "accent": "", "currency": "", "sound": "ding", "gross": None, "tax": 37,
                 "emoji": "", "color": "", "bg": "", "hide": [], "menu": [], "pins": [], "payout": 5, "ovorder": [],
                 "notify": {"warroom": True, "orders": True, "reviews": True, "keys": True}}

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
    MAX_CONTENT_LENGTH=6 * 1024 * 1024,   # room for a 5 MB War-Room picture; everything else is tiny
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
_pres_c = {}                      # device id -> last seen, so a message is still pushed to your phone while the computer is open
_seen_saved = {}
_typing = {}


def _cid():
    c = request.headers.get("X-Client", "")[:40]
    return c if re.fullmatch(r"[A-Za-z0-9_-]{6,40}", c) else ""


def touch(name):
    now = time.time()
    _presence[name] = now
    if _cid():
        _pres_c[_cid()] = now
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
    for k in ("menu", "pins"):
        if isinstance(p.get(k), list):
            out[k] = [x for i, x in enumerate(p[k]) if x in NAV_PAGES and x not in p[k][:i]]
    if isinstance(p.get("payout"), (int, float)) and not isinstance(p.get("payout"), bool) and 0 <= p["payout"] <= 90:
        out["payout"] = int(p["payout"])
    if isinstance(p.get("ovorder"), list):
        out["ovorder"] = [x for i, x in enumerate(p["ovorder"]) if x in OVERVIEW_TILES and x not in p["ovorder"][:i]]
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
    from stock_board import CATEGORIES, fetch_offers
    offers = []
    for key in CATEGORIES:            # items AND accounts, whatever the Discord stock board is set to show
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
                    msg = f"API error {code}" if code else type(e).__name__
                    st = _status.setdefault(name, {"ok": None, "err": "", "fails": 0})
                    st["err"], st["fails"] = msg, st["fails"] + 1
                    if st["fails"] >= 3:          # one hiccup from Eldorado is not shown, three in a row is
                        _cache["errors"][name] = msg
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
    return Response(PAGE.replace("__SHOP__", SHOP_NAME.replace("<", "").replace(">", "")).replace("__PREVIEW__", "1" if PREVIEW else "0"),
                    mimetype="text/html")


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
        d["unitcosts"] = load_unitcosts()
        d["alarms"] = prog_alarms()
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
        for k in ("menu", "pins"):
            if isinstance(j.get(k), list):
                p[k] = [x for i, x in enumerate(j[k]) if x in NAV_PAGES and x not in j[k][:i]]
        if isinstance(j.get("payout"), (int, float)) and not isinstance(j.get("payout"), bool) and 0 <= j["payout"] <= 90:
            p["payout"] = int(j["payout"])
        if isinstance(j.get("ovorder"), list):
            p["ovorder"] = [x for i, x in enumerate(j["ovorder"]) if x in OVERVIEW_TILES and x not in j["ovorder"][:i]]
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


def send_push(title, body, skip_user=None, skip_present=True, webpush_fn=None, kind="warroom", url="/#warroom", only_user=None, skip_dev=None):
    """Sends a notification to every subscribed admin device that wants this kind. Dead subscriptions are removed.
    title/body can be a text or {"da": ..., "en": ...} (each person gets the language they chose)."""
    if DEMO or PREVIEW:
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
    if not subs:
        print(f"Push {kind}: nobody has turned notifications on yet", flush=True)
    for s in subs:
        skip = skip_user if isinstance(skip_user, (set, frozenset, list, tuple)) else {skip_user}
        if s["user"] in skip or s["user"] not in admins or (only_user and s["user"] != only_user):
            continue
        who = f"{s['user']}@{(s.get('cid') or 'old-device')[:6]}"
        if skip_dev and s["user"] == skip_dev[0] and s.get("cid") and s.get("cid") == skip_dev[1]:
            print(f"Push {kind}: skipped {who} (the device that sent it)", flush=True)
            continue
        if skip_present and s.get("cid") and now - _pres_c.get(s["cid"], 0) < 20:
            print(f"Push {kind}: skipped {who} (page is open there)", flush=True)
            continue
        pr = prefs_of(s["user"])
        if not pr["notify"].get(kind, True):
            print(f"Push {kind}: skipped {who} ({kind} is switched off in Settings)", flush=True)
            continue
        lang = pr["lang"] or "da"
        payload = json.dumps({"title": str(_pick(title, lang)), "body": str(_pick(body, lang))[:140], "url": url, "tag": kind})
        try:
            webpush_fn(subscription_info=s["sub"], data=payload, vapid_private_key=str(VAPID_FILE),
                       vapid_claims={"sub": PUSH_CONTACT}, ttl=3600, timeout=10)
            print(f"Push {kind}: sent to {who}", flush=True)
        except WebPushException as e:
            code = getattr(getattr(e, "response", None), "status_code", None)
            print(f"Push {kind}: refused by {who} ({code or type(e).__name__})", flush=True)
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
        subs.append({"user": me, "sub": clean, "cid": _cid(), "created": datetime.now(timezone.utc).isoformat()})
        save_subs(subs)
    return jsonify(ok=True)


@app.route("/api/push/test", methods=["POST"])
def api_push_test():
    """Sends a test notification to the logged-in person's own devices and says what happened per device."""
    bad = api_guard(admin=True)
    if bad:
        return bad
    if DEMO:
        return jsonify(ok=True, devices=1, results=["demo: nothing is sent"])
    if not push_available():
        return jsonify(ok=False, error="pywebpush is not installed on the VPS. Run opdater.bat and restart.")
    from pywebpush import WebPushException, webpush
    me = current_user()["name"]
    with _push_lock:
        mine = [s for s in load_subs() if s["user"] == me]
    if not mine:
        return jsonify(ok=False, error="No device is registered for you. Turn notifications on from the installed app.")
    lang = prefs_of(me)["lang"] or "da"
    payload = json.dumps({"title": "Nexo-Shop", "body": "Test: det virker!" if lang == "da" else "Test: it works!", "url": "/#settings", "tag": "test"})
    results, dead = [], []
    for s in mine:
        host = re.sub(r"^https://([^/]+)/.*$", r"\1", s["sub"]["endpoint"])
        try:
            webpush(subscription_info=s["sub"], data=payload, vapid_private_key=str(VAPID_FILE), vapid_claims={"sub": PUSH_CONTACT}, ttl=600, timeout=10)
            results.append(f"{host}: sent")
        except WebPushException as e:
            code = getattr(getattr(e, "response", None), "status_code", None)
            results.append(f"{host}: refused ({code or type(e).__name__})")
            if code in (404, 410):
                dead.append(s["sub"]["endpoint"])
        except Exception as e:
            results.append(f"{host}: error ({type(e).__name__})")
    if dead:
        with _push_lock:
            save_subs([s for s in load_subs() if s["sub"]["endpoint"] not in dead])
    return jsonify(ok=any(r.endswith("sent") for r in results), devices=len(mine), results=results)


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
        if _cid():
            _pres_c[_cid()] = now
        if request.method == "POST":
            text = str((request.get_json(silent=True) or {}).get("text", "")).replace("\r\n", "\n").strip()
            msg, err = _wr_add(me, text, None, now)
            if err:
                return jsonify(error=err[0]), err[1]
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


WR_FILES = Path(__file__).resolve().parent / "warroom_files"
WR_FILE_MAX = 5 * 1024 * 1024
WR_FILE_RE = re.compile(r"^[0-9a-f]{32}\.(png|jpg|gif|webp|pdf)$")
WR_MIME = {"png": "image/png", "jpg": "image/jpeg", "gif": "image/gif", "webp": "image/webp", "pdf": "application/pdf"}


def _wr_kind(data):
    """Only images and PDFs, decided by what the file really is and not by its name."""
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if data[:3] == b"\xff\xd8\xff":
        return "jpg"
    if data[:4] == b"GIF8":
        return "gif"
    if data[:4] == b"RIFF" and data[8:12] == b"WEBP":
        return "webp"
    if data[:5] == b"%PDF-":
        return "pdf"
    return None


def _wr_add(me, text, file, now):
    """Adds a War-Room message (caller holds _wr_lock). Returns (msg, None) or (None, (error, status))."""
    if not text and not file:
        return None, ("Empty message.", 400)
    if len(text) > WARROOM_MAX_LEN:
        return None, (f"Max {WARROOM_MAX_LEN} characters.", 400)
    if now - _last_post.get(me, 0) < 0.4:
        return None, ("Slow down a little.", 429)
    _last_post[me] = now
    msg = {"id": _wr["next"], "user": me, "text": text, "time": datetime.now(timezone.utc).isoformat()}
    if file:
        msg["file"] = file
    _wr["next"] += 1
    _wr["msgs"].append(msg)
    del _wr["msgs"][:-WARROOM_KEEP]
    _wr_gc()
    names = [x["name"] for x in load_users().values() if x["role"] == "admin"]
    tagged = {n for n in names if n != me and re.search(r"(?<![\w@])@" + re.escape(n) + r"(?![\w-])", text, re.I)}
    msg["mentions"] = sorted(tagged)
    _wr_save()
    shown = text or ("📎 " + (file or {}).get("name", ""))
    threading.Thread(target=send_push, args=("War-Room · " + me, shown), kwargs={"skip_user": tagged, "skip_dev": (me, _cid())}, daemon=True).start()
    for n in tagged:
        threading.Thread(target=send_push, args=({"da": f"{me} nævnte dig", "en": f"{me} mentioned you"}, shown),
                         kwargs={"only_user": n}, daemon=True).start()
    return msg, None


def _wr_gc():
    """Deletes uploaded files no message points at any more (deleted or pushed out of the last 500)."""
    if DEMO or not WR_FILES.is_dir():
        return
    keep = {m["file"]["id"] for m in _wr["msgs"] if isinstance(m.get("file"), dict)}
    for p in WR_FILES.iterdir():
        if p.is_file() and WR_FILE_RE.match(p.name) and p.name not in keep:
            try:
                p.unlink()
            except OSError:
                pass


@app.route("/api/warroom/upload", methods=["POST"])
def api_warroom_upload():
    bad = api_guard(admin=True)
    if bad:
        return bad
    f = request.files.get("file")
    if not f:
        return jsonify(error="No file."), 400
    data = f.read(WR_FILE_MAX + 1)
    if len(data) > WR_FILE_MAX:
        return jsonify(error="The file is too big (max 5 MB)."), 413
    ext = _wr_kind(data)
    if not ext:
        return jsonify(error="Only pictures (png, jpg, gif, webp) and PDF files."), 400
    me = current_user()["name"]
    text = str(request.form.get("text", "")).replace("\r\n", "\n").strip()
    clean = re.sub(r"[^\w .()-]", "_", os.path.basename(f.filename or "file"))[:60] or "file"
    fid = uuid.uuid4().hex + "." + ext
    with _wr_lock:
        _wr_load()
        if not DEMO:
            WR_FILES.mkdir(exist_ok=True)
            tmp = WR_FILES / (fid + ".tmp")
            tmp.write_bytes(data)
            tmp.replace(WR_FILES / fid)
        else:
            _demo_files[fid] = data
        msg, err = _wr_add(me, text, {"id": fid, "name": clean, "kind": "pdf" if ext == "pdf" else "image", "size": len(data)}, time.time())
        if err:
            if not DEMO:
                try:
                    (WR_FILES / fid).unlink()
                except OSError:
                    pass
            return jsonify(error=err[0]), err[1]
    return jsonify(ok=True, id=msg["id"])


_demo_files = {}


@app.route("/api/warroom/file/<fid>")
def api_warroom_file(fid):
    bad = api_guard(admin=True)
    if bad:
        return bad
    if not WR_FILE_RE.match(fid):
        return jsonify(error="No such file."), 404
    if DEMO:
        data = _demo_files.get(fid)
    else:
        p = WR_FILES / fid
        data = p.read_bytes() if p.is_file() else None
    if data is None:
        return jsonify(error="No such file."), 404
    ext = fid.rsplit(".", 1)[1]
    h = {"Cache-Control": "private, max-age=86400", "X-Content-Type-Options": "nosniff",
         "Content-Security-Policy": "default-src 'none'; img-src 'self'; style-src 'unsafe-inline'; sandbox"}
    h["Content-Disposition"] = ("attachment" if ext == "pdf" else "inline") + f'; filename="{fid}"'
    return Response(data, mimetype=WR_MIME[ext], headers=h)


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
            _wr_gc()
        else:
            text = str((request.get_json(silent=True) or {}).get("text", "")).replace("\r\n", "\n").strip()
            if not text and not msg.get("file"):
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


# ======================= programs: the dashboard starts and watches the other scripts =======================

import atexit
import collections
import subprocess

HERE = Path(__file__).resolve().parent
PROGRAM_LIST = [("orders", "order_alerts.py", []), ("reviews", "review_alerts.py", []), ("stock", "stock_board.py", []),
                ("stats", "stats_board.py", []), ("offer", "offer.py", ["auto"])]
_progs = {}                       # name -> _Prog (only when the dashboard manages the programs)
_prog_stop = threading.Event()
_prog_lock = threading.Lock()
_prog_managed = False


class _Prog:
    def __init__(self, name, script, args):
        self.name, self.script, self.args = name, script, list(args)
        self.proc = None
        self.lines = collections.deque(maxlen=800)
        self.seq = 0
        self.started = None
        self.last_out = None
        self.restarts = 0
        self.code = None
        self.state = "starting"
        self.restart_now = False
        self.wake = threading.Event()
        self.fake = False
        self.cmd = None               # full command for non-python programs (Caddy)
        self.cwd = None


def _prog_add(p, text):
    with _prog_lock:
        p.seq += 1
        p.lines.append((p.seq, time.time(), text))
        p.last_out = time.time()


def _caddy_find():
    """Finds caddy.exe (HTTPS) and the folder with its Caddyfile. CADDY_DIR in .env points at it; otherwise next to or beside the dashboard."""
    names = ("caddy.exe", "caddy")
    dirs = [Path(os.getenv("CADDY_DIR"))] if os.getenv("CADDY_DIR") else []
    dirs += [HERE, HERE / "caddy", HERE.parent / "caddy"]
    for d in dirs:
        for n in names:
            exe = d / n
            if exe.is_file() and (d / "Caddyfile").is_file():
                return exe, d
    return None, None


def _prog_run(p):
    path = HERE / p.script
    if p.cmd is None and not path.exists():
        p.state = "missing"
        _prog_add(p, f"{p.script} not found next to dashboard.py")
        return
    env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONUNBUFFERED="1")
    fast = 0
    while not _prog_stop.is_set():
        began = time.time()
        try:
            proc = subprocess.Popen(p.cmd or [sys.executable, "-u", str(path), *p.args], cwd=p.cwd or str(HERE), env=env, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        except OSError as e:
            _prog_add(p, f"could not start: {e}")
            p.state = "crashed"
            _prog_stop.wait(30)
            continue
        p.proc, p.started, p.code, p.state = proc, time.time(), None, "running"
        _prog_add(p, "started")
        for line in proc.stdout:
            text = line.rstrip()
            _prog_add(p, text)
            print(f"[{p.name:<8}] {text}", flush=True)
        code = proc.wait()
        p.code, p.proc = code, None
        if _prog_stop.is_set():
            break
        manual, p.restart_now = p.restart_now, False
        fast = 0 if manual else (fast + 1 if time.time() - began < 30 else 0)
        wait = 1 if manual else min(5 * 2 ** min(fast, 5), 120)
        p.restarts += 1
        p.state = "restarting" if manual else "crashed"
        _prog_add(p, f"stopped (code {code}), starting again in {wait}s")
        p.wake.wait(wait)
        p.wake.clear()


def start_programs(only=None):
    """Starts the other scripts as child programs, so  py dashboard.py  is the only thing you run."""
    global _prog_managed
    _prog_managed = True
    for name, script, args in PROGRAM_LIST:
        if only and name not in only:
            continue
        p = _progs[name] = _Prog(name, script, args)
    exe, cdir = _caddy_find()
    if exe and (not only or "https" in only):
        p = _progs["https"] = _Prog("https", exe.name, [])
        p.cmd, p.cwd = [str(exe), "run"], str(cdir)

    def go():
        for p in list(_progs.values()):
            threading.Thread(target=_prog_run, args=(p,), daemon=True).start()
            time.sleep(2)
    threading.Thread(target=go, daemon=True).start()
    atexit.register(stop_programs)


def stop_programs():
    _prog_stop.set()
    for p in list(_progs.values()):
        pr = p.proc
        if pr is not None and pr.poll() is None:
            try:
                pr.terminate()
            except OSError:
                pass
    end = time.time() + 6
    for p in list(_progs.values()):
        pr = p.proc
        if pr is not None:
            try:
                pr.wait(max(0.1, end - time.time()))
            except Exception:
                try:
                    pr.kill()
                except OSError:
                    pass


def _demo_programs():
    if _progs:
        return
    now = time.time()
    for i, (name, script, args) in enumerate(PROGRAM_LIST):
        p = _progs[name] = _Prog(name, script, args)
        p.fake, p.state, p.started, p.restarts = True, "running", now - 3600 * (5 + i), (2 if name == "stock" else 0)
        for k, text in enumerate([f"Started. Checking every 60 seconds.", "No new orders.", "No new orders.", "Checked, nothing changed."]):
            p.seq += 1
            p.lines.append((p.seq, now - 600 + k * 120, text))
        p.last_out = now - (40 + i * 70)
    _progs["reviews"].lines.append((99, now - 20, "1 new review (Positive)"))
    _progs["reviews"].last_out = now - 20


@app.route("/api/programs")
def api_programs():
    bad = api_guard(admin=True)
    if bad:
        return bad
    if DEMO:
        _demo_programs()
    now = time.time()
    rows = []
    for p in _progs.values():
        pr = p.proc
        running = p.fake and p.state == "running" or (pr is not None and pr.poll() is None)
        rows.append({"name": p.name, "script": p.script, "running": bool(running), "state": p.state if not running else "running",
                     "pid": None if p.fake else (pr.pid if pr is not None else None),
                     "uptime": int(now - p.started) if running and p.started else 0,
                     "quiet": int(now - p.last_out) if p.last_out else None, "restarts": p.restarts, "code": p.code})
    return jsonify(managed=bool(_progs), programs=rows)


@app.route("/api/programs/<name>/restart", methods=["POST"])
def api_program_restart(name):
    bad = api_guard(admin=True)
    if bad:
        return bad
    p = _progs.get(name)
    if not p:
        return jsonify(error="Unknown program."), 404
    print(f"{current_user()['name']} restarted {name}.", flush=True)
    if p.fake:
        p.started, p.state = time.time(), "running"
        _prog_add(p, "restarted")
        return jsonify(ok=True)
    p.restart_now = True
    _prog_add(p, "restart requested")
    pr = p.proc
    if pr is not None and pr.poll() is None:
        try:
            pr.terminate()
        except OSError:
            pass
    else:
        p.wake.set()
    return jsonify(ok=True)


@app.route("/api/programs/<name>/log")
def api_program_log(name):
    bad = api_guard(admin=True)
    if bad:
        return bad
    p = _progs.get(name)
    if not p:
        return jsonify(error="Unknown program."), 404
    try:
        after = int(request.args.get("after", "0"))
    except ValueError:
        after = 0
    with _prog_lock:
        rows = [{"n": n, "t": datetime.fromtimestamp(ts, timezone.utc).isoformat(), "x": x[:400]} for n, ts, x in p.lines if n > after]
    return jsonify(lines=rows[-300:], last=p.seq)


# ---------- change log (from the git history of this folder) ----------

_chlog = {"at": 0, "rows": [], "head": ""}


@app.route("/api/changelog")
def api_changelog():
    bad = api_guard()
    if bad:
        return bad
    if DEMO:
        now = datetime.now(timezone.utc)
        return jsonify(head="a1b2c3d", rows=[{"date": (now - timedelta(days=i)).isoformat(), "text": t} for i, t in enumerate(
            ["Chart title follows net/gross", "Calendar: show currency next to day amounts", "History: backfill earlier cancelled orders once", "Add History page"])])
    if time.time() - _chlog["at"] > 60:
        rows, head = [], ""
        try:
            out = subprocess.run(["git", "log", "-n", "60", "--pretty=format:%cI%x09%s"], cwd=str(HERE), capture_output=True, text=True,
                                 timeout=6, encoding="utf-8", errors="replace").stdout
            for line in out.splitlines():
                d, _, s = line.partition("\t")
                if s and not s.startswith("Merge"):
                    rows.append({"date": d, "text": s[:160]})
            head = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=str(HERE), capture_output=True, text=True, timeout=4).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            pass
        _chlog.update(at=time.time(), rows=rows, head=head)
    return jsonify(rows=_chlog["rows"], head=_chlog["head"])


# ---------- own password, server page, restart ----------

START_TIME = time.time()


@app.route("/api/password", methods=["POST"])
def api_password():
    """Anyone can change their own password (the old one has to be right)."""
    bad = api_guard()
    if bad:
        return bad
    me = session.get("u")
    j = request.get_json(silent=True) or {}
    old, new = str(j.get("old", "")), str(j.get("new", ""))
    if is_blocked(me):
        return jsonify(error="Too many attempts. Try again in a few minutes."), 429
    if len(new) < 8:
        return jsonify(error="The new password must be at least 8 characters."), 400
    if len(new) > 200:
        return jsonify(error="That password is too long."), 400
    with _users_lock:
        users = load_users()
        u = users.get(me)
        if not u or not check_password_hash(u["hash"], old):
            register_fail(me)
            return jsonify(error="The old password is not right."), 400
        if old == new:
            return jsonify(error="Pick a password that is different from the old one."), 400
        u["hash"] = generate_password_hash(new)
        save_users(users)
        drop_devices(me, keep=session.get("d"))      # other devices have to log in again
    clear_fails(me)
    return jsonify(ok=True)


def _machine_mem():
    """(total, available) bytes of the machine, or (None, None)."""
    try:
        if os.name == "nt":
            class MS(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong), ("ullTotalPhys", ctypes.c_ulonglong),
                            ("ullAvailPhys", ctypes.c_ulonglong), ("ullTotalPageFile", ctypes.c_ulonglong),
                            ("ullAvailPageFile", ctypes.c_ulonglong), ("ullTotalVirtual", ctypes.c_ulonglong),
                            ("ullAvailVirtual", ctypes.c_ulonglong), ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            s = MS()
            s.dwLength = ctypes.sizeof(MS)
            ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(s))
            return int(s.ullTotalPhys), int(s.ullAvailPhys)
        info = {}
        for line in Path("/proc/meminfo").read_text().splitlines():
            k, _, v = line.partition(":")
            info[k] = int(v.split()[0]) * 1024
        return info.get("MemTotal"), info.get("MemAvailable")
    except Exception:
        return None, None


def _folder_size(p):
    n = 0
    try:
        for x in Path(p).iterdir():
            if x.is_file():
                n += x.stat().st_size
    except OSError:
        pass
    return n


_git_cache = {"at": 0, "v": None}


def _git_head():
    if time.time() - _git_cache["at"] < 120:
        return _git_cache["v"]
    v = None
    try:
        r = subprocess.run(["git", "log", "-1", "--pretty=format:%h%x09%cI%x09%s"], cwd=str(Path(__file__).resolve().parent),
                           capture_output=True, text=True, timeout=4)
        if r.returncode == 0 and r.stdout.strip():
            h, d, s = (r.stdout.strip().split("\t") + ["", ""])[:3]
            v = {"hash": h, "date": d, "subject": s[:100]}
    except Exception:
        pass
    _git_cache.update(at=time.time(), v=v)
    return v


@app.route("/api/server")
def api_server():
    bad = api_guard(admin=True)
    if bad:
        return bad
    base = Path(__file__).resolve().parent
    try:
        du = shutil.disk_usage(base)
        disk = {"total": du.total, "used": du.used, "free": du.free}
    except OSError:
        disk = None
    mt, ma = _machine_mem()
    bk = list_backups()
    progs = [p for p in _progs.values() if not p.fake]
    return jsonify(
        started=datetime.fromtimestamp(START_TIME, timezone.utc).isoformat(), uptime=int(time.time() - START_TIME),
        disk=disk, mem={"total": mt, "free": ma} if mt else None,
        data=sum((base / n).stat().st_size for n in _backup_members() if (base / n).is_file()),
        backups={"n": len(bk), "last": bk[0]["time"] if bk else None, "size": _folder_size(BACKUP_DIR)},
        files={"n": len(list(WR_FILES.iterdir())) if WR_FILES.is_dir() else 0, "size": _folder_size(WR_FILES)},
        programs={"managed": _prog_managed, "running": sum(1 for p in progs if p.state == "running"), "total": len(progs)},
        commit=_git_head(), python=platform.python_version(), system=platform.system() + " " + platform.release(),
        supervised=os.environ.get("NEXO_SUPERVISED") == "1" or DEMO, demo=DEMO)


@app.route("/api/restart", methods=["POST"])
def api_restart():
    """Stops the programs and exits with code 3. start_all.py sees that and starts everything again."""
    bad = api_guard(admin=True)
    if bad:
        return bad
    if DEMO:
        return jsonify(ok=True, demo=True)
    if os.environ.get("NEXO_SUPERVISED") != "1":
        return jsonify(error="The dashboard was not started with start_all.py, so nothing would start it again. Start it with  py start_all.py  (or the autostart)."), 400

    def go():
        time.sleep(1)
        print("Restart requested from the website.", flush=True)
        try:
            stop_programs()
        finally:
            os._exit(3)
    threading.Thread(target=go, daemon=True).start()
    return jsonify(ok=True)


# ---------- unit costs, backups and alarms ----------

UCOST_FILE = Path("unitcosts.json")
_ucost_lock = threading.Lock()


def load_unitcosts():
    if DEMO:
        return dict(_demo_ucost)
    try:
        j = json.loads(UCOST_FILE.read_text(encoding="utf-8"))
        return {str(k): float(v) for k, v in j.items() if isinstance(v, (int, float))} if isinstance(j, dict) else {}
    except (OSError, ValueError):
        return {}


@app.route("/api/unitcost", methods=["PUT"])
def api_unitcost():
    """What one unit of an offer cost you to buy in (admin). cost = null removes it."""
    bad = api_guard(admin=True)
    if bad:
        return bad
    j = request.get_json(silent=True) or {}
    title = str(j.get("title", "")).strip()[:200]
    if not title:
        return jsonify(error="Missing title."), 400
    cost = j.get("cost")
    with _ucost_lock:
        c = load_unitcosts()
        if cost is None or cost == "":
            c.pop(title, None)
        elif isinstance(cost, (int, float)) and not isinstance(cost, bool) and 0 <= cost <= 1e7:
            c[title] = round(float(cost), 4)
        else:
            return jsonify(error="Cost must be a number."), 400
        if not DEMO:
            tmp = UCOST_FILE.with_suffix(".tmp")
            tmp.write_text(json.dumps(c, ensure_ascii=False), encoding="utf-8")
            tmp.replace(UCOST_FILE)
        else:
            _demo_ucost.clear()
            _demo_ucost.update(c)
    return jsonify(ok=True)


_demo_ucost = {}

BACKUP_DIR = Path(__file__).resolve().parent / "backups"
BACKUP_KEEP = 14
# Your data. Secrets (.env, *.key, *.pem) are deliberately NOT included, so a backup is safe to download.
BACKUP_NAMES = ("ledger.json", "orders_db.json", "users.json", "devices.json", "prefs.json", "costs.json", "unitcosts.json",
                "push_subs.json", "warroom.json", "mindmap.json", "refill_log.json", "history.json", "history_backfill.done",
                "ignore_orders.txt", "additional_info.txt")
BACKUP_GLOBS = ("keys*.txt", "*_state.json")
BACKUP_RE = re.compile(r"^backup-\d{4}-\d{2}-\d{2}_\d{6}(-manual|-safety)?\.zip$")
_backup_lock = threading.Lock()


def _backup_members():
    base = Path(__file__).resolve().parent
    out = {n for n in BACKUP_NAMES if (base / n).is_file()}
    for g in BACKUP_GLOBS:
        out |= {p.name for p in base.glob(g) if p.is_file()}
    if WR_FILES.is_dir():
        out |= {"warroom_files/" + p.name for p in WR_FILES.iterdir() if p.is_file() and WR_FILE_RE.match(p.name)}
    return sorted(out)


def _backup_allowed(name):
    if name.startswith("warroom_files/"):
        return bool(WR_FILE_RE.match(name[len("warroom_files/"):]))
    return name in BACKUP_NAMES or any(fnmatch.fnmatch(name, g) for g in BACKUP_GLOBS)


def make_backup(tag=""):
    base = Path(__file__).resolve().parent
    with _backup_lock:
        BACKUP_DIR.mkdir(exist_ok=True)
        name = "backup-" + datetime.now().strftime("%Y-%m-%d_%H%M%S") + (f"-{tag}" if tag else "") + ".zip"
        tmp = BACKUP_DIR / (name + ".tmp")
        with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as z:
            for n in _backup_members():
                z.write(base / n, n)
        tmp.replace(BACKUP_DIR / name)
        # keep the newest BACKUP_KEEP automatic/manual ones (safety copies from a restore are kept a bit longer)
        old = sorted((p for p in BACKUP_DIR.glob("backup-*.zip") if BACKUP_RE.match(p.name)), key=lambda p: p.name, reverse=True)
        for p in old[BACKUP_KEEP + 5:]:
            try:
                p.unlink()
            except OSError:
                pass
    return name


def list_backups():
    if not BACKUP_DIR.is_dir():
        return []
    rows = []
    for p in sorted(BACKUP_DIR.glob("backup-*.zip"), reverse=True):
        if BACKUP_RE.match(p.name):
            st = p.stat()
            rows.append({"name": p.name, "size": st.st_size, "time": datetime.fromtimestamp(st.st_mtime, timezone.utc).isoformat()})
    return rows


def _backup_loop():
    """Once a day: if there is no backup from today yet, take one. Checked every 10 minutes (also right at start)."""
    while True:
        try:
            today = datetime.now().strftime("%Y-%m-%d")
            if not any(r["name"].startswith("backup-" + today) for r in list_backups()):
                print("Backup:", make_backup(), flush=True)
        except Exception as e:
            print("Backup failed:", type(e).__name__, e, flush=True)
        time.sleep(600)


@app.route("/api/backups", methods=["GET", "POST"])
def api_backups():
    bad = api_guard(admin=True)
    if bad:
        return bad
    if request.method == "POST":
        try:
            make_backup("manual")
        except OSError as e:
            return jsonify(error=f"Could not write the backup: {type(e).__name__}"), 500
    return jsonify(backups=list_backups()[:20], keep=BACKUP_KEEP)


@app.route("/api/backups/<name>")
def api_backup_get(name):
    bad = api_guard(admin=True)
    if bad:
        return bad
    if not BACKUP_RE.match(name) or not (BACKUP_DIR / name).is_file():
        return jsonify(error="No such backup."), 404
    return Response((BACKUP_DIR / name).read_bytes(), mimetype="application/zip",
                    headers={"Content-Disposition": f'attachment; filename="{name}"'})


@app.route("/api/backups/restore", methods=["POST"])
def api_backup_restore():
    bad = api_guard(admin=True)
    if bad:
        return bad
    name = str((request.get_json(silent=True) or {}).get("name", ""))
    if not BACKUP_RE.match(name) or not (BACKUP_DIR / name).is_file():
        return jsonify(error="No such backup."), 404
    base = Path(__file__).resolve().parent
    try:
        safety = make_backup("safety")           # whatever is there now can still be got back
        restored = []
        with zipfile.ZipFile(BACKUP_DIR / name) as z:
            for n in z.namelist():
                if "\\" in n or n.count("/") > 1 or ".." in n or not _backup_allowed(n):
                    continue
                if n.startswith("warroom_files/"):
                    (base / "warroom_files").mkdir(exist_ok=True)
                tmp = base / (n + ".restore")
                tmp.write_bytes(z.read(n))
                tmp.replace(base / n)
                restored.append(n)
    except (OSError, zipfile.BadZipFile) as e:
        return jsonify(error=f"Restore failed: {type(e).__name__}"), 500
    return jsonify(ok=True, restored=len(restored), safety=safety)


def prog_alarms():
    """Programs the dashboard looks after that are down right now (shown as a big red bar)."""
    out = []
    if not _prog_managed:
        return out
    for p in list(_progs.values()):
        if p.fake:
            continue
        if p.state in ("crashed", "missing"):
            out.append({"name": p.name, "state": p.state})
    return out


# ---------- app (PWA): manifest, icons, service worker ----------


ICONS = {
    "192": "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",
    "512": "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",
    "180": "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",
    "mark": "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",
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


@app.route("/font/<name>.woff2")
def font_file(name):
    if name not in FONTS:
        return Response(status=404)
    return Response(base64.b64decode(FONTS[name]), mimetype="font/woff2",
                    headers={"Cache-Control": "public, max-age=31536000, immutable"})


@app.route("/logo-mark.png")
def logo_mark():
    return _png("mark")


@app.route("/apple-touch-icon.png")
def icon_apple():
    return _png("180")


WIDGET_PAGE = r"""<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#0e1014">
<link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png?v=2"><link rel="icon" href="/icon-192.png?v=2" type="image/png">
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
        "icons": [{"src": "/icon-192.png?v=2", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
                  {"src": "/icon-512.png?v=2", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}],
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

LOGIN_PAGE = r"""<!doctype html><html lang="en" data-theme="dark"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#04060d"><link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png?v=2"><link rel="icon" href="/icon-192.png?v=2" type="image/png"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black"><meta name="apple-mobile-web-app-title" content="__SHOP__"><title>__SHOP__</title>
<script>try{var t=localStorage.getItem("theme");if(t==="light"||t==="dark")document.documentElement.dataset.theme=t;var a=localStorage.getItem("accent");if(a&&/^#[0-9a-f]{6}$/i.test(a))document.documentElement.style.setProperty("--accent",a);}catch(e){}</script>
<style>
@font-face{font-family:Sora;src:url(/font/sora.woff2) format("woff2");font-weight:100 800;font-display:swap}
@font-face{font-family:Manrope;src:url(/font/manrope.woff2) format("woff2");font-weight:200 800;font-display:swap}
:root{color-scheme:dark;--bg:#04060d;--panel2:rgba(255,255,255,.05);--line:rgba(150,185,255,.16);--ink:#ecf3ff;--ink2:#b6c4e2;--muted:#8092b6;--accent:#38bdf8;--red:#fb7185;--glass:rgba(10,15,30,.6);--onaccent:#031521;--glow:color-mix(in srgb,var(--accent) 42%,transparent);--ease:cubic-bezier(.16,1,.3,1);--spring:cubic-bezier(.34,1.56,.64,1)}
:root[data-theme=light]{color-scheme:light;--bg:#e9f0fb;--panel2:rgba(14,40,90,.05);--line:rgba(20,50,110,.14);--ink:#0b1630;--ink2:#33446a;--muted:#5c6c8c;--accent:#0a84d6;--red:#e11d48;--glass:rgba(255,255,255,.75);--onaccent:#fff}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;min-height:100vh;min-height:100dvh;display:grid;place-items:center;background:var(--bg);color:var(--ink);font:15px/1.5 Manrope,system-ui,"Segoe UI",Arial,sans-serif;padding:20px;overflow-x:hidden;-webkit-font-smoothing:antialiased}
#bg{position:fixed;inset:0;z-index:-1;overflow:hidden;background:radial-gradient(110% 70% at 50% -12%,color-mix(in srgb,var(--accent) 14%,#0a1a40) 0%,var(--bg) 62%)}
:root[data-theme=light] #bg{background:radial-gradient(110% 70% at 50% -12%,#f8fbff 0%,var(--bg) 70%)}
#bg i{position:absolute;border-radius:50%;will-change:transform}
#bg .a1{width:64vmax;height:64vmax;left:-18vmax;top:-26vmax;background:radial-gradient(circle,color-mix(in srgb,var(--accent) 32%,transparent),transparent 64%);animation:d1 30s ease-in-out infinite alternate}
#bg .a2{width:58vmax;height:58vmax;right:-22vmax;top:6vmax;background:radial-gradient(circle,color-mix(in srgb,#7c5cff 26%,transparent),transparent 64%);animation:d2 38s ease-in-out infinite alternate}
#bg .a3{width:70vmax;height:70vmax;left:16vmax;bottom:-44vmax;background:radial-gradient(circle,color-mix(in srgb,#0ea5e9 22%,transparent),transparent 62%);animation:d3 44s ease-in-out infinite alternate}
@keyframes d1{to{transform:translate3d(14vmax,10vmax,0) scale(1.12)}}@keyframes d2{to{transform:translate3d(-16vmax,12vmax,0) scale(.92)}}@keyframes d3{to{transform:translate3d(10vmax,-12vmax,0) scale(1.1)}}
#bg .lat{position:absolute;inset:0;opacity:.6;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='96' height='96'%3E%3Cpath d='M0 48L48 0l48 48-48 48z' fill='none' stroke='%239bbcff' stroke-opacity='.08'/%3E%3C/svg%3E");mask-image:radial-gradient(60% 55% at 50% 40%,#000,transparent 82%);-webkit-mask-image:radial-gradient(60% 55% at 50% 40%,#000,transparent 82%);animation:lm 80s linear infinite}
@keyframes lm{to{background-position:96px 96px}}
#bg canvas{position:absolute;inset:0;width:100%;height:100%}
.wrap{width:100%;max-width:410px;display:flex;flex-direction:column;align-items:center}
.hero{position:relative;width:180px;height:150px;margin-bottom:6px;perspective:700px;animation:rise 1s var(--ease) both}
.hero:before{content:"";position:absolute;left:50%;top:54%;width:260px;height:260px;margin:-130px 0 0 -130px;border-radius:50%;background:radial-gradient(circle,var(--glow),transparent 66%);animation:breathe 4.5s ease-in-out infinite}
.hero svg{position:relative;width:100%;height:100%;overflow:visible;animation:turn 9s ease-in-out infinite,float 5s ease-in-out infinite;filter:drop-shadow(0 18px 30px rgba(14,116,255,.45))}
@keyframes turn{0%,100%{transform:rotateY(-18deg)}50%{transform:rotateY(18deg)}}
@keyframes float{0%,100%{translate:0 0}50%{translate:0 -10px}}
@keyframes breathe{50%{transform:scale(1.18);opacity:.75}}
.sh{animation:sweep 5.5s ease-in-out infinite}
@keyframes sweep{0%,55%{transform:translateX(-140px)}100%{transform:translateX(260px)}}
.orb{position:absolute;inset:0;pointer-events:none}
.orb b{position:absolute;left:50%;top:50%;width:6px;height:6px;margin:-3px;background:#fff;transform:rotate(45deg) scale(.9);box-shadow:0 0 14px 3px var(--accent);animation:tw 3s ease-in-out infinite}
.orb b:nth-child(1){translate:-92px -34px}.orb b:nth-child(2){translate:98px -52px;animation-delay:.9s;width:4px;height:4px}.orb b:nth-child(3){translate:70px 46px;animation-delay:1.7s}.orb b:nth-child(4){translate:-76px 40px;animation-delay:2.3s;width:4px;height:4px}
@keyframes tw{0%,100%{opacity:0;transform:rotate(45deg) scale(.2)}50%{opacity:1;transform:rotate(45deg) scale(1)}}
h1{font:700 34px/1.1 Sora,system-ui,sans-serif;letter-spacing:-1.3px;margin:6px 0 6px;text-align:center;animation:rise 1s .08s var(--ease) both}
.tag{margin:0 0 26px;color:var(--muted);text-align:center;animation:rise 1s .16s var(--ease) both}
form{position:relative;width:100%;background:var(--glass);border:1px solid var(--line);border-radius:26px;padding:28px 26px 24px;-webkit-backdrop-filter:blur(26px) saturate(160%);backdrop-filter:blur(26px) saturate(160%);box-shadow:inset 0 1px 0 rgba(255,255,255,.07),0 40px 90px -30px rgba(0,0,0,.7),0 0 0 1px color-mix(in srgb,var(--accent) 10%,transparent);animation:rise 1s .24s var(--ease) both}
form.shake{animation:shake .5s}
@keyframes shake{20%,60%{transform:translateX(-9px)}40%,80%{transform:translateX(9px)}}
@keyframes rise{from{opacity:0;transform:translateY(26px) scale(.97);filter:blur(6px)}}
.f{position:relative;margin-bottom:14px}
.f svg{position:absolute;left:15px;top:50%;margin-top:-9px;width:18px;height:18px;fill:none;stroke:var(--muted);stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round;transition:stroke .25s;pointer-events:none}
.f:focus-within svg{stroke:var(--accent)}
input{width:100%;padding:15px 16px 15px 46px;border-radius:15px;border:1px solid var(--line);background:var(--panel2);color:var(--ink);font:inherit;font-size:16px;transition:border-color .25s,box-shadow .3s,background .25s}
input::placeholder{color:var(--muted)}
input:focus{outline:0;border-color:var(--accent);box-shadow:0 0 0 4px color-mix(in srgb,var(--accent) 16%,transparent),0 12px 34px -14px var(--glow);background:color-mix(in srgb,var(--accent) 5%,var(--panel2))}
.eye{position:absolute;right:8px;top:50%;margin-top:-18px;width:36px;height:36px;border:0;background:none;color:var(--muted);cursor:pointer;border-radius:10px;display:grid;place-items:center;transition:color .2s,background .2s}
.eye:hover{color:var(--ink);background:var(--panel2)}.eye svg{position:static;margin:0}
button.go{position:relative;overflow:hidden;margin-top:8px;width:100%;padding:15px;border:0;border-radius:15px;background:linear-gradient(135deg,var(--accent),color-mix(in srgb,var(--accent) 52%,#8b6cff));color:var(--onaccent);font:800 16px Manrope,sans-serif;cursor:pointer;box-shadow:0 16px 40px -14px var(--glow),inset 0 1px 0 rgba(255,255,255,.45);transition:transform .3s var(--spring),box-shadow .3s}
button.go:after{content:"";position:absolute;inset:0;background:linear-gradient(105deg,transparent 35%,rgba(255,255,255,.6) 50%,transparent 65%);transform:translateX(-130%);transition:transform .9s var(--ease)}
button.go:hover{transform:translateY(-2px);box-shadow:0 22px 50px -12px var(--glow),inset 0 1px 0 rgba(255,255,255,.5)}
button.go:hover:after{transform:translateX(130%)}button.go:active{transform:scale(.97);transition-duration:.08s}
button.go.busy{pointer-events:none;opacity:.85}
button.go.busy span{opacity:0}
button.go.busy:before{content:"";position:absolute;left:50%;top:50%;width:20px;height:20px;margin:-10px;border-radius:50%;border:2.5px solid color-mix(in srgb,var(--onaccent) 30%,transparent);border-top-color:var(--onaccent);animation:spin .7s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
.err{color:var(--red);font-size:14px;font-weight:600;margin-top:14px;min-height:20px;text-align:center}
.foot{margin-top:22px;color:var(--muted);font-size:12.5px;text-align:center;animation:rise 1s .4s var(--ease) both}
@media (prefers-reduced-motion:reduce){#bg i,#bg .lat,.hero svg,.hero:before,.sh,.orb b,.hero,h1,.tag,form,.foot{animation:none!important}.orb b{opacity:.8}}
@media(max-width:480px){h1{font-size:29px}.hero{width:150px;height:126px}form{padding:24px 20px 20px;border-radius:24px}}
</style></head><body>
<div id="bg" aria-hidden="true"><i class="a1"></i><i class="a2"></i><i class="a3"></i><div class="lat"></div><canvas id="c"></canvas></div>
<div class="wrap">
<div class="hero" aria-hidden="true"><svg viewBox="0 0 200 170"><defs>
<linearGradient id="gl" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#b6f5ff"/><stop offset="1" stop-color="#1fb4f0"/></linearGradient>
<linearGradient id="gr" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#58b4ee"/><stop offset="1" stop-color="#2b63d6"/></linearGradient>
<linearGradient id="gs" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="#fff" stop-opacity="0"/><stop offset=".5" stop-color="#fff" stop-opacity=".85"/><stop offset="1" stop-color="#fff" stop-opacity="0"/></linearGradient>
<clipPath id="cp"><path d="M58 18h84l50 42-92 104L8 60z"/></clipPath></defs>
<path d="M58 18h84l50 42-92 104L8 60z" fill="#0a84d6" opacity=".35"/>
<path d="M58 18L74 60H8z" fill="#bde6fc"/><path d="M142 18l50 42h-66z" fill="#7dd3fc"/><path d="M58 18h84l-16 42H74z" fill="#e6f6ff"/>
<path d="M8 60h66l26 104z" fill="url(#gl)"/><path d="M74 60h52l-26 104z" fill="#0284c7"/><path d="M126 60h66l-92 104z" fill="url(#gr)"/>
<g clip-path="url(#cp)"><rect class="sh" x="-30" y="0" width="46" height="190" fill="url(#gs)" transform="skewX(-22)"/></g>
<path d="M58 18h84l50 42-92 104L8 60z" fill="none" stroke="#eaf6ff" stroke-width="4" stroke-linejoin="round"/></svg>
<div class="orb"><b></b><b></b><b></b><b></b></div></div>
<h1>__SHOP__</h1><p class="tag" id="tag">Sign in to the dashboard</p>
<form method="post" autocomplete="on" id="f">
<div class="f"><svg viewBox="0 0 24 24"><circle cx="12" cy="8" r="4"/><path d="M4 21c0-4 3.6-6 8-6s8 2 8 6"/></svg><input id="u" name="username" autocomplete="username" required autofocus autocapitalize="none" spellcheck="false" placeholder="Username" aria-label="Username"></div>
<div class="f"><svg viewBox="0 0 24 24"><rect x="4" y="10" width="16" height="11" rx="3"/><path d="M8 10V7a4 4 0 018 0v3"/></svg><input id="p" name="password" type="password" autocomplete="current-password" required placeholder="Password" aria-label="Password"><button type="button" class="eye" id="eye" aria-label="Show password"><svg viewBox="0 0 24 24"><path d="M2 12s3.5-7 10-7 10 7 10 7-3.5 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/></svg></button></div>
<button class="go" type="submit" id="go"><span>Sign in</span></button><div class="err" role="alert" id="er">__ERROR__</div></form>
<div class="foot" id="ft">Private dashboard. Only for the team.</div></div>
<script>
(function(){
var DA=(navigator.language||"").slice(0,2)=="da",$=function(i){return document.getElementById(i)};
if(DA){$("tag").textContent="Log ind på dit dashboard";$("u").placeholder="Brugernavn";$("u").setAttribute("aria-label","Brugernavn");$("p").placeholder="Adgangskode";$("p").setAttribute("aria-label","Adgangskode");$("go").firstChild.textContent="Log ind";$("ft").textContent="Privat dashboard. Kun for teamet.";$("eye").setAttribute("aria-label","Vis adgangskode");document.documentElement.lang="da";
 var m={"Wrong username or password.":"Forkert brugernavn eller adgangskode.","Too many attempts. Try again in a few minutes.":"For mange forsøg. Prøv igen om nogle minutter."},e=$("er");if(m[e.textContent.trim()])e.textContent=m[e.textContent.trim()];}
if($("er").textContent.trim()){$("f").classList.add("shake");}
$("eye").onclick=function(){var p=$("p"),s=p.type==="password";p.type=s?"text":"password";this.style.color=s?"var(--accent)":"";};
$("f").addEventListener("submit",function(){$("go").classList.add("busy");});
var RM=matchMedia("(prefers-reduced-motion:reduce)").matches;if(RM)return;
var cv=$("c"),cx=cv.getContext("2d"),W,H,P=[],mx=-999,my=-999,ac="#38bdf8";
function size(){var d=Math.min(devicePixelRatio||1,1.5);W=innerWidth;H=innerHeight;cv.width=W*d;cv.height=H*d;cx.setTransform(d,0,0,d,0,0);
 var n=W<700?22:Math.min(70,Math.round(W*H/26000));P=[];for(var i=0;i<n;i++)P.push({x:Math.random()*W,y:Math.random()*H,r:.7+Math.random()*1.8,vx:(Math.random()-.5)*.16,vy:-.05-Math.random()*.22,ph:Math.random()*6.3,sp:.5+Math.random()*1.5});
 var v=getComputedStyle(document.documentElement).getPropertyValue("--accent").trim();if(v)ac=v;}
size();addEventListener("resize",size);
addEventListener("pointermove",function(e){mx=e.clientX;my=e.clientY;},{passive:true});
function draw(t){cx.clearRect(0,0,W,H);cx.fillStyle=ac;cx.strokeStyle=ac;
 for(var i=0;i<P.length;i++){var p=P[i];p.x+=p.vx;p.y+=p.vy;var dx=p.x-mx,dy=p.y-my,d2=dx*dx+dy*dy;
  if(d2<19600&&d2>1){var d=Math.sqrt(d2),f=(140-d)/140;p.x+=dx/d*f;p.y+=dy/d*f;}
  if(p.y<-12){p.y=H+12;p.x=Math.random()*W;}if(p.x<-12)p.x=W+12;if(p.x>W+12)p.x=-12;
  cx.globalAlpha=.2+.55*(.5+.5*Math.sin(t/1000*p.sp+p.ph));var r=p.r;
  cx.beginPath();cx.moveTo(p.x,p.y-r*3.2);cx.lineTo(p.x+r*.9,p.y);cx.lineTo(p.x,p.y+r*3.2);cx.lineTo(p.x-r*.9,p.y);cx.closePath();cx.fill();
  if(W>700)for(var j=i+1;j<P.length;j++){var o=P[j],ax=p.x-o.x,ay=p.y-o.y,dd=ax*ax+ay*ay;if(dd<14400){cx.globalAlpha=(1-dd/14400)*.15;cx.beginPath();cx.moveTo(p.x,p.y);cx.lineTo(o.x,o.y);cx.stroke();}}}
 cx.globalAlpha=1;}
(function f(t){if(!document.hidden)draw(t);requestAnimationFrame(f);})(0);
})();
</script></body></html>
"""

FONTS = {
  "sora": "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",
  "manrope": "d09GMgABAAAAAGEEABMAAAAA8egAAGCUAAEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGlAb1Vwckwo/SFZBUosuBmA/U1RBVIECAIRmL2oRCAqBrRiBil0LhDIAMIGXUgE2AiQDiGAEIAWHJgeKVwwHGyrdJapbsyO6W1VRAyCkmYjcDlGobB7ODOZxCMLdIvv/M5IOGdu4bQBmptaC5Cw3Zs/B24Wc3UejP90jo4xEJ5+mL/pCijoTBwmGLDIUXTjoFu5sGgiWh5SZ4XskoeA6g+tCYUQnLgcljNh0f2nfNxg8GVT06PO6JmtJp2lI0E+iP+eQObd50DSNzKChwFooKPopSntFwrM4C87KVzoD3MmxCDlyQjzPr+nPufe+93aXXVhg0WwIUYg6TRaa0NTyqSU0JSoVJ76PiFY9VifmJJ84cadO1SnLw9d+9Z7b3Q9m5kMISM6GWaLwsX33b0ClUp40sYoi4cI2wiC8/+F/W//7HA54RETUIx4RERHJkBAVv6EdCB2ynzn2M/pMMdYts5/9HZ9gt/n+uz/n7/01jstbvsZpfPZ9jeOYOQ3X/DKGSkhGhkSHAzz8f27VLcAwOdkhc2ykHcxIv3qUBVm6RKSrSwyLTEljSSOtZaKHjX/7mSf/7X6FGD5Dzi4MwTY7nJgzehNBzJiIYgMqNhJHDFHEAhRMjMbuxW/ac1iLcuHCWqUuXORn+Tn4svm7nZl+F5oU6xEKZ65BaPH45/2DnfuzjKKoBSVB2AKMMNAM24o04PShbtjAPE5fqtk4YfvxGwnJ8KX1LenDnCnzj272Gdoxlzd3Xt8XR8fi5vbmstxOQowpTREpItLIRcSIKaVxRcpRxFGKlHJILe75ep2Dh69d76e9kLV6RHVDY6QdI3CH/r5LLOUcP36unPn7szAvsCmjah2g0HecPcQcwU/GJDYrVB1JImGq6g/8/OmqUdVVOIQjXzbVxCO/RlcYUGU55OmvT1eSCxK1XpBjH3Pzz8ueuy9UJQlR8zebREU2inU2U4Rc/gnxYToUNoe6CFKTpG5ce9Pj3S5TBTKVn7+mncEKuHxUpvsEa62oF1f5//uqWfsuIXhAOgGO0FSc4wOf7yw7l5Nap1jUuXv/PfwMgB9hJAQFCCJGAESNP0DqnA9QsAHy4wuElGcyNXSKlGN6AMQZKNmgSIccqxQ2hNSmUOtsUU05Rentttw2pNPv1v2W1Wa/d6rYSbop2YsVobx39fudg2HVdyd5SV2TIG4ZBcaPX0vtzb0QvSIo4F+hdnKu6i6uVbUVLkA/k01JbS4l2AKjBZTXqkpQAVVCVWXZWFZWl4haOctWV8qvRdgogbTHHv/UoVBsFEGCUJF8j9SfjEIjozxWY48/1z8zKdhYB49s1NBj9P++eg5rOYNb9O+macheZRsOWRxxRIL4fdW/vofst/eG2OeH/ehH7xFNgjkJ55wXHONA6pA5c4Atn1baX8uZTYQjOTLB+iwILVpKEgGdKJAJgiR8x6BKEhAIPf8lTqjvszvcPi4hSddVlN3MVARcvMv4UFIAq4+ezjN/5G6jxvxJK02H+WAAYM12E9caDpOBxEow0J+laDYHuKBhE8lA1qQn+8EDKIkeVofwLXBezMYB3EmvSoKQSGjh58bexG4LM9orxlA+KoIlKF0OUBE1yPVfIyY3MZKjdFle30lAxXN1+6no/PJ/oeImxsJU/UGx2EQPsa7MwZ1nI7Y4JvvHOHyZr2+DBOrSNDFcSNmOkGZbryqq4xz65thY7cc3G+SCVIxN0+vn09cx/ugmNsZpJdkja11OXfe6xUN9BGe9sk/TO1TTzcOnriWRFiXFYwIU+wA6kHioq9ENsYGHLwDWXJOnZ2DQU0rzjCapSk/kniR/ZmKXqllkdCsd5yYM7bM7NuxF2dWXgCmLl7xpNkhMFzd9Hb0xdTchBLuCSSkydZzKOTITinW0t55f7hbFcmETa0BzVHHIokp9ClImst285sIDBOQ2LRRxbKkLgw6hjmw17aGZbpbBDj2oSfp1uqrlVIVw44ucX+7SXFus6IpBNsVccdbGFGAJIFtXpLmJfJGvxlsefnxc01NUpBuSVQ1ZpUphJ0/qzMJW5xQIMX6LQZ8iT0eXRPqA4usLfawlYGLnIGXNirtFwAWex2JXobQ0ybYdukN+j869qdgSslOYMJhrEihot8g+xgeGPxI/BRkEqrtuUfMjBP9Owu3moCaEmf/9/yLSkkvyfDPXEav4kJjarH5+y8VeiA/t4WoRLUFLiUa0T2QLWwIVYSFUxY+dwxh+j6PNBnASRakoNbRL6O+Bq/XpN9Fz8CMcg6FmqE5qb9rlFFmOWStPavnsPKLPzTlij0mvkXG3/mYxYJNKFfWKE8Ll+e6RC32bYnN1jdZ5jG07xFX0hEo8kexTeiZLi0PCsiZv3khz6VoaIFux+9xmsFJF5sGdZLfD7neZT/rELfWtH0z2U1/TgbcDrBaJiIMfCXBE9aT0IbyMODCL3xQfKLFqwWYaWoBVpLQClTZM1vZJCdrpxNFZF0FdGzdeN9159XDT9FTAdqNr6aOQuImN9XPFzW7jczvr6c8U/3MzFRnAYyBzFTPsXtdjkPskKnEtg40iRjPRGDYxls2NY6rxTDLxSfVN8hDtYY+I82jjhjzmCX5PutlKTVbPVKuX4CcZq62RY611GtkJNrKb6fYww16m28cM+5nuADNUMd1BZjjEdIctI1NosG8DX6nR1DdgU9+yoe+ofM9kPzDLT317KQWEh+bNzoQ+PvHi+k4QEK+xBMkMoh4kylWfTJblNtFILqU5jZZhw9z51mAzbZim7dm+DCI92EjCPp9WkMdp++grTqEEawkbOSqjAXUDP6qnbQybG8sWxjHFeKaawKCJlp01CPxIQkCa1oI5drO+Pcyy1+rnBVmojyzURxbqIwshC+UiGIe0/IQfIVbpA+7cGs/f8Am3Ud76297q397/NC7DRQ15Tp2e7Bp23lMt4J5xGvo+7/ugb6d+0A8jS4YJYOszNs25bDctnsg53JvWc5U9bN20uq1OS2QdMfiG2CfG5NWrdhmQW7Khb8BhAKESS1BYT6KqcQ04BElIUKIiM8fJz+5HS9FRTAnLoNpdJKlav9U22+2w0y677fFG1jb5rve87wMf+sjH0nziCz/7RToVQgZSJso+GvTpZ4jHnriZWvX8AoLCIpq1aNWux7jzxGJcPgfQt1XoJv30N9gQQw0z3AgjjTLW+Lr6f7M1+bZ3LKlwbwpyDS1K0AyLzeHhreGYuQPn6XbmO/mulKLJpvZ5ix+RTxrUtf9PW2fnGOMDxTZieoI8N+ilt0jyQcG/zuFiIiTyQ+hZ8FRSKo001kRTzeTI1Vyr2jZmddblhhjevx9v4/MwXR4R+Q5W/SDo9CtIgYxcnHiTTDbliOiW0Upmt06zENsBglFACOS6VJSgGRabw8P7NBw716B2jVG6mdId8qjrydwybqEvrGHOm/5ohNcoYydLy8RzrVWoXwbB7D7Pec5znvOc5xoYdToaDtmm4nSwELqYnnFmc1/97OKSMBOAKKB5bUE9wdEv+3zaNlaB+CggCBJzFNAMi83h4a2zgczrvl9I6XNHF2MnAebDC+o2IpEEvwQd5VXGv1sMyCQk/HERkwF8UYAPBAAU0gyLzeHhNQ95JXwF0j7PdRHfRmFrxLNPLiibkPBfCIDGnm67CO3VdMW8ce4KIy5bdVfvDhRiqdBnrl7Mnt9WhdWUQNDQl2P/2NA/2S9Irw9c2As4ipl9gsPARMUOhd/FGfesor2AamlG699FGQrrPNxQnhWaKMpzTT6MRQVcAVqCRDK2NMNic3h4r8OAakG11XMZXHSgWIllKHqGeSMghlJlTFnNMIO7bEPb7fCCnXax5IRHJoOpfd5Cl0i6G9Q9S2KfAw46vA2eaAl0Q19acwFdVD3pc+ihhAp6Dsh9mlEtzbDYHB7e4zDqd15o51IAAL7t276NhoZ08SQwSZAq6XaOBTRQnp45hRUdoqChTcLflacouT2ODafGbFnCiml4WutI+ytiIn+i237IzQzHUnYw4DAk7STxImon5SGEmxFj1k96TWZDKfp+Xj5xhtROaju1lW+an2bbgcam6tv914pUDtpvJ0cGGr827TOAYqyLhKBs5KRKgbxFNsRI2Yf/FsryAfsLnYD2w6TR8QGEcOBgAwUCAAsYuAgDZ0sEQo9k+iYc56+wLudL5yObQYTQ6UdIE1SHSLAtiKqOvbR/Gx1KOq8qBx1y2BFHfeozlwmv3fbYa5/9Drjiqk88MrMFwtPy0TEZsh8R8AyPydw//ZUJflQryXb6v0q7iK53xlmyx0u21kabbSG9Vr8jGomF8zl3s65ardZb1uGeN3oQtozNMd+ZfnPBnDNNxuLb7nsYE2O4/oPl0P26S7fqD7RN13nf8W71Ps2SsQQojU6qXtWhzqkmVet5yfMsKkV58qWcl7fkoPKKgiBioHGKcrHQSCcDsUYgQaeyQKAv/c0ALVBsDwsJGAv4QcxvzC8MFiYXirhbJG1K8fkUxqiEwNFKJsot5CQiMSAs2d/2teGWYto0SYrIhiRMyR+ehfKGnSRcJUXNG4KJsKTd/wsUUt/85HY75M5NFss7/bd5gwkg0WEyrq+0U6rWEBIixNtmHJuNCoVU5ksRMFOLPajHVtaSmTTS5ijhR7VNYFu8Q7E+YgrVnHwPcY4YEHOtRHSJXtKEzWC3jflzg3OT/cXm+TAds0DAMb84WGx9mN8r2Aud0uTqGKDCxer9yf/MXP0m3x2KGiWFSGQEWIJ/4ody6d8W7zBUX5EN+hGp0kO4SWp0mSzTD/BZOaafl2nBGTEgsqyua4JCQlNfnr52gOfRTVmTWaAY7n0TiW6DUpkZRr6Ucu1JXJpV/YF0JPZXqk+zqHxUPEs1QNFtQBnWZ+bT8ta5RIptZONCj3n0vy5Uc7HyBm6k6tX/qmDNjRAZrqXy9OsRmD1uE3LFwDkXZcB84Ih+A8hFuUCE4LD+c/oNp9OboMHruib9mlPp5bbnX5UirRl4RYNIBhIQgtZvGKgxPeTgDU3fTeIxewmCEvG5WYRJvJO+CMPFvv2cNUwKDw6TxniQlAVsy4cjacDK0ZWuTl8m6VPvEU+jTMS+YamCfKaC95riFiml3G6yv30ZCZsPm2i3Y77y12Xs3Z7g07L2cuPPp7w8z5is1fmp+A42VtEqzOO0SLnWNcdKQ0Nils42ly4UaCEvlcVZFh9jokVYRA5FPwaEUG/MjQxXR0HD+L8wbDjwwAsf4uBHAPFIQBCJSEIyQkhBKtKQjgxkoh7CqI8sNEA2GqIRGqMJmqIZcpCL5miBlmiF1miDtmiH9uiAjuiEzuiCruiG7uiBnsjDDeiF3oggHwW4EX3QF4W4Cf1wM27BrbgNt6M//oci3IE7cRfuxj0YgIEoxr0YhPtQgsEYgqEYhuEYgZEYhdEYg7EYh/GYgImYhPvxAB7EQ3gYj+BRPIbH8QSeRCkmYwqmYhqmYwZmIgoXZZiF2ZiDuZiH+ViAhViExXgKT+MZPIvn8DxewIt4CS/jFbyK1/A63sCbeAtv4x0swVIsw3KswLt4D+/jA3yIj/AxyrESq7Aaa7AW67AeG7ARm7AZW7AV27AdFdiBnfg/KrELu7EHe7EP+3EAVTiIQziMIziKYziOEziJUziNMziLcziPC7iIS7iMK7iKa7iOanyCT/EZPscX+BJfoQZf4xt8i+/wPX7Aj/gJP+MX/Irf8Dv+wJ/4C3/jH/yLWvyHOsQQSCAFqUhDBmREJmRGVsga2SD7kP3IAeQgclhyeHJEcmRyVHJ0ckxybAJ1IwL8kZ4QAC+ujy3ST8m4xzwvb9oik7yown3ROSV6mKvGvXKcFnraOE9YIVe/pQlftMR+1zL2u3OCmTZM8bgRuimc+xDDzFDhvuoDFY6YoSY0+Pth8cjXFXhamRk46QaLTRKdPuhEx+Rx2M9LSKY8hSpMU6nSGI+4TSPGDFFG3XOJ+7TTQxPB2SXfK56wv2FDIf11+bfjq1Z5NQJz/0Tvl7jsQ1pdrtkqiJaY5ORJKTimO27d+Wr+WNw/cihRsrLBKvCToUWrACBWo9hj3jQfXLNpFJjrqusoFza0Mm1o3bfCs3L1SVJQmlLjwHRDrha2DAZ96+fhvCyiAC8Hfb5pE6liwTpqbeBl9WD1iQ7rFfWYKHL8bl9/gp53XTIJKgXOeLzqv1YY3khVzEZeBZjrrgVkM+Sy4QMMIQ4IU0+PtZsKQLxMzXRRoL9BBCBBFeg8RVqBLqjQ8iwjybyhyW9480EVN4/2DZPOvqcwpG+3UOUx5U6tA7uPX5KAtrqbISaS9p5XX1BDajg7SkVSiVQmVUiLpEZs+YlGKe+eeOFkkiwu9AcB2aWiLXF3Vt5CpKRUfPaFf85wBdwFiAlZ1F2ZQsbjOwCqX9Ud1ZPVoh5y95djB7tzut6ODoOAduA2ZwDyAgBAno929bG+skG17b5XV/jkFmx+m1+sianVKgZyE3/5g7Dpwyd84gQkCEmRKk1YfVkayNZIC6201kZb7QbJjtXDfjscUOtUgnpWUOgfGtu2yEDF7t3oNtpY44w30aRhS+VR/FP2pL1FsM8/amz0rR9956deYkuCOEx3xb+Oh0sKLn9bbkUG/dfClkxbZoarViq3ymY2xfCwOLz8kgUlSlJPugyZ4jXUTGNN5GrqNzk6aa+DjrpraYLe8twgXy8RBfq6bZiv+wB3usvdblJieKWMBPxe/JD7PeBBKGMwublRLrns3CBe8PwtVVCkxFVfeWeoQuMvwFEhoa+UWdStXhSyEn2rL0LWYjr/CtmIBepRSIm/3EdlvzgUETkweT8vfwkAOS5AXRbyGaS9oekX5EfIlwAEKHoaNA0Bj1CCii5/xhQFk6RLUvBTFkk4vTMVIkiN1A8oAv+M+gnhqXQowSz6S84tTLj6nkOistQxhkiyThELiBCurpZ69XJ6vxFJYUhAmIou1OgPIPSdIjWSnCp8nZcgxI7WlHjkuV0TKYCUwRHpIY9cZEaFJgBJbpLaz6nVTCJGKO6QKSBjIlBoFP3U9x4oExQ0vZgHBdZpzdCGKwsrmKFFGAWYIfKKTxU/MfpHZmBoKqyaS8ohL6YRTgijANu4Fjtk8aEfdwbHvdRj5DsEfbhpuBr3YMusOYCgDIIGBBfMmXNzCQhxR2eIZGOSHdPwh0TaXr9UnEMYhBmu0AvoscNB9q13xEQ8UR/L1A4BB5NqsaFjv8UDHmNLjyg0J/FRNX2EsbuC6xDGsYIf6oOl7MMYcdWFHbg+N5tlWTByMLEGnAzM5+onca4wXLue0kqJHKjnd/AVtfGFF65ZUv5L7yKwWsdTjNzMy4zZjacRmQzS69ahtNzBZ8m3fzAoMsnhxmBEKmNwepuKNESBuMvX/UGaX2CCh2R40DH8v5FBvtWT1Cge+UuRcyrkSJy7ZNuDCpjZJsPyhypgS1Q7XqOqc1lO6GR1f9L+DRyrHwcNyO/ZGjrqSu0gEdp4LRAJjpEg+XE0G7R82Eoa+fx70chfr9xPsNR+425AiXZRBR+IVM4sj1Ppz1unKM6NTvnXFao4HvwvZde7rj8e1qCLlQo/gkKW5IFKObuVP/M7TtXsEiF/iiNapmhGP6g16v4VAZdaCm7dlrA6wux6RdpUcM5ETP4MfQ7eFmnKP2o7wMYWMvHaxhFEBwjkapT1lziq9A9VhVPJjEWMKzksfp5hA/UCZMKNvLoPsaflVSSib8ReessdQ82/Llqe2Va6WGMb1YEp9YNtwiP1gJrY0GXB/IZaoW8NEdrvRi5/59A2Hq8uCZ14OMcZOoLS1PD+cYOD4cBAfOsd1o4fnq6T7NAICTrMclP2NMZeI7e0mLqpxRyX3+awsrvtFh2qbJGbU3peWeIR2ngCZ3yjJmgRLEqPJHRWyl2arPzfIFqTiZpVtYMXja6UzhryWcKMlboBvtJaxAQdJ0unhfGx1ArjYonQ8bByOuKc4yjigu+0OQnJHU5X8UqKl1fQ6rKjl/+JOmuaSBYCa5tjXEwzcUrntpLZjqe9jhIGwiS6D4GV2pPYhUsl+wW/2QueTEGhonYEnzQU9rcSincIEYbSfj7LYX1HyZs+ROwQWWg9+Mm89EcgPPIjWVVCmE6ltI1QhoN+3b9FqWXqScUzG5w7TzqkWum8sWUSxqyLdGgkpm87I7CV+pwHid5CKETGADm2mii1FpKNZeopFbZiqkyDO8VDti4XZOOitqY9+7IOVaNzIyI6I9gonbp1AwOEvRPPW4GpqEEKAb+NtRRpjW31oLVXcX7z6W5j0O4FNHOOaDtKJWvwJrsc0FKwLA+I7ooc+eu1Egyq5FUBbHuqdh126uRdC00Y7SefxBzIX6mpvIt0eDaEq+WsUxFR8OGEQ+zto4PsGe3fIz0F5KSKg/HcyXQKRKdiYFgnD2uGUFpLjr/r6xzUJYQT/jXJAQLG6Q1ZPyv01HorBBjrhMJk+WwB9yfxh0nSFbNnXYol/7fMMOXE0OZs2ypFwvzFdtiMqqGJ5h3fjoYZLZjHqzn+8rEoE5wAebOzxq7PkmiOnSqXRtHJTvBHvu6meYg/UQbzMg04hr0AmtL6Zk3wZnANktyrOnt38Fz2kxODyn0DrRMll/FgM6KSxCyH0sC19YsSBiy3ErFOKLF+cVeCJD20sJRfnDf7KRQJtNPSP6LumoMMWMPETRYiswbkogYRr6URfUv9Y65OyBsrQu40dX+VJHx5TS78IMMncVzGqQcovleT8zFQhEwhREna64px4bCx2CdRkbiy34jCInszXO06giixEh5TdHLNBm1yXkQeYck76jSc6/ZNDl2yWRJxqmUprZihbjjCMZXJYRenDtamvTunDk071x0hK1xUg7kGTTEo1kLye379zhQOjCdJFrpXn6T2Aebs1FMlgMdIyDZrOACp7p6tbpBn9A+4CAEe18Z/7RGhMkJUg6CxUfBsFkivXmFuUsZPnoWFsSZ7dfIwVNO+wvA/5EUHxi80uXOQE9SnktHXfdxPho4dpyDNK6KUVkLFOESQRak+RzTfOPAuVqHPKZYDPy19EaqrSWAnOJL/qtj936quU2tLyam1g6YbgYhw8KiZqcWwp9U5hJ+l2zagsg7DSsE49/tN+VUtsn4rZzYbg2o6eh3zkzt090/7IwtfJv+qo2mfnMWnDrJUcvl5tosvy4skXTMpWnBxmkXa3z9FWt8+8XOGTJgF0GHQ4dhVcgaD9C2SeLXBX9JHKZGWNz2PtL174uc/y+zkBcFjJDxVrbhco7ukudgtqJcjGB/ig1th5oYGKGGOY37y5broXHfQd8mYMrVK4qiu2VHs+p7VjiS3T9Sk1+Mzb5XyB1AoH2lnmz3mwlL9xNqVDoq1yLw1tYpjw4PiYrLwFGNtiS3ikN7d8LPoiMyYcCGT4rB7fqeibScEtogODRTODc6+/piYwpEkAy34DBUO9DQuQmQlH7Zgg/j7VdJbfxvvqEm4ZPInLy4QZN+tqH55phmjjYY58O02edPoSLPZ4Rpue/7tptgKM3bCMwnPysb2uHUrtLhBWVnLIgBrW0mMIzmRvVygrotPa6fhSSH+nDgEHZfzowRsVnMDWgtL6/KpNt7ax9rpurWaCaLK5HZ+GoJykgRbM9lnZUO/7tljdPCZPOYY4ja/Jz+rjGiwLKaqTMhswJgvGmAeaYigVQrUozPkkZuyZSPTS2iMguzWfPalTEC+AT2liwZs+dFWwxRTxZkfyMjsyGEdLWwJhd4gBIr1MjlJ+wdIsbUtsdIls2XEwP3aumiwmF52Z+OSNmpAxrk13y+ueJeiudRnLNauW26ZRz5GwV2AZIOmzChFwMoUMEykInefAqxUoJjZm/vCHpn7ye+Oqn5Yo+WzR/jzp7LGq5gIT6TPv6NlOCtLj35j84brPBx0KnxYNHYCcm6bXFL/+u+fv+KxC4aOYuEDnN8p1eiBk5Tww2Mgu+dotZ2opXlmjHoYJi769u3zPzutg0hUO5t2xUiXxSPDqLU31bmLGAoP/+KUcZD/VC0MKt3yM/tg1jGIOQeknJlZQtR6Veg01omxrXnFmMPSGhbiUcWayxcS9VytckK8eVm0oRfNr4xvU0sTaPJT22GdZfTMAs3xgu5zL3oPSmaVQsFr+UMMSwsRUmrudGH5/qTCNHrRRJcOhR9k0/sf1PR/v64R+8+0Y3qF+Pj2ej4hP1TRTSPQBq88mhDtzacQKCvlZALZHUgIxPtYmN4iT4LnynxXgmvCmeC88NgSbBNYAraq0pxgDhyxqyO8Lz/XLT+WBVqulskKaW9owIkCuQIdrut6yrme9va2IaKgwIwQahCXGxTChk4NmeDF7A6DtrQG0zW4/iP/Fk/rOepnN2+EV6TdprpLpLyx2S3suy8arD9BgQ73FLeiwFVYxTv0irhxmPOZ+QY0s9+F5+C8OT5483K88T46jtNi4CUbz/QIJrq5/+ixhBjijqdMxG5IhS/Tfa3RIdoiwo5kgXGJPhBpEBabHO4Y85/b/uzxNDkmw7M8LR8dxGIv6PyX5WSRW0wFza0QIFtyoQVjAk4wLCBoj/9prLV4gSsZluTXLWXZh3S6zd7cX54zu5RQ+CvztngqPLkuKYm7r5/H+41xl94YF1/HKFH2VN4Fu9C/YX7som9tddExlzf/xanhn3OMPJbU3m0u/na03BVxDXGt3GVbubip9t7jB44R/jmOAy5etfpxBhVlZOumaYtjOlvG3IF+B23D4kiRotSgy7Ko4ewp8zyE72HT+6vpnucWTb+/kvuxl6vsimHGeiYjkR1ms0qqxsQEcML87o9MRbrFAqNJyIW/T/K1aB+6qGMGGq/A7kjKqX2NKW51BQZr8ELQBi2zYKegJXJYeJsB9eGYAlfRn/0sG12nGU5uddEwS5t3Dbr9PqFb4Rq/HlEu/jZd7jIcx1583ytGzinghkuE7sVK153zQpJwSiyb/oiAkZq3FNA7a6xLu0k4mKEyBZCaeGq1sT3q16t+6t7HNK93ew2SQvMBSUfVrg6hK1lGpry+MgmpJsA+fFRDRt2G276IJENOmwdzgtWZ13NsfUF+dcHT+ie5Z+1PPzWxVbdvWqZ9s9Hf7qM/i/8KH9tgG0kW2GCa6LOqBdhc+BvtnB8P5HyC/jC7xxRknMpta//8gBvMxT+U5S7Ly+WufxxdxFwMeAaeudZyUDDOsIB3rjXt89lHcEFortUb5/dBJ4e7xHdQNP8iOWL3s/UnHML727gLKxsrTz57+fbBS7eEUFsyDU1OTIj09hUxTkmlhhPOfYyfNFki9i8ZvC9g6OWm+nXS6cTEHJW/M7g8/n90jFXGR6OzI922iAGUCQ49cCDaj6SM2avEypXRLeTtbNcCC0DxqdG/XelNUoL4EQtZFomUlVUcat6PrwNHvuyy/M+e6IWKisD7VvuldPKrRILu/Spp39zuIqaefd9/M6erLsSLuoVReCEjcK+NkygrzjSXFMG0TvXLLlI+Sm7reC3qvGhQxdTTERcfvsQpylPGCeoYbH5GA+Gq02aezDkznlKbmhg+UCc5SwC2ALlKH8qhfuoXHK8/8mdDxy/jY7CxYe/5jvxR78jIUe8G51xDIxwb29zyZyNwLXLWK6nOUdC1QmGzQeoZXq7Y4D7mtIG8i6vqI1c1TWEl6I/2EqR9NouDld2XKraZnYYZUoP7nV8gLlJjqwHir2ezq2lnaxZr0hLOy7Ws9i33gVdp6PeBO468mHyRjF4OtACrgbgizaGUo19LaRjvdHcKvGattXMlM8AqunGSQ++CAkZFQ0SsXqLhhsV/jFYfqS71n7/YPFGCrUgwsxl4dXBmcL3URrSpneczQXXMc97/+ajALDzBzD6sm12ssDgedl7/nvnzxtoiHCUx2hsnKYsAdsbfKb826p7ZJfwyRvXfjd+1UWVSS8U6F6Sjza+NIJ2yT2HDvnOUa6Rmeg/mwvrxsYLsWrlj0hrEi/fhu/R1jTRG9v7/d4VEzL77vZmII0elnx9q9x241Z+udYJtgXx5dsdFhbIMPu9+cVVrqexKMaGc5OCYWFN9hBRMg/W35a7J00a1IFndN8mjQl3uGJvELhgq6WCeuKUc4ofJZcQKVC7Sjo9Ctgcs96ZVll8UWVZzUMYplVUng0QTy91WtVNqsc67i+2r93Vd8iu0gkQI9qK71ofEKqMTEnC3d6jn5qAEMTyWpXJ/MAMNkC2QqsaoxldOV7O22loZz49U1VQpy9nPO9pYW8pqEIQefdaVA1RaVWZzPz+jRwa/6fSsiLdyFZ3PK2s+XsZ5juhSeXFDc734rMxTQrch17xoADtK0EtY57Kst80Ovf/+YJbK2LAEcXOwZ+hurwRMLBWrrA91MquVXc51sJ8ry0N+uor+vBXjp6v/xTPUqDOnfyiC0AcRz+vkPyOqiPHCn17Y9iPkiM2k4CSD4cpPG3WDWpr0BU3ERESvfbT9pPaH6fGiX7aah1hrt367d/vhz0sqyyr3/rh75/4Put40Es5ESMKBIPT+rZbiz8dKiz5vUQcOvmiTa17kWSC/urt96cqj/7+cevT/lbM3KgMKwx1ILT8PsKxgLgQOvwWmOdYy3cU3wzjmzLGmnRY3svbnBdsZ/xIoaG+hRbnQWjIXsdOlPbY2KXFvttKg7gNkQ+DwH/WQS6vYkxe1B5+9zE/rGZOSNkaMNb6i/rtnRwJfrzbz6AVG+2u7fWzBfJ7cfTohuxYPU1vDWMUOBzlxiMXSd9dFxYxmt0x2VKXdSHJsEUC2UBlqVKDFxiqgAhmOJUACGPka1TsDdFK74e9/9lW5Cp2stk4OkaZ/hq2F/b18o9fssJAkSiJASiBAEq25pXVa6qDpbkVZ1DEXpV6FQ7WgugXqGgU1XP5LEJcB9w2QqaZDB+TEWj9uS0m0ahF/4UiydP/a5WnE96xkQKBuqfHdEc/aD4yXVx2c6Y6yFCeOTfCzEoZjU0arEV/eIhVxJYFrfRybK80P30l7fwehR1705CGmlQWftw4cGn3Rnfv5yOE8sNV1mHl7XffZy+tqt1pOlHOedW7d1gYKOZhzpDG4i2Fqp7WLbXVGegKcK/UGyj4mPWXTS0yFpekXU+YL4+Os8dH9TQ2Lw4dYAwOs0AucF1M1MS6XlE64KVZD9bfRVWCTVIbaWqnJ6nVH44puL+w1G3dltzvS/rfoHyZragwqUCNBezeqSo82LqbpfIlrqdoPNLLugCExoN69RbOXbAxMUGd/3mfRyNIzT10r7u6brZQG4KIHg3od9jspqWEpkez0upNRRcVLVHm7RgJLzzD3Sm13I0KZx8f5RXYFVFuOOp5iRuYw+15MgXCUG1/zOPzM8OKG106N935auLgDRmrUERkliU1Dg42JA9Cce0ad7WrIdyTopnxAGZMEzZ68/KPMxMmygszZtN1XCzyzkijtgqsfvgPbigwOaZSTMaFypJTyP/yfosKys4k4iK00dk7th1MQuJl5z3OEgQXuR6fYYf4221LjQwKwW5kql9gnQw5kVEPmTOOjKt8a50lyiYUT9zFrb3LJqT7R1fZYej2Ba/J+yWR5ifdKg3zjiWnC4P30jXwfNdwxzT5QlGQC47NWcybi4s3CTXHC+e3MrHxf/R60fv0AhxxBT7Tzzet3Ec1WdlXbZOwCVo+HbVbjP59fGHG4xVmR6xqt2RHjuXxti1tk/YuWTMB+/AMkQmdvLYGt1w/9EMw/+9UTE/gCEjEi9mrVoNH2czb0o9H2RLk8gLuMKDm0hGgxLm06E0uNr3n7Q2ZwSHQkK6qnFJB0MCTNct3bu0l7a2PARJW2DldVd3xRVNZ6uLK67XAJhPScvQkMKZMVn53OlwGnT/d0V2Bo3/1gqj7i2V0khOxYk6ofHVPac2i7DmxyHN8yKiRQ5wMylpPyS8+k+PKbAQldslZUtFaSW1K09sCu9i9GMVM4IhCMCHOFd+xmCDcm0AyyRG805UbnWF91aQjmaHoCA7+PlyYcHxemicZTkyaEsLzk5o3i8qobZYU3SxjWDbEFm8Op5RkQ/IfOnAkvrUfz41AuJYulxSq5KgcTaVP581dujLqkmfXtCRVGHfofYthOegajdiCh/914u+zeSh7AeJ2HlqrmfPtMSroGr83CWS+AQ+df4teNoUTxJqa8gvpDEZy8E1LRyaxc2YmT4sz8uSz8XtYel/fb8N0zlxv/EZnLqQV1z2pqn9XX1jx/Vg+y0PUTVJO2qFc8e7wDDfVbdYFZEU5e3FPS7LwTMtHJTOnvwfK3/W0U4foab65jZp+USE5mZxtOzdl/ysGW9R+jT7F12ae3BLiha1fSsy/Udnc+HvR0rzGvWyspEk+d4RYVOezeoqKSqpVa8/Ihz77H3bU5F1bTa5hfXJ0bm1xSDg9DnxzLhoO/dsx3d8DRyePJAPvVJTNv9KIu6CE4p2WyB/5Nf/uezxn1U6kDH3XU+0FWK53eziHy6B1tdG58Y+QXJNzrVL9AUnqwvyjoh99to1t5EDbFxzcyIaOllc6MT1TUJiYoFImJCkWCY4E5zaiNja1lZDLu+GcG4y8jPZ5dWsbKJbeYzSorZueayoAVyvFoOj/+fcioB6koRMz+QoEVx5NTWMIOSPTDJyIhPVZRG8Vg1MTG1MT7mjN9Ige6ssptaSBVPbVPbMGLMzMLz6SQQRJCXJCULCvg75YeGK4WVf5CVaWxQvEik+HAve0pnIja6iigk3hCSfOo4XvUUHcydqbR0k6AJifzcJV5SpyRUXQpN1JQVcMLDkxL8w8kJvvfjbHZ/eANdUlgcvI/TnFAJKPhhq+awWhuYYBLwmpl0NuG6GHQGiIO3T+76BYPX1E9VM3/TJusZ7LDe4r2P834vTcMCFSQI0sYiUnNyWhvaAorYvP7qwvkfdX5sbCSa2AgxAqaEhmRJQoyM36vNCVBkJXM48mSBQk5KZw7NCEt3rBTqJDj8zMWoD6esODLpUQFhKWnRfjZZk9drWZhA8B8heR3FoMf3KCweyzvZ6SKRuipJH2kVEsExceZVnItLPlUyU/kiBDwkwIqmKL7ERkbvAr4FfxjA5xcANVydf9JZ0jCuQm7k3DBloKf/2x0iIhVuLaHYTMIkOzcrHJpCs/ijeE7jFwUceGuNT/47KEI47q6QFrE3pZB3iAImBPAjjYX4IKwgnd/NDlS4prhCpZlhi/Xqdnw4qQPm+HTruqqiA13q33ZTIwQxnYNZ1Cqfm/Yyf6ztvnXGrtlI3sJHpzzS8D58Pz84hpOeT88F4fPmJhMoJvqHrpn9OUO5u54rDWEhuv68MsVzA5g3eQ7p0yYZ1JL5W3kLXALFlp5uk6l8+CU32GX3mmO91i1VpiagWXDCG8X0jJAJ21E8XABPTExT2CbFdOoGEMDCxtmwhNF584RJ5yP9CivYdyHEz8zvZc57pdTXZKfDPiJJ/r0zAbexIUZj1x7Ae4FTlkZa96OQc/LREnuCYbd7IzNkUKpd1QkfjYUhuzt0zB0Hjcp8pZCsHph85b4yEjcvDILBb9CPNTZvbhRKarMNc96/cDsAtBoiYXbAP3bEHy+8O+pjwVD9Q7SJbdaHWKfz9WkheIYyIWtI/IVMBQAAgzy2DF1vyFtLQf0MP9/ft9s8k8lp8hYLbkV8MLmsuZYM689TntUSjy24uBGTpJfauXX09VOc5AH60cKh8QovHMHOGcIYih+55xsDGYx8F+ZzPOUC9N7BkQRMU6SS09IFNdZCyWvo4udUN8g22zAkxO7OAld5ko3JSl8Ly6xZf78fjFkudlMwOHKDHZIQzgxoqOjglMu8hvepQwiA5OAM30a630Z2ypVlUnR9vrbvRpn4JlGzfttbgX3MeWCi5fra99iAtmy9BK9q5t+SSY1vasr61IZ9O4u4ISpd3eTlWJz4fLlC37jV68uMuG1PHLGYO8JKLteUrReXFZ6/XpRZK8XFV4vKy5cXy/5+tuDhb+zFoHmlVfwFZIS+wa+QSCnWreSeuZ2FcXr2fT9PDN7avNYX05N7SEPt8Td3B9zc5XryXVNT0RNF/Wr4vV0xHmHT3JyJaPR/Hp2kqK61QXNmfDqPdpVLj/1JBXgFZjHNtd6maqPVN/00lAXHsIRmzA7t6g7TRgKOCe/Hy1zXb5e6vT75CKiU6WK6BYRZjti62ttC7Ohz9tAyMC/pfv8aDS/7Gz+1ChfxGmLyTpgL4/f7TnQ2SYu7z9Qt10+QjD5DNSCYDgGT8B72jhQz6/w431pOl+we8fYGPycBMWTrrbRc4/UQfEZB/s7KJE9cmgD9Fhh8F8YcjUw1GEl8sURV6B/TwZuZ03PwDOmcPuWaqrDKxDghNu+Esc0b76jSxCa8TFdn2gv4QeTCFlLwLO8Hal66bp20kQyCMleIL3+PaCT88vtvrt3OPuGBveBny6wG9IWDVfrU8eShWNpKanj48Lkey45eSwtzePEkzmFGVMZHV0ZEwMMHOUK8hkDp6Sn4bndSLuni8pptotjuAGsIw5T4cVamYyzKnPS8/0XrMKN4dy/GgFB8fCgTu6tm/kGI/vEuiv3dh1buGhaceIBVUWrQffs5EJ5qiLBiM5Bk5pCounFYeQyGgwrKyXHk5p9bCisZqp1VHxmmu/eIN8CVbpGP+3nqfnvEwdG/sxRXuL+UN2S8dOpMz9mNKffJKz0sglNDt4IbDaB6UKeQJxE5wmF/KSMREBHl66FhkbY4dpUYgDFuWfbhef7M2TxWiUZwlmOq5PUxCeyywbv6xdmGmdzcGhOhvJLZTiQrcIq6OFOvM2y3EXkWxoBg/iady1ZN3Xh0sKhmVEOK3LwSrdpHDO60DD4U9BVndfBZryaPzZXG2UrFfPnCWAxg8c2OTku0t9XxDgplRomzmUTJ0yUQO2SnADfYoCO4B0j1FWZilh6JrRcQZtzSFw9ni6KjaTFH/TOxcTfU44TM8QJwpzqOe9EHUExarKcT+bGDXjyTAvRF8gyeaZI1DZHsfIwCy7Gxy3yq6hmhsiTzMfntGvyWHr6fKmk1TUoutIrJiGIoI/UxhE38K1m51+ZFy9m/tXZlbmdcMZQt/X4dlfnEgPn3q06rK4gbxKOZHUgChFtPaTbfMS7g7h4genN8+H0X+ioN27zH1YaOhBlOEG8RWVgOLZ6p6fMi8gIdfj12WMmujks8tGtVFTw6YpN/sQE/3llBX8zYSQrKp8LeZMu/nPMHiCRLpyOqK6OmBYmRxwBBoZ6RB8+kiyMmMZkCZiS2Yz02UxJ+gx1SSb0jJlBz5jFH+r6Hrx9O6CaE+jgHlvDOc6IHy+Z+KoW87+VbYB5LfCtPfFDtJOZk1k04nsaccejMMQjIvmALsyGOw+A8e+P/6FTT2AoO/njzB+7e40VWuOemAmf2PP884+g6fP28FrC+yHMFOH/g4mXJWEcNJ0TUO/xSJ+LS+6TF169JIzP9moIxj5YYSByPtqd0feavvfj/Rb9udCN79jWFv7nk4xTOnzR70/A2bajLfL3BdYOztGMvAS9156jdwwTs9VR/Y1EjcyEOqdGwIlQx0FVkNDGYdWircNFRV3J0W/zWmAb7Oi4PXX7kmZtqsI48+2povU5zTExNXG10DPbbxnbnFM1NPc+NO/gnb9DaQscbrzQ2+0WHVETS/Hfj85lzuXOFc53ne8533d+MPBhBzmGgG8hdJi0VKV5KGh7Kg26MVRgPz32AEZLP8D9+qIqplEOnd4aPD0Qx1XHda1vs3B7SWrnNeqg9QvH7WQbEAzO47N2njbbJsHSBZUA5rs6h39oQmYiSIgfDUfZQFcCsMUZlbvgY7YeykvyKaxYi8hG/eXqL4ZEf0yAbKASIOgHHKgh+y8EHirwHb0r34ncRA0AiwFdG4aji40HU59ccGZLjxcloynZLbERINsaDizAb8SUns6bDTVewJwheD271aDe0n5+bDcUsC3K1wB1olbhCO3GuGXcuBSDZpBimIJRoZOyiuo5DrwDEeR4651Zln79ESpAHvMSpAGqXH+Ccvl9aQJ1L/CATlzrmZc5RUnor6gIHcMdKqIKJ9cSMXzPQguga1BhMFTmn1EVVEiW1IqYSeldu4u3aFLXHCmy8KX2Oz0R1QKIhUtCqOWAUwN4Pd09ZLWssshxng7sUPVAQ1ZO1R6GuWKZkNBaJZiR7meRSZm2IGft8P1FPej1cdnlxgH2AD2sNGkG3vhfiqF1+JtBBFX+Wvr30/G4r8eLBEBAAFWoLAYA1Q8ApJPPTmpFat2UTKRK0cgF8aNK9AVPuueg6lDfq7tqWktZOaxi1lpvmnevl9Lf6Rt6ULsNYB2wF3xG02fhVh67oYew3rB6rAAnk2PprbKv2w8cYZix7+c+i/Ot85Nz3wngQjwDP97f8EU0MZoFmitaHlr7tbW0SdrZ2se1P+603gl3tu9c33lXR1XHTqdAZ1LnlM6Szn2djzrf6/yuK+na6RJ0ybptukt6unp+epl6h/Ue6bP0g/Wb9Lv01wxQAx+DJIPDBt8Z8gwJhhJD2g6FM8ISkZ18C1fk0ifFIsgxqZUHMh838ScK46EoxLYUl2bpL3UlLg3WWfVX3VV3aKRG7ehYV3rUh77pr/ZqnrJarE6tVI/W6S29bWxb28P+rdnyLWDPWnnrt1XaamoFWhn2mvubU8wTzcXmBeZV5u3mB8w/oNSocFQCqgg1gVpALaJWUAMWYgtbC5KFwOILi3sW4xYPLXxoY7QFmopmozPQ2Wg5ugJdj25Fd6MH0V+gJ9Bz6C30FAbF7MTYY4Ix4RgGJgGTjpFhGjBtmMOYqeninlpGWpIs+yzvWNJYNNYR64clYVnNV5IAK8VWYDuxp7GXsfewd63CrUyt0FYeViSrcWtTa7z15F2XjQtTT58617i9cVfjn9cNrpte55dz5HHyRfI1p4+cfun0uSbXIGgAjgIgyrHTCEO5e5sm8DZKFItAhiQSHTQTp74w6vGBWa6gffVFmEJRK+ha6DnJHJ9Wm56w6ohxt1wKn5urb5rJcanUgM0d1P6yi8Q8a36el7smW3Ill35nG+HNE0Lht5WUGz2UnlauS5pXGO/I0zn63I7F6fLAUlcb9auJww2eH2oqUJjUmi1tbaZZh6wSXXsht074DBbF5X5F262tKqyrOkqwj/7UCujPB78XWpmql4nUQ1oUlcAhgJTX7hzDjI/ZroExTrzYUJ6Y4gDK4fl45MEXoTYU9wTa+VRRBiIMEnjKKjqAF359C01azadi8fm5wj9nLqlyDanZrC6FhOVkzalh6nSNnyd2pQRNFxnQTtKrxqqJ57C2vT02nQ6kKSTEg6gYRPyAR/W/CjdlEi/IE0SFJEIpEhW5dr4CheCkfQxcCvXzVyj45Au7DO5BSUUpjeFX1Zs1nbWQH6XwzYb7unViV98LdvDxTaKFzucVHhetL7GDrTlr2ujevhtO7zwnqp0y1npjjnVjzv4a+UiflWh36fGx2jcU8uBnjNZ+klCdchJsvoQcrWa19cpHl7QWData9fy4lSX0+B/L3jkHwZyunKYBM2U6WuTgCCaGOA0PTZX7M65WDzj/P0MJpxhpzZJiBepUAvWI+8TrfnpVPrsnRvbJGAoEABtQwncPGUiOFxLCsmmVKjqw/xqYQLXZPaBKTSQXmZZpjp8jRWkqCvfcEB8jdApmFJz9whgRsDr4OWdPQY2K0W09YkJZeMS9MSV4RYhaDDczhUWBotSYgIXtHlFtDkjK1Ym80kpLvSszowXLk4KWA+UjGi3Wt0WFEKLVFMx/l+8wfcp6IuIzhDQhcp1jC650kIPHA7lCna4JP0h+2TgfOHyBg3+XRVHIoGJRqyVcSDkUH6ht3NEL5mepaBKRsAmGxZfallaIPYYLcVHQKsWIZ7VOLLxteOb91PyIWGdbcpODyhtU5Rf+NKrVe69cRrtPDt1oab7YphcVy/aqGOlb32UCT1rhLh1QfBjM9v0aFtHVXq+ph3wKatOd8njmHMxLRNVhV9+ug80S8zAvP5mn4aHpEicHfr3lV/9y3K8sTFUlcHoxIw744r55FjDY9h6GDl5LHAahsIRWUkT5KZ7dQyTqRkReLNov6M6jox3myRvRN3AZpF+XVKbrYVxW28xCIwVyoW0mTJiMYYu7oFOgjFdpaz9ShpNXiGo8skeQow17UQZa0Q/6bn806Ins8zHtAuNqv6tUGcYacrcYZMaeWNgljmGE6upWFPv6eMbauD47brULlKkyCc5EEkiNuLcqWsBi5mQTseWk9nCxxMFil7EELJCIN2Q0MWlzmK1n7Y4U7w3cbbZJfK5H0TvPrhTr4fEdPO+WwfmrLQxDdc66Jvi4Gg+FG1TaiI72zbd0kAz7vBGe7W9FO6IV2vKBI1RiaFP5BaVR/Zf//V2clr10WUletsaAjoU+Yb64vt8IiXk+vg4js8B2OJztr4msHT0KrY+lkBzPXWuLMzuixa4s278Ow+TmYuHzaCpbpvBU9Zg7Wjt5Ee7sKhjkKYREIxIjhzLZS5Ma+occiiIF1MFs1TKw2/3yD4cPSXDQalSN5Ka2tupe5EP6a42ObrRfqMi9SiWKXUQDNWw7NPb552Qr9FDPsVcHHP9FUERsrvLntX909LF0iR4LfvR+Uo1OOpjN/9Mf9l4UalXLFVgh7PlHy30+zzn/3vQfDMHO7m5dk12v6qhl0bx30sLr3vVMVuJZmQ4Y9ITufzKg8BPlMyqFR3fUZMZC+tFE042LDvtmELzUPT83ygzyqRrMk4+q/FmAAXZr7szlbazmhfzNOCVEVgdo6ZiwDsUpS+LbGPdVT0QEpps0zstNXG4KT8xpE5+jAlO7hOX4dB44Xs+vd5UBBbRmbfZZycdg/DUDhaLGWw6N/VdPwrbn11JhtBRmaeuRHQCeSRstjdlfRuXn4uv30t+C6CCdA5Pd/8taLxYxZQd/6cMUhMQCwkCHM7KPqXrsXr1WnZWVRjRVhVFiiZlri8vVXYGmdW5qSa7SyVCtpe5cKbOeiJvNKCTdakn16HwEKLbEZDH5lTUNAr96h4m59PhsxaFcM5OdaJ/dZg7NoqEOjWK1Q1XJ3CFYBodX1bng4hKjWcglItokTigKIn7UMhmqjdlEwiPnqW5hmjDDQPqJqCZCju1GOzMYD24dlEtmyymhrUuTw2BKNz4sJGEAK9DZx06oFyihieU+TEliMzJa/RpBPULqFpcwIQo2LnHgeffcazvn4x7kUnEjRbzGW9iQEY8n313nM96sosSrFN0aIxo1lM/H/uKdORtl0khmhzwgk1LOfZfb9E190kgvCMZwGPnsxQG16w/3aEVU/PEb0nPw4Vsn+Epg83M/wgCyzZH1ulTIWFQ0XIpiImq+a8Cviz+Gx0z5Dzr4EwV33UjW/L6GNZ9kouLjoXRFHYohLyzcJ3wlDCHvmqE9g14dN6rzotwIv16NQ0QNS90sGwlIoq9KLL8eOyjjJ+/4N4POLXr7vYL6hUZs+l6F/0toa82q/nNuRFqrksV4HI1g4bgMytDb8551DqpRw7k0n8g2mTyQ6/xEQ0oDV1afdGGp5aV0pyO2/68FviRFkVUi/qGAtfqA+tAxbN5mZBIu9pNVX1hYBRLh8MN29Qsr8mxlhXkWzlraH5OyQYDHIvjT3zTqoY5RIHaN+s8pYd7AZ+7Fn+/5EfENSoWskbzxlGih5W8XnzHTDj53VafbSX69o4kGtvDJj4r9zYqF5j2NEqeGcfBzLisn5mG7OYvzMGaRbttWpBQerOY9FaeMDQR8PUQCZdcO7yUCnxSdEtYBt/5jJQzBpRJ9cd6kEPK7J693pbj7Bvh7ubuSQTsH6HTARrojp4aRwJ7j3X95eUptzt97+PqXXz4YPgcEY6J3fONv/xS8Y6iNcdJnegyv+9v29w7PUKVt/9AXB7bzy8JAN5PafqxV5na/iU+afaz4ZkWDxkO2mGitSg7TUXQEP1mueS49Zxg/Hbwf1Go/fQ2MJCYP+uZ8QZv18FxvL/H/iq4t7sT0Cdh+Pfz44XiEJHD44Xyn928djPplx4Cr79aPdZPccgGa0yLq/M/CEjKyK/1PPtron94QlZ6RGdt0xP71Tk9rdAF6b09+jbvxJvYZlhkl0lSFZuWytsyKDrO8xWtisWvy8aXXUVE5ws8/KWHD3vVUGHakK2eCDB20GZZ51xw6pN57HiSy4E7bsQDTRymsVoc+zSw6KLAognVLC7ZIjQxCMHGxeuPm6iubbynNUVjy+fbWrY75oy6+/dFnjjfSlXMcFv62Sd+KFC2qFMSdtRRkzw3wY7pSXwo1cdDAaFo4naNZEw3J+OKmxPA21JrOHpgvy0Jfmz1rINzAdqYKS6NtyXGaomJKihNRm047fZOnFle6Gg7+MM7N++dv3Je2j+58lK481GEwVpkVpJkg8w3e8uA55g59BnWMUR/DMfXe8+QNHOq7UVjCZ4AJiMUzlCk/O9/v/OVyYCaxQMOaVPFPeElUvFsihh+pcffJfvkGnnWjc1C2rvP7aYbW1V+4d9z9tO6ICuvgYB7AUKXyYTDF0LlYYIlVu3pVk7qFqX/+Dm2fxScuS/UZi7f549Ta5fOG+sanDTepm3KjmNPREPP1/JeuUsXoGNXrhbJ05Wwe1X6b5T7T20v0785ZeVHOXfPhC/jQe720R6h5aVQPHBkEFeXQZtlmVS1q/XzbbqQm1s4biSF0pqJdL5XYn701a/3GYm9fuRSgQPd/qaONjXtwg10ulcpRcNZQT9nkqLyX0Xiba42MhzJlBeqQ9r5DMJcwEd7v03SQi+UqPV1qj9weGi+xc5yve4fmvWjmAhL7j5T9h5DtZFEJ/xiiYOxvMvb81L//7mNbgUF7Ub9qrXXbXKPGOnVnp97iwfilBSeilKvj5a0H66WKhta/onyY1ij+/zhaYX7vqB38lVFQe1N3i+klwlyar327J+/KZoZwfTOq11tPxzRLnfNa/Drac+dnOZ/HITlfBthP15lWD08hcPWIU0WcCG5aSyJpC+8J2pzb3L45iaMGesN2HtDzb2ZNiSb3cl5lJS4lZIpVn8+SsDkg3iR1YPKqqucyGe9hXwa9hQdpT20dwKttrSSBYEX5egqz+v5WGQWOED0xoUg4torCAnkqG27bedvSZL7RGUBHrLaUiWldcUF/h4USBcYb7SGz6dpBVvKwOlqGiZbmRNth7JEvZykyis4DlXPehZgaOTXqdNdMzLZC1QpX6KPfpBMaUUyq0yUrE+nfj83IMgr0M1q4IM+AkY2p/GnbQGfa2KYbrGaqTlnxtkQyS5u3rqrhK2PaB7YJY1pLlCJ3ZZcGvswyWagTZGzWsIlBEPqls2VV57u63c74MWaFgHdD2PzSoB7zbBW4v5juC7YVPrDd/epP9fMODXnZ6jNpT7LtBpVGMzOcXRqzpXeaggU1ogj6I4deuhQPirGf+WChfTkuUepKgozNhFQhSo5YM9+wAsCMzN/+o63RnmpQd7bhurah+0VAhG4mlTWf6Wqr1B7V48JsGznOf5ertb7LSD5/UfeoRyG88ht7aEA6kpuVvayY+vGdEWGyKrewQKNSGtAwoUtvhPLbpw2EvbhZlmAkM0iwhEL2wD1b58CBiLvjwvari/DSrY2l2kpOccSdveJ6dQ6UbXLvz7psz3GJOk1gYm46Cf7TY1SMd3bUDjMnPjkQ4AjF4QsLwC1XX+Fa0Hd6BAQ2wbGkDocpNvmIR1kC9ylxmHqHn42VelJkysycgo7ieOJb9d4Z3BfmYnq66Q8JjckgGAbvSiWU2ZAYxG/bzdqHn/1WLTrLT/Q7FmwGqfPfLVAoU2Wjj1x6RKSnZ2kWp8cxZIcdgR69b+vgoLJYPGl3nPg1WXnf9Fpe+Y6y5DEVgb5i2NU39zixNG2mwbHQrTVwCcIsF+1My+DxZVlVJQuMRB5lYsH11gGmrTx5vzjQn2ux71Qy11QHblrjaFddV4ff5p8+bQ/lDgQcPQERe8QR8k3BQVPor1WdbjnSM67ZVgPby4cnGh98GsSTVpTbun6/1pSomenbcnQ+sOaxP11xePuY0p55R+6O6r2ntvu6+fxscrgjpRtb/HXp7vdLV5ee9mBgc1/onyiVW7Ln45Ek5egikR/0NM0+zwLkdz/4/+V7oPKrVR/Y8fU14F72T+P8YxMVLrgKBsC2G9iZkibyrtH858nPzdZVKJ7Xsq/GYMMh8Hy1dN7mU4L99hUNwgp3myuqO/pdNdNhFRy2MxrIyHqry2KTAtkfWnsiNLoSZS4QnagEhYr1VhttjniYPoFsEdG4VUcRK3kfTFpgS+2bukwW7ODrnAUz7UG2Ew+kvKM1X067KfhSUkLrKUN2GJqoBPe4+Q0ZqnFQvzoiDkbKbkHr57V43lpaxQ8ot4C0UOpx5zlPrm92rq4WmmqYFiicEc96d4zoFX+QUqZLK8EcalFDzrXw6roOE4w0HoAbeCQjkz5rBtlo2/VjKax4LoNT9iIlvpc5HlcVuZhoxF48LnhOttERCz1H+wkFSeSD10qNWP/Uzmo9e8HZ+Wy6z4MnytNC/3BMXDCOUB/uCc/9Jzz6995Jp9N9JyggVDKnAuG6sxHWvxXI+0GSPvut+TfnYyRoM7ijpNaa7Bl9BNLsSHfNxJR7yjkz5cW42QFKjAX8LSKvVlr/cmq/n4hAIJMfmFmVlSVq4l7FCaH87uxs9LQceuqHx4gkgrGODiBEaWpoeWCE3D5PWeKZbfOW7ZpsAuXUb9G8S3PuYS+qmq9hq1c/q/74fXdo+JHnMQNaLLaDP7JsTx2ouWar5ys/sl9HFB0F9h9XDRuPalZR3XbEoJTyXfBPnVrPw48zqhY9t7w7A6c2aMPFSSBfYnFfvH0vVT2y2Y9ush/sosDAyUlfX0x/4K1kdfJQXXf+pp1PFf04boz4SmSt3M3v0D2+L9FEk0v+Of/aEF0xnUus6issyK6SZKkg7vN6nyUUPGdVZM6c5umVjUg663ViPk2kEcxt1QhnaEuyfYXH2k3VleEnaLP18NwPYjm7XnzbLGWAepsOGhIBPbfCtSWE9G7RIm4WlDYE+Fj0+Zt3GUs5qtwfchjnx8PoWBiDw2lhJkWtq2FfmeUER+yfyx++hqIkk15p6ObKPcETUdhn5j6sdwhF0ZgqlLCvz3vsInMLsR3KdLTO0lP/OIqz+K83dTaNeMHRoxvj9Sj0RI52epR/7xnqwPNozvmUr9WDY6tAoFRqkSjjM2Pxev/oUo1MGSEOMp53YoBWVUXJqvQF7aUhtN9HHVPWKaf11bB9Ks1hn55PaFS19JnxtjcmNQKd5WNl5CXS/A+W38zbPEPetjdXKN/UC21CxQq5SOjMU6iFVTbXkCaNHIlehlKG3HWnYxnZndeeMbzAWPnGp0lbhiFX9TEBvlr1X5SjuCHkGQhhG7xqscF53cnDOPMMlqeHINjMQMLkvzpcSWNLUN9BplM8ybft13rgHUYkGGOLty9jznLECakpo7bXSeewLkOOQEPDqi4nfG6USKhbkgDk5gahVIC+U0MiGf8Dhr992LRohZKHBF0LZ1vGvDa/d6xlNs45k+VvoYgGLiM31/hdvK5yTFkjcLRNxQftzHBAlrlAbDI9ereIxB9uoBiPKd8em8F9B1duD3+c4joyNOcwOmtv9092VIy7PJJ9EhNU1b1Puj3JNiWIH1eXF7nrMEzgfqjsOMumv3/1UQtP3F1GKRt4JeLgKDNu31pfgAn9b+hm3YwHDv6jPC6x7VWP+wM3E7t7W0d50HHj2sHDjJvgcBMtX21NkDlN/y6aJxD76ThD6Y7Ih5pdXbAcKg4RIKGP6Cp9Tv+kv9HbCnbKO3F0ExES8sWxwfFbIpwCr0eeHD+e4nAN916l3AXnBkZc2OSlQTP9sLxzawgwfZjiEz0WfqIZm05PhU0n2Viz4/XHayb8dpdZTMdfi2gdFba2qfPTgPDnq2t3bTlUqzopEXfFyUH61nHM5+YYWbzTnNBv60f183q9nn2x5/Lkb5ZtcZtPR2Y9cl3YsxMDYw+dEvJh9MrXenF12rJw72378L1xBzs7wXZUbvRTA+cSiwv907VWgNoajkWEmgpwL6fwW1c1osy6IKCK8293w5r+Wn8Chrk70LdVbRLYzX52htpQsFBpxgKKZu9idf5u9JZdAnM6qPLllH3sgs8W8t/zpG4j0DuNadOHKgSM1XRuPRhWA9HHllg3Tejaj7czKv1iqeTsAgyG6HHMaHSQPWBxrnG+8N8AEymWZWhkTovh6LFy1BcTNG50hukkiXrOncf3XTPq8QTOePzunuF7AzW5HDPFksx4a8KmbFDkG0efjFiWSz3ZtQ6TZGcbsOPpJvOk+slIhCI3xDCRpGrZulx2EP99t5Zx9Trvg3IHNuV8JuEdmsDDdV3QIg7tzd5rTDxo/7BA3lcjQy2sWskoh5AeVrGiZ2EoG+4+hTs2qa/TXpzUlfdODhFGs7S8OEUmxgvEjGAhcN3ZNE1kVmj4BMx80ZYLurzWwG8uUBZOprEVYRH8r0Jg7kf5bZmVg0SG+aH+E+dgeUuTBW5paVoqSxIOx/J531QkxniZG9pFM3MQX+roeSaTonE1bgfDmHeTEWRcHGVxN0Ll/Sdg7H1ku2H9nWaGWLbUDmPyoqJqnnejkg82Y0DYo1IslSXEbQHHTncv6rxBSUbRqttUCPip5shwrkKCjHthZd4O76QEhnCGnu+ZKShxXTmeRIRuVh33zHPB1viR51Z8gPaHjjoCh8r7g4TPDoaP0FT6lVzPyXb99Wn0cJXNNg4xFRG19fCfDXRxtqLSPP5gevCk1YLqtKLMkgCzevUv+Um7HCQfeV5JUz5RpqBbQMJIBpKFFCHLZpO1SAoSh3wn38OqSfCzHfI79O/8B2iO35n3QZpDrV2+6LOnkpOQXU/cAWmiX0JlCV37UqaJL9IRHbQHD7+JSnAmCpqsFjoqy+MPVmgPnXWSZMOBxuIYaVwUjkwSMWI9qqVxyW3+VZQNNWfJlc40gwFD3yutjlLJMIZfzdYaDkbw/+Mh8xEERhUE+l9NtHHTlq5Ltn9Ek1HNRwvLv/x03DFnNWYr7DEXgHgLomq+AciZkqsrUgLhXk+Y6U+eaMuecoeVmm4UVIfzrHXubGeRozWX8/2h9IQo7R25qQPdLqDXmCSei3nc9y/lO44Kkk/kt0RBVTV4HiecEuqzecuXF0XQtOk2tnEy6vklL2qweMUYTNgv6OOld5Ceftp1Z/7BmZ+G7t0Z/E6doskixgVz8/Pa6zUDA8/kch5DeXb3uL+OXiAT2Tgr8b6vZ5b23lfswetaf0Zp4X00snm0CjrJ2inC1ttNHbF2lNe7rdTBp7+GhQm5ZYEwBrN5tGsS990N/TI01H8n10TWqDOWyuKlLMlVyNWqNYfdkaC1Fc7MPuLYWkSt5gxfmUclJ+0eP0O2ck/FRD+evioux2IweCCZskruHLKpzMobLGU4DsHM5rS2NZ2wtkhPdBJG3qXZCa+HeFSjtGgzJvkE1NyAU+DONP/5zSqQdvvPAxWw5Gj2qF/a4dFaF4Qs9aK+BsunK78bHEzrk1+6ljyptlpqbUvFxU8iXHOiyhPjq/gAPHyGu6se8H67QJRHj4rZAFPc+dh7lhOQbSCZe9D1oOXlb9yw8rVLW1DQnwxLUZCnWkssi+4kEhNyJNPKNf7j2LVgs5Zt7a8is0oji9dhIesD7vvmu8c00L+6x445GpRinGJkrd3m60wcjLmCwEpTqnqrG+chvF3psEEg5+2KwGcfOL+4fm2S8enBoe1kvVbfFaA93/EfLw2Gw/zJ6pBKGc+C4DexGRza6AwdjFBJWpTViUp7zrfaboCdfT/JUpUodNzERDLLT5l9drA3k0iysK7/6vg5LH+NlQz1S+VKGrpueOz9n4on4/wS4zncCI5ROwssVgrm4mbpPh82Vcnk4KWmR30KmyXIlTWWLNs7O/byc1WKvSkkaVx1YQY+4znGAX+ctuudUvRb7t4Q2t+p3MqOYZ5qH143QTZTEjodn7+2MNEolfWvRKoIEjJPiyoze9+rN0gWFy5XXmlCWh1f78BahrAJrr1JX3LPVVf9vECgC7PgurH823AFDP0h/KvrK+o3R9//5+sWqko0Cc5Ij91V8USgGXWnKVoKqvnybuZjXEoVj6w271dkfkDoLMzeS7cu1/irZPsOUx3bdhNrFEFV+/7xPKJBUiHkzTjPVBF8vlxcDxMtrGyNZVVMTLuSEqA+amfPtW8osxkMCuN4MsWd+/cdqhqsKCG6zdpX2SzvPKvGREOEt1rOig4iTYr6DYlacX/uMm66+eJE4r1qa9yXKwwkQQbATUoefBgCi5CyiL60cHN3BbbMyoNXIsDDDBTMaZ46Qf9d9YkgD4qjWHluv1tnEnhLXdxRHwt22bE2TP9sJpjep4LoYqfwm2djZdZyq3GVYGORHeEvnoPAeNA6ZwKBZAxH0GZN6g3rEP9yMhMOKYk+2LUm97uenoj4mhBcV/WogbIbzE7Y8pmW/stVZiZWh8Ut0SV53Q3nPU2TD5zDFee9TQVuUMV9566q7vcm6yrrLbfKSGJx6W3bG50LNtHJbPbCVPR7IQEo6EHO7zfzcbkNHP5EjP8x588UjNAfPib0HwQFHk+uvnmrcfzaio3+bW3z3Y9bL2qCZBTM/uAJWLV/6vgRa2hYrz+O82yo9Jkz0oGQaL0lmpKetO5xgs0RXEUHJ7aIE325S/1k68mdLo6CH5hWdLm2vvls3NW8Ux6iUsdclZ4KU+jC/hLkbDl8/mydrnsB51LyT+AnUox7N2qIFBAGohoQh1XcFZQ3whIgliYt3lCqbAmIoauiL61iR8MpFN5JYTlRbEiod6AcMYCYnETz+bWeu4wHkxGFlbUoms18Iw/fNTDJ0Yw1NL4Q+p9GWLVDpcm2frex8M5ZegHNNxXzcnSxwKiw9z3si1xeQnC5jYuphX2BpqVnL6U2NQQRYRHl9YgIp1NQccJoS6UhpTD+bZ6Y/OkCIFImnmvGbpwrXKVIIeoT8MT0KHYODu61PAY6r8nrnIAJVeUSIqhuq9ULVZp/zH/P7XHvv4zltlZhq9LJt71e0geiXTDZeCes5CqeHxZs+sF194UkO70hMab6l4Lny84VHokzyogG/FtSiJKabCYFPT7lnwGqurbQjV/4pdOLLHGSnWYBI26wt+C6xt2/eOJ7Iv+kPsNFaJD88gR+VWwmFFvOPlp5K83OjBv+sCOX1Zez5VyfLNdj+I5h0eQcVf7ln5eK/jwLLyD+zVSpICyAFEN28E5aLhau4J1cMY+jIx7u1NpN7RaYzuinELj5Cozv4Xxm9JEnahV7f+fg71P9EVRmqXajXilZUQacZ56fO6wll7z1tK3GLk7vP/gBvetenRl6hcs2Ljzxf1o1wKvbxJbSnsj3QXiU6ChUXUo9zIOumq6bbg+g8/Xo6PyjuAxITQHEpRIRVhhMjpem7VKIf+nBbKiq7CY1Am2pcbO2ysndK9DH3qMmXVbk1WVfatO+K/AuUp/TYTUkVvouXChnYSvHa+3k86OQdbCcYWbjQtFPVUIo/xaHd2Fcy3bH3NkUNiOg7z+H0J5/nzy1NY9K5Hl+pnnJysI1D2cIeUpRtMD74xKWrfXFxJBikqy17cSdk8+9y+YmOqSVKiVdvSHBkfa3w8kneSNp7NXgSwbF4TaPRJ6qVn/JkO668U8f9o9GK0W25AhhPC/Yp+FLgsvOT/IHJPpmDF1Y0CtjeU6fl566htxESJz29GLZKkURz/Rj+eZWbiHUdhEKaYE4lg88xBan6w8jPU04iYeLG0Zw/z/X7CfdXHKCTpefvfrGwS238Z7K4QeRslVNHQ1b2MOCgh3bcPCpS6Lo2o4vx/li8pvMPcF0+Krq6b+fVtikjlsbS+NgjHjHuIgcTNSlkuR0l2DclGRloTEeTBAy7uhDAZ9TS9O/13fk0lvtYVPqRnavsLU5Dk1w5EvU6uXuvJQ6rv2HGyer5ozln3df9A/MQhL9f9P+QWx2hfPOLfE0zUgLVuxISHlsMOQygp/22ad+6uLMjMpNhZ5TTnsploDGXPG1KQpH0Y7OaEVXzl5ScXJwzBuCLMoJd/swSb77o249DgVH7RuW+dvng8M3OYbc2KS4RL56q4478BTRpQ+s9mionEqjvb8eUmiC8TJW9l23z2Fpfjbfl5Qs13fLbKRSBPkNGhyYcmCrBncuiIxWCgZ+q+vq6wc6RmWCIuIjIpx8whji+r1eNOyvZ74A/vWHE2Lthkp5daFom/qkUg9Kc85LOX+Y48StW/b7k08jCXLFiTzXdi16AvbsfISqWFek0ZrS2ctuioYKfW5Q4sRznV0pEa1ULMEapU5MKoK6g6UDj5xgSwdkVZSOFmPAYpdR2uf3UoEibl4etf7Tpq3ssFuzkDiCOhOuCyr+XgaLxe0EEY8qL62VDNr0GxKFrwHHPqP49S2MVTPd1kilFiRQn4l8kikSS6Xx0ow0mVwpRoYime0509fdfVndwqPuaMl229Wggp449VGHKubVyXSZSC5PlZn/xF9H6HRPdI9MEdfWmSvKLHpu0XHFdRZj4Wy5hCPP1pXOWb3mZkbzso3TlIjp+rDWJPd4gbq3ftyEKntc9/dP+FB+E22JemrlfPSPich1mSwxEv1ndkCrzAbQyHoyH2fYU+unfd75eR/mraOfzfutGLRdfR2yG7MDe22ffEhkMLhzTNdY44qKKnJ8nmVHRhVBRq2UDJlH/lW+EIgASlrtcQ6/I3KIReoBfImtFqe77iyWd1L7gPMTf3sJJ9I6E0ByTFpECDfzwyAsEUSKko7e1W6tCyw8AsVIdJFlUFtcHagGOmguepPSBODRDqufJigc0w8RCxBREJlHBcMWPgjQLHoSMujNQAOPmRTsKOeAicE3scl5rAfT49pmVZI8/574cEoS1A1fkN6s5rSVMBjR2FvUXBmY8bF/fpSSfxtCCf5IpGGRmhrJQpKMeUfFve8YVuiMkYNJA8PzPoQI1cL7Zx1AT+YYmn08KDXfdHDd3qaeAWXKtqOWcytk4q0KEHGVDq7KLB1SelkX+2ahrRFh+okCjGsLNM1ntt+DPMFZzgkAXP6YIwCAq6eue7HuYAcNv+KpAmCDAoAAY5sK++4uoIOXR0L9bSzp7JsEWg8JjcuJuTPTDj2cAFHInEMhzI40JbrqYHjYVkbpo/EBLAzGemhUBqLrAKakJj8KOzbWBVV4/86AwFQ34rmpm9cQbccEznBdOZdyf2a+ZcGUzTHbWaY6mZBuTjHf8IGlh9dC0hoCFeEpDcModMujAOi5+C1bOBCbFF99jLTD5duSnpjWVn00k7jS5v41oITVa5XTXQ4CJJTF4gAr/gu6+IBgSxVyqocEq/9udAAIPQ/pg0YyPA1i9w6aTeg1hlXPfHUAZSlpSK5ILIRvuL2Vj3wGuvSiai+R1h6EioYnRQW5xQ3WnuR7qIA35HZJ7fXhgA0azOhcFNF92AxdLEeos8FSrkNFTQBLXU7ljy2lfZp8EE50trhwoq5zsLcvPG0186cowwUb4zSU5TBcNLiT9gps0cLc6XoOLJHQ8S2TL7URxJHVaUGk7gRFe7o+ipBuI1TXVQmSYfHBkdBhSppQoas96xoXP8mQAKBTTutRWDw99qBaWSdgz6DbeSET76h/bZ3pa+JbNtULyWmBdSoQk8wagLcZuqgk8x0gpgYwCceSfCCWWKPCxqqoyPhuCTUNIbeBr1WHVGZ4EO7kWZ94FG0ZdgPnmz4dlJYBYGTTUNEwzEMLiLlU5xqHKioBIl1UAHEh/MpY3ZzX78kuJo57Q3l8LZcNh0mTjPFnkYeGFhJA0sFiBpvFn/doWk+miWhWZbwAS8Ld+RDkctOHwpdtPhZF0tSM2X1sRFKjcLachtvgoxU+2wjgF4U+gcDjU3CZ1HQYP/gMPOw+CwE3fbZSeFT6kiTzWg7pB1+Rqd9XZSnyNWE83ySbv2+WzlpZ4u+GgAyhbPly5ErnJlwJuXxCZDmk0qzWTApzODgZiQ3iIO2KC8nMwFBEUZHG1vkWTyzJbGJyZoKaLrAUaFrf2v4GjvSONDiekcufR3GBVPkkU0XuPO4KFGn65ubIJ+IhHkUs0+npga3l+7JzZMPy5g7P09XKVQMwRYoT1TCd9XTtHOushVo2lMrvlWN58bSHHxUISJ+SRKN1kKmlihRJYZK0nGg2YDkmLFggUyISa6JQCpXUKk2WSE3MklSJNEI3UxZkgxOV8cSfo9enUVkBTruRxwEp5qSa182OvTQOvuYo3XU33eLEmQtXt91x170Rur35e2Twct8DIo/0WHAMzve8x+72xj32hNgGP/4CBPpWkLCNpWXKJjMiHEWOCN+ItOQfSsDIw2PgvrrzHvOEJ/Py+HjfPpB3KHWnyaaaZoqlplvrLj+42z0GWGCgYjNEuWaOCy6spFvMNoPziUWlXXF4y9upt+ANJY9EThjF278N1BMuQvwSkHhJkKBoMWIR4gjFIyUQSSSWRCKZVAqZVHJpFBZJr8JvfveHRAnqy/IxY7lGltljngBbkt4tppRBVRy/IYbpJdJFapk0smQXLKd11isoJFdee+2zwUabbPahj+z0fxZfdFWgUJGl6chTrKTZdnCid3O8HJF4P/rJFtkaauAFhRaaQAoVjdiVqKIpM9jQNF+jNq3a1RH4Kl2J0SlUh6deeua5V8V71dX89KJ0zfVAbTNVChkxOypLGcjKUoZAqtFckrvX1kVC9ZuOxDOUUNehQ5mnL6r+S12VNCtqm076cqS5o2ka336Nb1X1L8VGRXS9yHajrfUS+uXfyDr9Jm9kPeqsL0wos15Bp3LCWc52Pied45TTK1YTVdYzeBPgHBYARMFJ5zjl9H4bfzUO+SluD6O35qZKhbK0nGI9ZPBN3CQZMPqib8HU73dHZUD3h8Ij38yNbjn0tPwE0P+pq18i7h4o1sCA/oasdLkMGszVbPqj2u5r2vZurjj9QMjaSU7zQXF32obB8JmbEql01pSzZyGjzdrNgOHeBAVrpCSCRvPCV8OjkxHU4bqMIFWwQs0Coy1BT9RAfYM5VfAd6TRBiWiCObobVfX3OKBpXjcM5ue8kTv3gfJQNX38h1JfadRtKi7M1VTkCMcLIUHEXsc0ZV5vcOLPujz/2pxflZ7zb+A0AQA=",
}


PAGE = r"""<!doctype html><html lang="en" data-theme="dark"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover"><meta name="theme-color" content="#04060d"><link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png?v=2"><link rel="icon" href="/icon-192.png?v=2" type="image/png"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black"><meta name="apple-mobile-web-app-title" content="__SHOP__"><title>__SHOP__ Dashboard</title><script>window.NEXO_PREVIEW="__PREVIEW__"==="1";</script>
<script>(function(){try{var t=localStorage.getItem("theme");if(t==="light"||t==="dark")document.documentElement.dataset.theme=t;var a=localStorage.getItem("accent");if(a&&/^#[0-9a-f]{6}$/i.test(a))document.documentElement.style.setProperty("--accent",a);}catch(e){}})();</script>
<style>
@font-face{font-family:Sora;src:url(/font/sora.woff2) format("woff2");font-weight:100 800;font-display:swap}
@font-face{font-family:Manrope;src:url(/font/manrope.woff2) format("woff2");font-weight:200 800;font-display:swap}
:root{--onaccent:#031521;color-scheme:dark;--bg:#04060d;--panel:rgba(14,20,36,.6);--panel2:rgba(255,255,255,.05);--line:rgba(150,185,255,.14);--ink:#ecf3ff;--ink2:#b6c4e2;--muted:#8092b6;
--accent:#38bdf8;--accent2:color-mix(in srgb,var(--accent) 62%,#1a2f8a);--dot:#1b2640;--accentbg:color-mix(in srgb,var(--accent) 16%,transparent);--red:#fb7185;--redbg:#fb718518;--amber:#fbbf24;--amberbg:#fbbf2418;--tip:#0a1020;
--glass:rgba(10,15,30,.58);--solid:#0b1121;--glow:color-mix(in srgb,var(--accent) 40%,transparent);--ease:cubic-bezier(.16,1,.3,1);--spring:cubic-bezier(.34,1.56,.64,1);--r:20px;--hi:rgba(255,255,255,.06);--sh:rgba(0,0,0,.6)}
:root[data-theme=light]{color-scheme:light;--bg:#e9f0fb;--panel:rgba(255,255,255,.74);--panel2:rgba(14,40,90,.05);--line:rgba(20,50,110,.13);--ink:#0b1630;--ink2:#33446a;--muted:#5c6c8c;
--accent:#0a84d6;--dot:#c9d6ec;--red:#e11d48;--redbg:#e11d480f;--amber:#b45309;--amberbg:#b453090f;--tip:#0b1630;--glass:rgba(255,255,255,.7);--solid:#fff;--hi:rgba(255,255,255,.9);--sh:rgba(30,60,120,.28);--onaccent:#fff}
*{box-sizing:border-box}
[hidden]{display:none!important}
body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.5 Inter,system-ui,"Segoe UI",Arial,sans-serif;-webkit-font-smoothing:antialiased}
svg.i{width:18px;height:18px;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round;flex:none}
.app{display:grid;grid-template-columns:minmax(0,1fr) 240px;min-height:100vh}
main{padding:28px 36px 48px;min-width:0;max-width:1180px;width:100%;justify-self:center}
aside{position:sticky;top:0;height:100vh;border-left:1px solid var(--line);background:var(--panel);padding:22px 14px 18px;display:flex;flex-direction:column;gap:6px}
.brand{display:flex;align-items:center;gap:10px;padding:2px 10px 18px;font-weight:700;font-size:16px;letter-spacing:-.2px}
.logo{width:34px;height:34px;border-radius:9px;display:block;object-fit:cover}
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
.cal .cd b{font-size:13px;margin-top:8px;text-align:center;line-height:1.15}.cal .cd b em{font-style:normal;font-weight:500;font-size:9.5px;color:var(--muted);margin-left:3px}.cal .cd s{text-decoration:none;font-size:10.5px;color:var(--muted)}
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
@media(max-width:820px){.toasts{bottom:84px}.drawer{width:100vw}.quote{margin:-4px 0 12px}.cal .cd{min-height:54px}.cal .cd s{display:none}.cal .cd b em{display:block;margin:1px 0 0;font-size:8.5px}.header-tools .seg button{padding:6px 9px}}
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

/* round 3 */
.gr{display:inline-block;font-size:11px;font-weight:700;padding:2px 8px;border-radius:99px;white-space:nowrap}.gr.up{background:var(--accentbg);color:var(--accent)}.gr.down{background:color-mix(in srgb,var(--red) 16%,transparent);color:var(--red)}
.tile[data-help] .l:after,.panel[data-help]>h2:after{content:"\24D8";font-size:11px;color:var(--muted);opacity:.7;margin-left:4px;font-weight:400}
.helpb{position:fixed;z-index:120;max-width:min(320px,calc(100vw - 24px));background:var(--ink);color:var(--bg);border-radius:12px;padding:10px 13px;font-size:13px;line-height:1.45;box-shadow:0 12px 36px rgba(0,0,0,.4)}.helpb[hidden]{display:none}
.prog{border-bottom:1px solid var(--line);padding:12px 0}.prog:last-child{border-bottom:0}
.prog .ph{display:flex;align-items:center;gap:12px;flex-wrap:wrap}.prog .pn{flex:1 1 200px;min-width:0}.prog .pn small{display:block;color:var(--muted);font-size:12.5px}
.pdot{width:10px;height:10px;border-radius:99px;background:var(--muted);flex:none}.pdot.ok{background:var(--accent);box-shadow:0 0 0 4px var(--accentbg)}.pdot.bad{background:var(--red)}.pdot.warn{background:var(--amber)}
.plog{margin:10px 0 0;max-height:300px;overflow:auto;background:var(--panel2);border:1px solid var(--line);border-radius:10px;padding:10px 12px;font:12px/1.5 ui-monospace,Menlo,Consolas,monospace;white-space:pre-wrap;overflow-wrap:anywhere}
.plog .e{color:var(--red)}.plog .tt{color:var(--muted)}
.chrow{display:flex;gap:12px;padding:8px 0;border-bottom:1px solid var(--line)}.chrow:last-child{border-bottom:0}.chrow time{flex:none;width:92px;color:var(--muted);font-size:12.5px}
.mrow{display:flex;align-items:center;gap:10px;padding:8px 10px;border:1px solid var(--line);border-radius:10px;margin-bottom:6px;background:var(--panel2);cursor:grab}.mrow.drag{opacity:.4}.mrow.over{border-color:var(--accent)}
.mrow .nm{flex:1;min-width:0}.mrow button{border:0;background:none;color:var(--ink2);font-size:15px;padding:4px 7px;cursor:pointer;border-radius:8px}.mrow button:hover{background:var(--panel)}.mrow button.on{color:var(--amber)}
#nav a.pinned:after{content:"\2605";margin-left:auto;font-size:10px;color:var(--amber)}
@media(max-width:820px){#nav a.pinned:after{display:none}}
body.hide .prog .pn small{filter:none}

/* overview editing */
#ovg{display:grid;grid-template-columns:repeat(12,minmax(0,1fr));gap:14px}
#ovg #tiles,#ovg .grid,#ovg .grid2,#ovg #mini{display:contents}
#ovg .tile{grid-column:span 3}
#ovg [data-mod="chart"]{grid-column:span 7}#ovg [data-mod="latest"]{grid-column:span 5}#ovg [data-mod="pending"]{grid-column:span 6}
#ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 2}#ovg [data-mod="status"]{grid-column:span 12}
@media(max-width:1000px){#ovg .tile{grid-column:span 4}#ovg [data-mod="chart"],#ovg [data-mod="latest"],#ovg [data-mod="pending"]{grid-column:span 12}#ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 4}}
@media(max-width:560px){#ovg{gap:10px}#ovg .tile{grid-column:span 6}#ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 12}}
#ovbar{position:sticky;top:8px;z-index:30;margin-bottom:14px;display:flex;flex-wrap:wrap;gap:8px;align-items:center;padding:12px 16px}
#ovbar[hidden]{display:none}#ovbar .sp{flex:1}#ovbar .hint{color:var(--muted);font-size:13px}
body.ovedit #ovg [data-mod]{outline:2px dashed var(--line);outline-offset:2px;cursor:grab;user-select:none}
body.ovedit #ovg [data-mod].sel{outline:2px solid var(--accent)}body.ovedit #ovg [data-mod].drag{opacity:.4}body.ovedit #ovg [data-mod].over{outline:2px solid var(--accent);background:var(--accentbg,rgba(52,211,153,.08))}
body.ovedit #ovg [data-mod] *{pointer-events:none}

/* alarm bar + stock value + backups */
#alarm{position:fixed;top:0;left:0;right:0;z-index:300;background:#dc2626;color:#fff;text-align:center;font-weight:900;font-size:clamp(20px,4.2vw,34px);letter-spacing:.5px;padding:12px 16px;cursor:pointer;box-shadow:0 6px 24px rgba(220,38,38,.55);animation:alarmp 1.6s ease-in-out infinite}
#alarm small{display:block;font-size:13px;font-weight:600;letter-spacing:0;opacity:.95;margin-top:2px}#alarm[hidden]{display:none}
body.alarmon .app{padding-top:var(--alh,78px)}body.alarmon #nav{top:var(--alh,78px)}
@keyframes alarmp{50%{background:#b91c1c}}@media (prefers-reduced-motion:reduce){#alarm{animation:none}}
.ucost{display:flex;align-items:center;gap:8px;margin-top:8px;font-size:12.5px;color:var(--muted)}.ucost input{width:90px;padding:5px 8px;font-size:13px}
.bkrow{display:flex;gap:10px;align-items:center;justify-content:space-between;padding:10px 0;border-bottom:1px solid var(--line);flex-wrap:wrap}.bkrow:last-child{border:0}

/* war-room files, server page, password */
.wimg{display:block;max-width:min(280px,100%);max-height:240px;border-radius:10px;margin-top:6px;object-fit:cover}.bub .wimg:first-child{margin-top:0}
.wpdf{display:inline-block;margin-top:4px;color:var(--accent);font-weight:600;text-decoration:none}
.srv{display:grid;gap:0}.srv .r1{display:flex;justify-content:space-between;gap:14px;align-items:center;padding:11px 0;border-bottom:1px solid var(--line)}.srv .r1:last-child{border:0}
.srv .r1 small{display:block;color:var(--muted);font-size:12px}.srv .v{text-align:right;font-weight:600}.srv .qbar{margin:6px 0 0;min-width:140px}

/* =====================================================================
   NEXO EVO - the same dashboard, built up: living background, glowing slabs,
   sliding menu light, 3D gem cockpit, spotlight and motion everywhere.
   Loaded after the old rules; the pages keep working exactly as before.
   ===================================================================== */
@property --pc{syntax:"<color>";inherits:true;initial-value:#38bdf8}
:root{--pc:#38bdf8;--c1:#38bdf8;--c2:#a78bfa;--c3:#34d399;--c4:#fbbf24;--c5:#f472b6;--c6:#fb7185;--slab:#0a0c14;--hair:rgba(255,255,255,.09);--ring:rgba(255,255,255,.14)}
:root[data-theme=light]{--slab:#ffffff;--hair:rgba(15,40,100,.1);--ring:rgba(15,40,100,.18)}
body{transition:--pc 1.1s ease}
html{background:var(--bg)}
body{font-family:Manrope,system-ui,"Segoe UI",Arial,sans-serif;font-size:14.5px;line-height:1.55;background:var(--bg);caret-color:var(--accent);overflow-x:hidden}
::selection{background:color-mix(in srgb,var(--accent) 40%,transparent);color:var(--ink)}
*{scrollbar-width:thin;scrollbar-color:color-mix(in srgb,var(--muted) 45%,transparent) transparent}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:color-mix(in srgb,var(--muted) 40%,transparent);border-radius:99px;border:3px solid transparent;background-clip:content-box}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:10px}
h1,h2,h3,.tile .v,.big,.welcome b,.taxpot b,.cmdk-t,.ck-big,.ck-lab,.brand{font-family:Sora,Manrope,system-ui,sans-serif}

/* ---------- world: mesh, floor grid, grain ---------- */
#fxbg{position:fixed;inset:0;z-index:-1;overflow:hidden;pointer-events:none;background:#05060b}
:root[data-theme=light] #fxbg{background:#eef2fb}
#fxbg i{position:absolute;border-radius:50%;will-change:transform}
#fxbg .a1{width:70vmax;height:70vmax;left:-25vmax;top:-34vmax;background:radial-gradient(circle,color-mix(in srgb,var(--pc) 34%,transparent),transparent 62%);animation:drift1 38s ease-in-out infinite alternate}
#fxbg .a2{width:60vmax;height:60vmax;right:-26vmax;top:-6vmax;background:radial-gradient(circle,rgba(140,90,255,.30),transparent 62%);animation:drift2 46s ease-in-out infinite alternate}
#fxbg .a3{width:64vmax;height:64vmax;left:8vmax;bottom:-46vmax;background:radial-gradient(circle,rgba(244,114,182,.20),transparent 62%);animation:drift3 52s ease-in-out infinite alternate}
:root[data-theme=light] #fxbg .a1{background:radial-gradient(circle,color-mix(in srgb,var(--pc) 24%,transparent),transparent 62%)}
:root[data-theme=light] #fxbg .a2{background:radial-gradient(circle,rgba(150,120,255,.22),transparent 62%)}
:root[data-theme=light] #fxbg .a3{background:radial-gradient(circle,rgba(244,114,182,.16),transparent 62%)}
#fxbg .cur{width:620px;height:620px;left:-310px;top:-310px;background:radial-gradient(circle,color-mix(in srgb,var(--pc) 18%,transparent),transparent 66%);opacity:0;transition:opacity .6s}
body.mouse #fxbg .cur{opacity:1}
@keyframes drift1{to{transform:translate3d(16vmax,12vmax,0) scale(1.12)}}
@keyframes drift2{to{transform:translate3d(-18vmax,14vmax,0) scale(.92)}}
@keyframes drift3{to{transform:translate3d(12vmax,-14vmax,0) scale(1.1)}}
#fxbg .grain{position:absolute;inset:-50%;width:200%;height:200%;opacity:.09;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='200' height='200'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='.9' numOctaves='2' stitchTiles='stitch'/%3E%3CfeColorMatrix values='0 0 0 0 1 0 0 0 0 1 0 0 0 0 1 0 0 0 .55 0'/%3E%3C/filter%3E%3Crect width='200' height='200' filter='url(%23n)'/%3E%3C/svg%3E");animation:grain 1.1s steps(6) infinite}
:root[data-theme=light] #fxbg .grain{opacity:.05;filter:invert(1)}
@keyframes grain{0%{transform:translate(0,0)}20%{transform:translate(-4%,3%)}40%{transform:translate(3%,-5%)}60%{transform:translate(-5%,-2%)}80%{transform:translate(4%,4%)}100%{transform:translate(0,0)}}
#fxc{position:absolute;inset:0;width:100%;height:100%}
#fxcel{position:fixed;inset:0;width:100%;height:100%;pointer-events:none;z-index:400}
#fxbar{position:fixed;top:0;left:0;right:0;height:3px;z-index:500;pointer-events:none;opacity:0;transition:opacity .25s;background:linear-gradient(90deg,transparent,var(--accent),#f472b6,var(--accent),transparent);background-size:60% 100%;background-repeat:no-repeat;animation:fxbar 1.1s linear infinite}
#fxbar.on{opacity:1}
@keyframes fxbar{from{background-position:-60% 0}to{background-position:160% 0}}
#fxflash{position:fixed;inset:0;z-index:380;pointer-events:none;opacity:0;background:radial-gradient(120% 90% at 50% 100%,color-mix(in srgb,var(--accent) 38%,transparent),transparent 62%);box-shadow:inset 0 0 120px 10px color-mix(in srgb,var(--accent) 45%,transparent)}
#fxflash.on{animation:flash 1.3s ease-out}
@keyframes flash{0%{opacity:0}15%{opacity:1}100%{opacity:0}}

/* ---------- layout: work area left, glass menu right (as before) ---------- */
.app{display:grid;grid-template-columns:minmax(0,1fr) 268px;min-height:100vh;gap:0;padding:0}
main{display:block;min-width:0;max-width:1340px;width:100%;margin:0 auto;padding:34px 40px 80px}
body.alarmon .app{padding-top:var(--alh,78px)}
header{position:relative;display:flex;flex-wrap:wrap;gap:14px 20px;align-items:center;justify-content:space-between;margin:0 0 26px}
header>div:first-child{min-width:0}
h1{font-size:clamp(34px,3.7vw,54px);font-weight:800;letter-spacing:-.045em;line-height:1.04;margin:0;color:var(--ink);text-shadow:0 0 40px color-mix(in srgb,var(--pc) 45%,transparent)}
h1 .ch{display:inline-block;will-change:transform}
.sub{display:inline-flex;align-items:center;gap:8px;margin-top:10px;padding:5px 14px;border-radius:99px;border:1px solid var(--hair);background:var(--panel2);font-size:12.5px;font-weight:700;color:var(--ink2)}
.sub:before{content:"";width:7px;height:7px;border-radius:50%;background:var(--pc);box-shadow:0 0 10px var(--pc)}
.header-tools{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}
.live{font-weight:600;font-size:13px;white-space:nowrap}
.dot{position:relative;box-shadow:0 0 12px var(--accent)}
.dot:after{content:"";position:absolute;inset:-4px;border-radius:50%;border:1.5px solid var(--accent);opacity:0;animation:ping 2.4s ease-out infinite}
.dot.stale:after{border-color:var(--amber)}
@keyframes ping{0%{transform:scale(.6);opacity:.9}100%{transform:scale(2.2);opacity:0}}
.quote{text-align:left;font-size:13.5px;margin:0 0 6px;padding:0}
.taxpot{justify-content:flex-start;margin:0 0 18px;font-size:13.5px;text-align:left}
.taxpot b{color:var(--accent);font-size:18px}.taxpot small{flex-basis:auto}

/* ---------- glass menu with a sliding light ---------- */
aside{position:sticky;top:0;height:100vh;border-left:1px solid var(--hair);background:linear-gradient(180deg,rgba(255,255,255,.05),rgba(255,255,255,.01)),color-mix(in srgb,var(--bg) 78%,transparent);-webkit-backdrop-filter:blur(24px) saturate(150%);backdrop-filter:blur(24px) saturate(150%);padding:22px 14px 16px;display:flex;flex-direction:column;gap:6px;z-index:30;overflow:hidden}
:root[data-theme=light] aside{background:rgba(255,255,255,.62)}
body.alarmon aside{top:var(--alh,78px);height:calc(100vh - var(--alh,78px))}
.brand{display:flex;align-items:center;gap:12px;padding:2px 8px 18px;margin:0;font-size:18px;font-weight:800;letter-spacing:-.4px;font-family:Sora,sans-serif}
.brand>span:not(.logowrap){overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.logowrap{position:relative;display:block;flex:none;width:40px;height:40px;border-radius:13px;overflow:hidden;cursor:pointer;box-shadow:0 0 0 1px var(--ring),0 10px 28px -8px color-mix(in srgb,var(--pc) 70%,transparent);transition:transform .6s var(--spring)}
.logowrap:hover{transform:rotate(-10deg) scale(1.12)}
.logowrap .logo,.logo{width:40px;height:40px;border-radius:0;display:block;object-fit:cover}
.logowrap:after{content:"";position:absolute;inset:-20%;background:linear-gradient(105deg,transparent 40%,rgba(255,255,255,.6) 50%,transparent 60%);transform:translateX(-120%);animation:shine 6s ease-in-out infinite}
@keyframes shine{0%,70%{transform:translateX(-120%)}100%{transform:translateX(120%)}}
nav{position:relative;display:flex;flex-direction:column;gap:3px;flex:1;overflow-y:auto;overflow-x:hidden;scrollbar-width:none}
nav::-webkit-scrollbar{display:none}
nav a{position:relative;z-index:1;display:flex;align-items:center;gap:13px;flex:none;padding:11px 14px;border-radius:15px;color:var(--ink2);font-weight:700;font-size:14px;text-decoration:none;background:none;transition:color .2s,transform .4s var(--spring)}
nav a svg.i{width:19px;height:19px;transition:transform .45s var(--spring),color .25s,filter .3s}
nav a:hover{background:none;color:var(--ink);transform:translateX(-5px)}
nav a:hover svg.i{transform:scale(1.2) rotate(-7deg)}
nav a.on{background:none;color:var(--ink)}
nav a.on svg.i{color:var(--pc);filter:drop-shadow(0 0 8px var(--pc))}
.navind{position:absolute;left:0;top:0;width:0;height:0;border-radius:15px;z-index:0;pointer-events:none;background:linear-gradient(100deg,color-mix(in srgb,var(--pc) 30%,transparent),color-mix(in srgb,var(--pc) 6%,transparent));box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--pc) 45%,transparent),0 12px 30px -14px var(--pc);transition:top .55s var(--ease),left .55s var(--ease),width .55s var(--ease),height .55s var(--ease),opacity .3s;opacity:0}
.navind.ready{opacity:1}
.navind:before{content:"";position:absolute;right:0;top:22%;bottom:22%;width:3px;border-radius:3px;background:var(--pc);box-shadow:0 0 12px var(--pc)}
.badge{margin-left:auto;background:linear-gradient(135deg,#fb7185,#e11d48);box-shadow:0 0 14px #e11d4899;animation:badgep 2.2s ease-in-out infinite;font-size:10.5px;line-height:16px;padding:0 6px}
@keyframes badgep{50%{transform:scale(1.18)}}
.newdot{margin-left:auto;width:8px;height:8px;background:var(--accent);box-shadow:0 0 10px var(--accent);border-radius:50%}
.me{margin-top:auto;display:flex;align-items:center;gap:11px;padding:14px 8px 0;border-top:1px solid var(--hair)}
.me b{font-size:13px}.me small{display:block;line-height:1.1}
.av{width:38px;height:38px;border-radius:50%;background:conic-gradient(from 200deg,var(--accent),#a78bfa,#f472b6,var(--accent));border:0;color:var(--ink);font-family:Sora;font-weight:800;position:relative;box-shadow:0 8px 24px -8px var(--accent);isolation:isolate;display:grid;place-items:center}
.av:after{content:"";position:absolute;inset:2px;border-radius:50%;background:var(--slab);z-index:-1}

/* ---------- slabs (cards) ---------- */
.tile,.panel{--c:var(--accent);position:relative;isolation:isolate;overflow:hidden;background:radial-gradient(120% 90% at 0% 0%,color-mix(in srgb,var(--c) 16%,transparent),transparent 58%),linear-gradient(165deg,rgba(255,255,255,.07),rgba(255,255,255,.015) 55%),var(--slab);border:1px solid var(--hair);border-radius:28px;box-shadow:inset 0 1px 0 rgba(255,255,255,.08),0 40px 70px -44px rgba(0,0,0,.95);transition:transform .5s var(--ease),border-color .35s,box-shadow .5s;-webkit-backdrop-filter:none;backdrop-filter:none}
:root[data-theme=light] .tile,:root[data-theme=light] .panel{background:radial-gradient(120% 90% at 0% 0%,color-mix(in srgb,var(--c) 11%,transparent),transparent 58%),var(--slab);box-shadow:0 1px 0 #fff inset,0 24px 50px -28px rgba(40,70,140,.35)}
.tile:before,.panel:before{content:"";position:absolute;inset:0;z-index:-1;border-radius:inherit;pointer-events:none;background:radial-gradient(460px circle at var(--mx,50%) var(--my,0%),color-mix(in srgb,var(--c) 22%,transparent),transparent 62%);opacity:0;transition:opacity .4s}
.tile:after,.panel:after{content:"";position:absolute;inset:0;z-index:2;border-radius:inherit;padding:1.5px;pointer-events:none;background:radial-gradient(280px circle at var(--mx,50%) var(--my,0%),color-mix(in srgb,var(--c) 90%,#fff),transparent 65%);-webkit-mask:linear-gradient(#000 0 0) content-box,linear-gradient(#000 0 0);-webkit-mask-composite:xor;mask:linear-gradient(#000 0 0) content-box exclude,linear-gradient(#000 0 0);opacity:0;transition:opacity .4s}
.tile:hover:before,.panel:hover:before,.tile:hover:after,.panel:hover:after{opacity:1}
.panel.chat:hover:before,.panel.chat:hover:after,.panel.welcome:before{opacity:.4}
.tile:hover{box-shadow:inset 0 1px 0 rgba(255,255,255,.1),0 40px 80px -34px color-mix(in srgb,var(--c) 60%,transparent)}
[data-mod=today],[data-mod=month],[data-mod=all],[data-mod=avg],[data-mod=forecast],[data-mod=chart]{--c:var(--c1)}
[data-mod=lastorder],[data-mod=latest],[data-mod=pending],[data-mod=others]{--c:var(--c2)}
[data-mod=stock],[data-mod=stockval],[data-mod=stockp]{--c:var(--c4)}
[data-mod=keys]{--c:var(--c3)}[data-mod=profit]{--c:var(--c3)}
[data-mod=reviews],[data-mod=revrate]{--c:var(--c5)}
[data-mod=status]{--c:var(--c6)}
.tile{padding:22px 24px 20px;min-height:158px;display:flex;flex-direction:column}
.tile .l{font-weight:700;font-size:12.5px;color:var(--ink2);letter-spacing:.01em}
.tile .v{font-size:clamp(28px,2.7vw,40px);font-weight:800;letter-spacing:-.045em;margin:auto 0 4px;padding-top:14px;font-variant-numeric:tabular-nums;line-height:1}
.tile .v small{font-family:Manrope;font-size:13px;font-weight:700;letter-spacing:0}
.tile .s{font-size:12.5px;position:relative;z-index:1}
.tile .wm{position:absolute;right:-14px;bottom:-16px;width:112px;height:112px;z-index:-1;color:var(--c);opacity:.13;fill:none;stroke:currentColor;stroke-width:1.4;stroke-linecap:round;stroke-linejoin:round;transform:rotate(-8deg);transition:transform .8s var(--spring),opacity .5s}
.tile:hover .wm{transform:rotate(4deg) scale(1.14);opacity:.26}
.tile .spark{position:absolute;left:0;right:0;bottom:0;height:38%;width:100%;z-index:-1;pointer-events:none;opacity:.5}
.tile .spark path.f{fill:url(#fxsp)}.tile .spark path.s{fill:none;stroke:var(--c);stroke-width:2;stroke-linecap:round;stroke-linejoin:round;filter:drop-shadow(0 0 6px var(--c));stroke-dasharray:var(--len,900);stroke-dashoffset:var(--len,900);animation:draw 1.8s .3s var(--ease) forwards}
@keyframes draw{to{stroke-dashoffset:0}}
.tile .ringw{position:absolute;right:18px;top:18px;width:66px;height:66px}
.tile .ringw svg{width:100%;height:100%;transform:rotate(-90deg)}
.tile .ringw circle{fill:none;stroke-width:6;stroke-linecap:round}
.tile .ringw .t{stroke:color-mix(in srgb,var(--c) 18%,transparent)}.tile .ringw .p{stroke:var(--c);filter:drop-shadow(0 0 6px var(--c));stroke-dasharray:var(--cl) var(--cl);stroke-dashoffset:var(--cl);animation:ringin 1.6s .3s var(--ease) forwards}
@keyframes ringin{to{stroke-dashoffset:var(--co)}}
.tile .ringw b{position:absolute;inset:0;display:grid;place-items:center;font:800 13px Sora;color:var(--ink)}
.tiles .tile:first-child{--c:var(--c1)}
.panel{padding:24px 26px}
.panel h2{font-size:16px;font-weight:700;letter-spacing:-.2px;margin-bottom:18px}
.panel h2 a,.panel h2 span{transition:color .2s}
.welcome{padding:0;min-height:0;background:none;border:0;box-shadow:none;overflow:visible;display:block;margin:0}
.welcome:before,.welcome:after{display:none}
.welcome b{font-size:clamp(17px,1.6vw,22px);font-weight:700;letter-spacing:-.4px;display:block}
.welcome .w2{font-size:14px;margin-top:4px}
.rec{background:linear-gradient(135deg,rgba(251,191,36,.22),rgba(251,113,133,.18));box-shadow:inset 0 0 0 1px rgba(251,191,36,.35)}
.gr{font-weight:800}

/* ---------- buttons, controls ---------- */
button.btn,a.btn{position:relative;overflow:hidden;background:rgba(255,255,255,.06);border:1px solid var(--hair);color:var(--ink);border-radius:99px;padding:9px 16px;font-weight:700;transition:transform .3s var(--spring),border-color .25s,background .25s,box-shadow .3s,color .2s}
:root[data-theme=light] button.btn,:root[data-theme=light] a.btn{background:rgba(255,255,255,.8)}
button.btn:hover,a.btn:hover{border-color:color-mix(in srgb,var(--accent) 70%,transparent);background:color-mix(in srgb,var(--accent) 12%,rgba(255,255,255,.04));box-shadow:0 12px 30px -12px var(--accent);transform:translateY(-2px)}
button.btn:active,a.btn:active{transform:translateY(1px) scale(.95);transition-duration:.08s}
button.btn:disabled{opacity:.45;transform:none;box-shadow:none}
button.icon,button.btn.icon{padding:0;width:40px;height:40px;display:inline-grid;place-items:center}
button.primary,button.btn.primary{background:linear-gradient(135deg,var(--accent),color-mix(in srgb,var(--accent) 50%,#c084fc));color:var(--onaccent);border:0;font-weight:800;box-shadow:0 14px 36px -12px var(--accent),inset 0 1px 0 rgba(255,255,255,.45)}
button.primary:after{content:"";position:absolute;inset:0;background:linear-gradient(105deg,transparent 35%,rgba(255,255,255,.6) 50%,transparent 65%);transform:translateX(-130%);transition:transform .8s var(--ease)}
button.primary:hover:after{transform:translateX(130%)}
.btn.on{box-shadow:inset 0 0 0 1.5px var(--accent)}
.seg{border-radius:99px;border:1px solid var(--hair);background:rgba(255,255,255,.05);padding:3px;gap:2px;display:inline-flex}
.seg button{border-radius:99px;padding:7px 14px;font-weight:700;transition:background .3s,color .25s,box-shadow .3s}
.seg button+button{border-left:0}
.seg button.on{background:linear-gradient(135deg,var(--accent),color-mix(in srgb,var(--accent) 50%,#c084fc));color:var(--onaccent);box-shadow:0 8px 22px -8px var(--accent)}
.chip{border-radius:99px;transition:transform .3s var(--spring),border-color .25s,background .25s}.chip:hover{transform:translateY(-2px)}.chip:active{transform:scale(.93)}
.chip.on{background:color-mix(in srgb,var(--accent) 20%,transparent);box-shadow:0 0 22px -6px var(--accent)}
input,select,textarea{background:rgba(255,255,255,.05);border:1px solid var(--hair);border-radius:16px;transition:border-color .25s,box-shadow .3s,background .25s}
:root[data-theme=light] input,:root[data-theme=light] select,:root[data-theme=light] textarea{background:#fff}
input:focus,select:focus,textarea:focus{outline:0;border-color:var(--accent);box-shadow:0 0 0 4px color-mix(in srgb,var(--accent) 18%,transparent),0 14px 34px -14px var(--accent)}
select.sel{border-radius:99px;padding:9px 14px;font-weight:700}
input[type=checkbox]{appearance:none;-webkit-appearance:none;width:46px;height:28px;border-radius:99px;background:rgba(255,255,255,.12);border:1px solid var(--hair);position:relative;cursor:pointer;flex:none;padding:0;transition:background .3s,box-shadow .3s}
input[type=checkbox]:after{content:"";position:absolute;left:3px;top:3px;width:20px;height:20px;border-radius:50%;background:#fff;box-shadow:0 2px 8px rgba(0,0,0,.4);transition:transform .45s var(--spring)}
input[type=checkbox]:checked{background:linear-gradient(135deg,var(--accent),color-mix(in srgb,var(--accent) 50%,#c084fc));box-shadow:0 0 22px -4px var(--accent);border-color:transparent}
input[type=checkbox]:checked:after{transform:translateX(18px)}
.tgl input{width:46px;height:28px}
.pill{display:inline-flex;align-items:center;gap:6px;padding:3px 12px;font-weight:800;border-radius:99px}
.pill.good{box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--accent) 35%,transparent)}
.pill.bad{box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--red) 40%,transparent)}
.pill.warn{box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--amber) 40%,transparent)}
.pill.warn:before{content:"";width:6px;height:6px;border-radius:50%;background:var(--amber);box-shadow:0 0 8px var(--amber);animation:pulse 1.8s ease-in-out infinite}
@keyframes pulse{50%{transform:scale(1.5);opacity:.6}}

/* tables become rows of floating pills */
table{border-collapse:separate;border-spacing:0 6px}
th{font-weight:700;border-bottom:0;padding:0 12px 4px 12px}
td{border-bottom:0;padding:13px 12px;background:rgba(255,255,255,.035);transition:background .25s}
td:first-child{border-radius:16px 0 0 16px}td:last-child{border-radius:0 16px 16px 0}
tr:last-child td{border-bottom:0}
tr.click:hover td{background:color-mix(in srgb,var(--accent) 12%,rgba(255,255,255,.04))}
tr.click td:first-child{box-shadow:inset 0 0 0 0 var(--accent);transition:box-shadow .3s,background .25s}tr.click:hover td:first-child{box-shadow:inset 4px 0 0 0 var(--accent)}
.row2,.rows .r1,.hrow,.statrow,.urow,.bkrow,.srv .r1,.chrow{border-bottom:0;border-radius:16px;padding:12px 14px;margin:0 -4px 4px;background:rgba(255,255,255,.03);transition:background .25s,transform .4s var(--ease)}
.row2:hover,.rows .r1:hover,.hrow:hover,.statrow:hover,.urow:hover,.srv .r1:hover{background:color-mix(in srgb,var(--accent) 9%,rgba(255,255,255,.03));transform:translateX(4px)}
.row2:last-child,.rows .r1:last-child,.hrow:last-child,.statrow:last-child,.urow:last-child{margin-bottom:0}
.hday{border-bottom:0;margin:20px 0 8px;font-family:Sora}
.rev{border-bottom:0;padding:16px 18px;margin-bottom:8px;border-radius:20px;background:rgba(255,255,255,.035)}
.qbar{height:8px;background:rgba(255,255,255,.07)}
.qbar i{background:linear-gradient(90deg,var(--accent2),var(--accent));box-shadow:0 0 14px -2px var(--accent);transform-origin:left;animation:qgrow 1.2s var(--ease) both}
@keyframes qgrow{from{transform:scaleX(0)}}
.big{font-weight:800;letter-spacing:-.05em}
.err{border:1px solid color-mix(in srgb,var(--red) 35%,transparent);border-radius:16px}

/* charts */
.bar{fill:var(--accent2);fill:url(#fxbar) var(--accent2);transform-box:fill-box;transform-origin:50% 100%;animation:barin 1.2s var(--ease) both;animation-delay:calc(var(--i,0)*80ms + 140ms);filter:drop-shadow(0 0 12px color-mix(in srgb,var(--accent) 35%,transparent));transition:filter .3s}
.bar.cur{fill:var(--accent);fill:url(#fxbarcur) var(--accent);filter:drop-shadow(0 0 18px var(--accent))}
@keyframes barin{from{transform:scaleY(.02);opacity:.2}}
.val{animation:fade .6s .9s both}.tx{animation:fade .6s .3s both}
@keyframes fade{from{opacity:0}}
.gl{stroke:var(--hair);stroke-dasharray:3 7}
.tip{background:var(--slab);color:var(--ink);border:1px solid var(--ring);box-shadow:0 16px 44px -10px rgba(0,0,0,.8);border-radius:14px;font-weight:700}
.hit{cursor:crosshair}
.cal .cd{border-radius:16px;transition:transform .4s var(--spring),border-color .25s,box-shadow .3s}
.cal .cd:hover{transform:translateY(-4px) scale(1.09);z-index:2;box-shadow:0 18px 36px -12px var(--accent);border-color:var(--accent)}
.cal .cd.today{box-shadow:0 0 0 1.5px var(--accent),0 0 26px -4px var(--accent)}
.sk{background:linear-gradient(100deg,rgba(255,255,255,.05) 30%,color-mix(in srgb,var(--accent) 16%,rgba(255,255,255,.05)) 50%,rgba(255,255,255,.05) 70%);background-size:300% 100%;animation:sk 1.5s linear infinite;border-radius:14px}
.sk.tile{min-height:158px}

/* drawer, toasts, calc */
.veil{background:rgba(2,3,8,.6);-webkit-backdrop-filter:blur(8px);backdrop-filter:blur(8px);transition:opacity .4s}
.drawer{background:linear-gradient(180deg,rgba(255,255,255,.07),rgba(255,255,255,.02)),rgba(10,12,20,.9);-webkit-backdrop-filter:blur(34px) saturate(170%);backdrop-filter:blur(34px) saturate(170%);border:1px solid var(--ring);border-right:0;border-radius:30px 0 0 30px;box-shadow:-50px 0 100px -30px rgba(0,0,0,.9);transition:transform .7s var(--ease)}
:root[data-theme=light] .drawer{background:rgba(255,255,255,.92)}
.drawer .dh2{border-bottom:1px solid var(--hair)}
.toast2{position:relative;overflow:hidden;background:linear-gradient(135deg,rgba(255,255,255,.1),rgba(255,255,255,.03)),rgba(10,12,20,.88);color:var(--ink);border:1px solid var(--ring);-webkit-backdrop-filter:blur(24px);backdrop-filter:blur(24px);box-shadow:0 24px 60px -16px rgba(0,0,0,.8),0 0 0 1px color-mix(in srgb,var(--accent) 25%,transparent);border-radius:20px;padding:14px 18px;animation:tin .7s var(--spring);transition:transform .25s}
:root[data-theme=light] .toast2{background:rgba(255,255,255,.95)}
.toast2:hover{transform:translateX(-5px)}
.toast2:after{content:"";position:absolute;left:0;bottom:0;height:3px;width:100%;background:linear-gradient(90deg,var(--accent),#f472b6);transform-origin:left;animation:tbar 7s linear both}
@keyframes tin{from{transform:translateX(50px) scale(.9);opacity:0}}
@keyframes tbar{to{transform:scaleX(0)}}
.toast2 b{font-family:Sora;font-size:14px}
.toasts{bottom:24px}
.helpb{background:var(--slab);color:var(--ink);border:1px solid var(--ring);box-shadow:0 24px 60px -14px rgba(0,0,0,.8)}
.calc{background:rgba(10,12,20,.88);-webkit-backdrop-filter:blur(28px);backdrop-filter:blur(28px);border:1px solid var(--ring);border-radius:26px;box-shadow:0 34px 90px -24px rgba(0,0,0,.9);top:84px}
:root[data-theme=light] .calc{background:rgba(255,255,255,.94)}
.ptr{background:var(--slab);box-shadow:0 8px 24px -8px var(--accent)}
.dropall{backdrop-filter:blur(8px);border-radius:30px}
.drop{border-radius:20px}

/* chat */
.bub{border-radius:20px 20px 20px 6px;background:rgba(255,255,255,.06);border-color:var(--hair)}
.m.mine .bub{border-radius:20px 20px 6px 20px;background:linear-gradient(135deg,color-mix(in srgb,var(--accent) 38%,transparent),rgba(168,85,247,.28));border-color:color-mix(in srgb,var(--accent) 30%,transparent)}
.msgs .m.fresh{animation:msgin .6s var(--spring) both}
@keyframes msgin{from{opacity:0;transform:translateY(16px) scale(.94)}}
.send{padding:8px;border-radius:99px;background:rgba(255,255,255,.05);border:1px solid var(--hair);align-items:center}
.send textarea{border:0;background:none;border-radius:99px;padding:10px 14px;box-shadow:none!important}
.onl i{box-shadow:0 0 8px var(--accent)}
.mmboard{border-radius:28px;background-color:rgba(255,255,255,.02)}
.pdot.ok{box-shadow:0 0 0 4px var(--accentbg),0 0 14px var(--accent)}
.relnote{border-left:0;position:relative;padding-left:20px}.relnote:before{content:"";position:absolute;left:0;top:2px;bottom:2px;width:4px;border-radius:4px;background:linear-gradient(var(--accent),#f472b6)}
body.ovedit #ovg [data-mod]{outline:2px dashed color-mix(in srgb,var(--accent) 50%,transparent);animation:wob .45s ease-in-out infinite alternate}
@keyframes wob{from{transform:rotate(-.3deg)}to{transform:rotate(.3deg)}}
body.ovedit #ovg [data-mod].drag{animation:none}
#ovbar{border-radius:99px}
/* ---------- overview grid ---------- */
#ovg{gap:16px}
#ovg .tile{grid-column:span 3}
#ovg [data-mod="chart"]{grid-column:span 8}#ovg [data-mod="latest"]{grid-column:span 4}
#ovg [data-mod="pending"]{grid-column:span 8;grid-row:span 3}
#ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 4}
#ovg [data-mod="status"]{grid-column:span 12}
/* ---------- cockpit ---------- */
#cockpit{position:relative;display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,.85fr);align-items:stretch;gap:0;margin:0 0 18px;border-radius:32px;overflow:hidden;border:1px solid var(--hair);background:radial-gradient(90% 130% at 0% 0%,color-mix(in srgb,var(--pc) 20%,transparent),transparent 60%),radial-gradient(70% 110% at 100% 100%,rgba(168,85,247,.22),transparent 62%),var(--slab);box-shadow:inset 0 1px 0 rgba(255,255,255,.1),0 50px 90px -50px rgba(0,0,0,.95)}
#cockpit:before{content:"";position:absolute;inset:0;border-radius:inherit;padding:1.5px;pointer-events:none;background:conic-gradient(from var(--ang,0deg),transparent 0 70%,var(--pc) 85%,transparent 100%);-webkit-mask:linear-gradient(#000 0 0) content-box,linear-gradient(#000 0 0);-webkit-mask-composite:xor;mask:linear-gradient(#000 0 0) content-box exclude,linear-gradient(#000 0 0);animation:ang 7s linear infinite;opacity:.9}
@property --ang{syntax:"<angle>";inherits:false;initial-value:0deg}
@keyframes ang{to{--ang:360deg}}
.ck-left{position:relative;z-index:2;min-width:0;padding:26px 8px 22px 32px}
.ck-lab{display:inline-flex;align-items:center;gap:10px;font-weight:700;font-size:13px;color:var(--ink2);margin:0 0 4px}
.ck-lab i{width:8px;height:8px;border-radius:50%;background:var(--c1);box-shadow:0 0 14px var(--c1);animation:pulse 2s ease-in-out infinite}
.ck-big{display:flex;align-items:flex-end;flex-wrap:wrap;gap:0 14px;font-weight:800;font-size:clamp(48px,6.4vw,104px);line-height:.98;letter-spacing:-.06em;font-variant-numeric:tabular-nums;filter:drop-shadow(0 0 28px color-mix(in srgb,var(--c1) 40%,transparent))}
.ck-big small{font:700 clamp(16px,1.8vw,24px) Manrope;letter-spacing:0;color:var(--muted);padding-bottom:.55em;text-shadow:none}
.odo{display:inline-flex;height:1em;overflow:hidden;line-height:1}
.odo>span{display:inline-block;height:1em;overflow:hidden}
.odo>span>b{display:flex;flex-direction:column;font-weight:inherit;transition:transform 1.4s cubic-bezier(.16,1,.3,1);transform:translateY(calc(var(--d,0)*-1em))}
.odo>span>b>i{display:block;height:1em;font-style:normal;line-height:1}
.ck-sub{font-size:15px;color:var(--ink2);margin-top:6px;font-weight:600}
.ck-chips{display:flex;flex-wrap:wrap;gap:8px;margin-top:18px}
.ck-chip{display:inline-flex;align-items:center;gap:8px;padding:8px 15px;border-radius:99px;font-weight:800;font-size:13px;color:var(--ink);border:1px solid var(--hair);background:rgba(255,255,255,.05);cursor:pointer;text-decoration:none;transition:transform .35s var(--spring),border-color .25s,box-shadow .3s;-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
.ck-chip:hover{transform:translateY(-3px);border-color:var(--cc);box-shadow:0 14px 30px -12px var(--cc)}
.ck-chip i{width:8px;height:8px;border-radius:50%;background:var(--cc);box-shadow:0 0 10px var(--cc)}
.ck-chip b{font-family:Sora}
.ck-bars{display:flex;align-items:flex-end;gap:4px;height:54px;margin-top:22px;max-width:520px}
.ck-bars i{flex:1;min-width:4px;border-radius:5px 5px 2px 2px;background:linear-gradient(180deg,var(--c1),color-mix(in srgb,var(--c1) 30%,transparent));height:calc(var(--h,0)*100%);min-height:3px;opacity:.85;transform-origin:bottom;animation:barin 1.1s var(--ease) both;animation-delay:calc(var(--i,0)*28ms)}
.ck-bars i.now{background:linear-gradient(180deg,#fff,var(--c1));box-shadow:0 0 16px var(--c1);opacity:1}
.ck-cap{display:flex;justify-content:space-between;max-width:520px;font-size:11px;color:var(--muted);font-weight:600;margin-top:5px}
.ck-gem{position:relative;height:100%;min-height:360px;display:grid;place-items:center;touch-action:pan-y}
#gem{width:100%;height:100%;min-height:360px;cursor:grab;touch-action:pan-y;display:block}
#gem.drag{cursor:grabbing}
.ck-hint{position:absolute;left:50%;bottom:6px;transform:translateX(-50%);font-size:11.5px;font-weight:700;color:var(--muted);display:flex;gap:8px;align-items:center;pointer-events:none;opacity:.8}
.ck-hint:before{content:"";width:18px;height:18px;border-radius:50%;border:1.5px solid var(--muted);box-shadow:inset 0 0 0 4px transparent;animation:nudge 2.4s ease-in-out infinite}
@keyframes nudge{50%{transform:translateX(8px)}}
.ck-ticker{grid-column:1/-1;position:relative;overflow:hidden;border-top:1px solid var(--hair);background:rgba(255,255,255,.03);}
.ck-track{display:flex;gap:10px;width:max-content;padding:9px 6px;animation:tick var(--tk,60s) linear infinite}
.ck-ticker:hover .ck-track{animation-play-state:paused}
@keyframes tick{to{transform:translateX(-50%)}}
.ck-ord{display:inline-flex;align-items:center;gap:10px;padding:6px 14px 6px 8px;border-radius:99px;background:rgba(255,255,255,.05);white-space:nowrap;font-size:13px;cursor:pointer;transition:background .25s,transform .3s var(--spring)}
.ck-ord:hover{background:color-mix(in srgb,var(--c2) 22%,transparent);transform:scale(1.04)}
.ck-ord s{text-decoration:none;display:grid;place-items:center;width:26px;height:26px;border-radius:50%;background:linear-gradient(135deg,var(--c2),var(--c1));color:#fff;font:800 11px Sora}
.ck-ord b{font-family:Sora}.ck-ord em{font-style:normal;color:var(--muted)}
.ck-ord.new{animation:newo 1.6s var(--spring) both;box-shadow:0 0 0 1px var(--c1),0 0 30px -4px var(--c1)}
@keyframes newo{from{transform:scale(.4);opacity:0}}
body.hide .ck-big,body.hide .ck-sub,body.hide .ck-bars,body.hide .ck-ord b,body.hide .ck-chip b{filter:blur(12px);user-select:none}
/* ---------- command palette ---------- */
#cmdk{position:fixed;inset:0;z-index:450;display:none;align-items:flex-start;justify-content:center;padding:14vh 16px 16px;background:rgba(2,3,8,.6);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}
#cmdk.on{display:flex;animation:fade .2s both}
.cmdk-box{width:min(660px,100%);background:linear-gradient(180deg,rgba(255,255,255,.08),rgba(255,255,255,.02)),rgba(10,12,20,.9);border:1px solid var(--ring);border-radius:28px;box-shadow:0 50px 120px -20px rgba(0,0,0,.95),0 0 0 1px color-mix(in srgb,var(--accent) 22%,transparent);-webkit-backdrop-filter:blur(34px) saturate(170%);backdrop-filter:blur(34px) saturate(170%);overflow:hidden;animation:cmdin .55s var(--spring) both}
:root[data-theme=light] .cmdk-box{background:rgba(255,255,255,.94)}
@keyframes cmdin{from{opacity:0;transform:translateY(-22px) scale(.93)}}
.cmdk-in{display:flex;align-items:center;gap:12px;padding:18px 22px;border-bottom:1px solid var(--hair)}
.cmdk-in input{flex:1;border:0;background:none;box-shadow:none!important;font-size:18px;padding:4px 0;border-radius:0}
.cmdk-in kbd,.cmdk-f kbd,#cmdkbtn kbd{font:700 11px Manrope;border:1px solid var(--hair);border-radius:7px;padding:2px 7px;color:var(--muted);background:rgba(255,255,255,.05)}
.cmdk-l{max-height:min(52vh,420px);overflow:auto;padding:8px}
.cmdk-g{font:800 11.5px Manrope;color:var(--muted);padding:12px 14px 5px}
.cmdk-i{display:flex;align-items:center;gap:13px;padding:11px 14px;border-radius:16px;cursor:pointer;color:var(--ink2);transition:background .15s,transform .3s var(--ease)}
.cmdk-i svg.i{color:var(--muted);transition:color .2s}
.cmdk-i.on{background:linear-gradient(100deg,color-mix(in srgb,var(--accent) 24%,transparent),color-mix(in srgb,var(--accent) 5%,transparent));color:var(--ink);transform:translateX(4px);box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--accent) 30%,transparent)}
.cmdk-i.on svg.i{color:var(--accent)}
.cmdk-i small{margin-left:auto;color:var(--muted);font-size:12px;white-space:nowrap}
.cmdk-i b{font-weight:700;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.cmdk-e{padding:28px;text-align:center;color:var(--muted)}
.cmdk-f{display:flex;gap:16px;padding:11px 20px;border-top:1px solid var(--hair);color:var(--muted);font-size:12px}
#cmdkbtn{gap:10px;padding:0 14px;height:40px}
.pvbadge{position:fixed;left:50%;top:12px;transform:translateX(-50%);z-index:350;background:linear-gradient(135deg,var(--accent),#c084fc);color:var(--onaccent);font-weight:800;font-size:11.5px;padding:5px 14px;border-radius:99px;box-shadow:0 10px 30px -8px var(--accent);pointer-events:none;white-space:nowrap}

/* ---------- entrances ---------- */
.fx-in{animation:fxin .9s var(--ease) both;animation-delay:calc(var(--i,0)*65ms)}
@keyframes fxin{from{opacity:0;transform:translateY(34px) scale(.96);filter:blur(8px)}}
.page.on.pg-in{animation:pgin .7s var(--ease) both}
@keyframes pgin{from{clip-path:inset(0 0 100% 0 round 28px)}to{clip-path:inset(0 0 0 0 round 28px)}}
.tile.fx-tilt{will-change:transform}
.mag{will-change:transform}

/* ---------- laptops / tablets ---------- */
main{--x:0}
@media(max-width:1180px){
 main{padding:28px 24px 80px}
 .app{grid-template-columns:minmax(0,1fr) 224px}
 #cockpit{grid-template-columns:1fr}
 .ck-gem{order:-1;min-height:300px}#gem{min-height:300px}
 .ck-left{padding:8px 24px 22px}
 #ovg .tile{grid-column:span 4}
 #ovg [data-mod="chart"],#ovg [data-mod="latest"],#ovg [data-mod="pending"]{grid-column:span 12;grid-row:auto}
 #ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 4}
}
/* ---------- phones: glass bar at the bottom ---------- */
@media(max-width:820px){
 .app{display:block}
 main{padding:18px 14px calc(104px + env(safe-area-inset-bottom));padding-left:max(14px,env(safe-area-inset-left));padding-right:max(14px,env(safe-area-inset-right))}
 aside{position:fixed;left:10px;right:10px;bottom:calc(10px + env(safe-area-inset-bottom));top:auto;height:auto;border:1px solid var(--ring);border-radius:26px;flex-direction:row;padding:6px;gap:0;background:linear-gradient(180deg,rgba(255,255,255,.1),rgba(255,255,255,.03)),rgba(10,12,20,.78);box-shadow:0 24px 60px -16px rgba(0,0,0,.85);z-index:60}
 :root[data-theme=light] aside{background:rgba(255,255,255,.88)}
 body.alarmon aside{top:auto;height:auto}
 .brand,.me{display:none}
 nav{flex-direction:row;width:100%;gap:2px;overflow-x:auto;overflow-y:hidden}
 nav a{flex:1 0 60px;flex-direction:column;gap:3px;padding:8px 2px;font-size:10.5px;border-radius:18px;justify-content:center;text-align:center;white-space:nowrap}
 nav a:hover{transform:none}
 nav a .badge,nav a .newdot{position:absolute;top:3px;right:9px;margin:0}
 #nav a.pinned:after{display:none}
 h1{font-size:clamp(30px,9vw,40px)}
 header{margin-bottom:20px}
 .tile,.panel{border-radius:24px}
 .panel{padding:18px}.tile{padding:16px 17px;min-height:136px}.tile .v{font-size:25px}
 #ovg .tile{grid-column:span 6}
 #ovg [data-mod="reviews"],#ovg [data-mod="keys"],#ovg [data-mod="stockp"]{grid-column:span 12}
 #cockpit{border-radius:26px}
 .ck-big{font-size:clamp(44px,15vw,72px)}
 .ck-gem,#gem{min-height:250px}
 .drawer{border-radius:28px 28px 0 0;border:1px solid var(--ring);border-bottom:0;width:100vw;top:auto;height:88vh;transform:translateY(105%)}
 .drawer.on{transform:none}
 .toasts{bottom:calc(98px + env(safe-area-inset-bottom))}
 #cmdk{padding-top:8vh}
 .pvbadge{top:auto;bottom:calc(92px + env(safe-area-inset-bottom))}
 #cmdkbtn kbd{display:none}
 table.stack tr{background:rgba(255,255,255,.04);border-radius:18px;padding:14px;margin-bottom:8px;border-bottom:0}
}
@media(max-width:460px){.tile .v{font-size:21px}#ovg{gap:10px}}

/* ---------- motion off ---------- */
@media (prefers-reduced-motion:reduce){
 #fxbg i,#fxbg .floor,#fxbg .grain,#fxbg .sun,.logowrap:after,.dot:after,.badge,.pill.warn:before,.fx-in,.bar,.qbar i,.val,.tx,#fxbar,.ck-track,.ck-hint:before,.tile .spark path.s,body.ovedit #ovg [data-mod]{animation:none!important}
 .tile .spark path.s{stroke-dashoffset:0!important}.tile .ringw .p{animation:none!important;stroke-dashoffset:var(--co)!important}
 *{transition-duration:.01ms!important}
}
body.fxoff #fxbg i,body.fxoff #fxbg .floor,body.fxoff #fxbg .grain,body.fxoff #fxbg .sun{animation:none}
body.fxoff #fxbg .grain,body.fxoff #fxcursor{display:none}

</style></head><body><div id="alarm" role="alert" hidden></div>
<div class="app">
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
 <div style="display:flex;justify-content:flex-end;margin:-4px 0 10px"><button class="btn" id="ovedit">Edit overview</button></div>
 <div id="ovbar" class="panel" hidden></div>
 <div id="ovg">
 <div class="tiles dyn" id="tiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="grid">
  <div class="panel" data-mod="chart"><h2><b id="mt1">Sales per month</b> <span id="cur1"></span></h2><div class="chart dyn" id="chart1"><div class="sk box"></div></div></div>
  <div class="panel" data-mod="latest"><h2>Latest orders <a href="#orders">View all</a></h2><div class="dyn" id="latest"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div></div>
 </div>
 <div class="grid2">
  <div class="panel" data-mod="pending"><h2>Waiting to be completed <a href="#orders">Open</a></h2><div class="dyn" id="pend"><div class="sk line"></div><div class="sk line"></div></div></div>
  <div class="grid3 dyn" id="mini" style="grid-template-columns:repeat(auto-fit,minmax(150px,1fr))"><div class="sk tile"></div><div class="sk tile"></div></div>
 </div>
 <div class="panel" data-help="status" data-mod="status"><h2>Eldorado connection <span id="statsum"></span></h2><div class="dyn" id="statbox"><div class="sk line"></div><div class="sk line"></div></div></div>
 </div>
</section>

<section class="page" id="p-sales">
 <div class="tiles dyn" id="stiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="grid">
  <div class="panel"><h2><b id="mt2">Sales per month</b> <span id="cur2"></span></h2><div class="chart dyn" id="chart2"><div class="sk box"></div></div></div>
  <div class="panel" data-help="records"><h2>Records</h2><div class="rows dyn" id="recs"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div></div>
 </div>
 <div class="grid">
  <div class="panel" data-help="calendar"><div class="calhead"><button class="btn icon" id="calprev" aria-label="Previous month"><svg class="i" viewBox="0 0 24 24"><path d="M15 5l-7 7 7 7"/></svg></button><div style="text-align:center"><b id="calttl"></b><div class="muted" id="calsum" style="font-size:12.5px"></div></div><button class="btn icon" id="calnext" aria-label="Next month"><svg class="i" viewBox="0 0 24 24"><path d="M9 5l7 7-7 7"/></svg></button></div>
   <div class="cal dyn" id="cal"></div></div>
  <div class="panel"><h2>Day <span id="daydate"></span></h2><div class="dyn" id="dayd"><div class="empty">Pick a day in the calendar.</div></div></div>
 </div>
 <div class="grid">
  <div class="panel" data-help="fees"><h2>Eldorado fees</h2><div class="rows dyn" id="fees"></div></div>
  <div class="panel" data-help="months"><h2>Monthly breakdown</h2><div class="scroll dyn" id="months"></div></div>
 </div>
</section>

<section class="page" id="p-history">
 <div class="tiles dyn" id="htiles"><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div><div class="sk tile"></div></div>
 <div class="bar2"><div class="seg" id="hseg"><button type="button" data-h="all" class="on">All</button><button type="button" data-h="add">Added</button><button type="button" data-h="remove">Removed</button></div><span class="muted" id="hnote"></span></div>
 <div class="panel"><div class="dyn" id="hlist"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div>
  <div class="row" style="margin-top:12px"><button class="btn" id="hmore" type="button" hidden>Show more</button></div>
  <div class="muted" style="font-size:12.5px;margin-top:10px">Orders from before the history started are shown as added. Cancelled orders only show from when the history started.</div></div>
</section>

<section class="page" id="p-programs"><div class="panel"><h2>Programs <span id="progsum"></span></h2>
 <div class="dyn" id="proglist"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div>
 <div class="muted" style="font-size:12.5px;margin-top:10px">The dashboard starts these programs and starts them again if they stop. Restart one if it seems stuck.</div></div></section>

<section class="page" id="p-server"><div class="panel"><h2>Server <span id="srvsum"></span></h2>
 <div class="srv dyn" id="srvbox"><div class="sk line"></div><div class="sk line"></div><div class="sk line"></div></div>
 <div class="row" style="margin-top:16px"><button class="btn" id="srvrestart" type="button">Restart the dashboard</button></div>
 <div class="muted" id="srvmsg" style="font-size:12.5px;margin-top:8px">Restarting stops the programs and starts everything again. It takes about half a minute. The page reloads itself.</div></div></section>

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
 <button class="btn icon" id="wattach" type="button" title="Attach a picture or PDF" aria-label="Attach a picture or PDF"><svg class="i" viewBox="0 0 24 24"><path d="M21 12l-8.5 8.5a5 5 0 01-7-7L14 5a3.5 3.5 0 015 5l-8.5 8.5a2 2 0 01-3-3L15 8"/></svg></button><input type="file" id="wfile" accept="image/png,image/jpeg,image/gif,image/webp,application/pdf" hidden>
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
   <div class="field"><label>Payout delay</label><div class="row" style="margin:0;align-items:center"><input type="number" id="payout" min="0" max="90" step="1" inputmode="numeric" style="width:100px"> <span>days</span></div><div class="muted" style="font-size:12.5px;margin-top:4px">How many days after the buyer has confirmed receipt you expect the money. Used for the expected payout date. 0 hides it.</div></div>
   <div class="field"><label>Fees</label><div class="seg" id="gnSeg2"><button type="button" data-g="0">Net (after fees)</button><button type="button" data-g="1">Gross (before fees)</button></div></div>
   <div class="tgl"><div>Hide all numbers<small>Blurs every amount. Good when someone looks over your shoulder. Only on this device.</small></div><input type="checkbox" id="setHide"></div>
  </div>
  <div class="panel" style="margin-bottom:14px"><h2>Look</h2>
   <div class="field"><label>Accent colour</label><div class="sw" id="sw"></div></div>
   <div class="field"><label>Background</label><div class="chips" id="bgSeg"></div></div>
   <div class="field"><label>Light or dark</label><div class="seg" id="thSeg"><button type="button" data-t="dark">Dark</button><button type="button" data-t="light">Light</button></div></div>
   <div class="tgl"><div>Animated background and effects<small>Moving light, sparkles, 3D cards and count-up numbers. Turn off on a slow device. Only on this device.</small></div><input type="checkbox" id="setFx"></div>
  </div>
  <div class="panel" style="margin-top:14px"><h2>Menu</h2><div class="muted" style="font-size:12.5px;margin-bottom:8px">Drag a page, or use the arrows, to change the order. The star pins it to the top.</div><div id="menuedit" class="dyn"></div>
   <div class="row" style="margin-top:10px"><button class="btn" id="menureset" type="button">Reset menu</button><a class="btn" href="#news">All news and changes</a></div></div>
  <div class="panel" style="margin-top:14px"><h2>Overview</h2><div class="muted" style="font-size:12.5px;margin-bottom:6px">Choose what is shown on the overview.</div><div id="tilesel"></div></div>
 </div>
 <div>
  <div class="panel" style="margin-bottom:14px" id="notifybox"><h2>Notifications <span>admins</span></h2>
   <div class="field"><label>Sound</label><div class="row" style="margin:0"><select id="sndsel"><option value="ding">Ding</option><option value="bell">Bell</option><option value="pop">Pop</option><option value="chime">Chime</option><option value="none">No sound</option></select><button class="btn" id="sndtest" type="button">Play</button></div></div>
   <div class="tgl"><div>War-Room messages</div><input type="checkbox" data-n="warroom"></div>
   <div class="tgl"><div>New orders</div><input type="checkbox" data-n="orders"></div>
   <div class="tgl"><div>Bad reviews</div><input type="checkbox" data-n="reviews"></div>
   <div class="tgl"><div>Keys running low<small>10 or fewer keys left, and when they run out.</small></div><input type="checkbox" data-n="keys"></div>
   <div class="row" style="margin-top:12px"><button class="btn" id="setnote" type="button">Notifications: off</button> <button class="btn" id="pushtest" type="button">Send test notification</button></div>
   <div class="muted" style="font-size:12.5px">The switch above turns notifications on for this device. The boxes decide which ones you get.</div>
  </div>
  <div class="panel" style="margin-bottom:14px" id="backupbox"><h2>Backup <span>admins</span></h2>
   <div class="muted" style="font-size:12.5px">A copy of all your data (orders, history, users, notes, keys) is taken automatically every day. The last 14 are kept in the folder "backups" next to dashboard.py. Your .env and secret keys are not included.</div>
   <div class="row" style="margin-top:12px"><button class="btn" id="bknow" type="button">Back up now</button></div>
   <div class="rows dyn" id="bklist"></div>
   <div class="muted" id="bkmsg" style="font-size:12.5px;margin-top:8px"></div>
  </div>
  <div class="panel" style="margin-bottom:14px" id="pwbox"><h2>Password</h2>
   <div class="field"><label>Old password</label><input type="password" id="pwold" autocomplete="current-password"></div>
   <div class="field"><label>New password <small class="muted">(at least 8 characters)</small></label><input type="password" id="pwnew" autocomplete="new-password"></div>
   <div class="field"><label>New password again</label><input type="password" id="pwnew2" autocomplete="new-password"></div>
   <div class="row" style="margin-top:6px"><button class="btn" id="pwsave" type="button">Change password</button></div>
   <div class="muted" id="pwmsg" style="font-size:12.5px;margin-top:6px">Your other devices are logged out when you change it.</div></div>
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

<section class="page" id="p-news"><div class="panel"><h2>What's new in the dashboard</h2><div id="newsbox"></div></div>
 <div class="panel" style="margin-top:14px"><h2>Changes from GitHub <span id="chhead"></span></h2><div class="dyn" id="chlog"></div></div></section>
</main>
<div class="helpb" id="help" hidden role="tooltip"></div>

<aside>
 <div class="brand"><img class="logo" id="logo" src="/logo-mark.png?v=2" alt=""><span>__SHOP__</span></div>
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
  <a href="#server" data-p="server" id="navserver" hidden><svg class="i" viewBox="0 0 24 24"><rect x="3" y="4" width="18" height="6" rx="1.5"/><rect x="3" y="14" width="18" height="6" rx="1.5"/><path d="M7 7h.01M7 17h.01"/></svg>Server</a>
  <a href="#programs" data-p="programs" id="navprog" hidden><svg class="i" viewBox="0 0 24 24"><rect x="3" y="4" width="18" height="16" rx="2"/><path d="M7 10l3 2-3 2M13 14h4"/></svg>Programs</a>
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
"Switch light or dark": "Skift lys eller mørk",
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
"off": "slået fra",
"on": "slået til",
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
"Search or jump to...": "Søg eller hop til...",
"move": "flyt",
"open": "åbn",
"Go to": "Gå til",
"Actions": "Handlinger",
"Hide or show numbers": "Skjul eller vis tal",
"Refresh data": "Opdatér data",
"Animated background": "Animeret baggrund",
"Celebrate": "Fejr",
"Find this key in the orders": "Find denne key i ordrerne",
"Nothing found.": "Intet fundet.",
"Drag the diamond": "Træk i diamanten",
"now": "nu",
"New design - preview": "Ny udgave - test (den rigtige side er urørt)",
"Animated background and effects": "Animeret baggrund og effekter",
"Moving light, sparkles, 3D cards and count-up numbers. Turn off on a slow device. Only on this device.": "Bevægeligt lys, gnister, 3D-kort og tal der tæller op. Slå fra på en langsom enhed. Kun på denne enhed.",
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
"Gross per month": "Brutto pr. måned",
"Net per month": "Netto pr. måned",
"Big update": "Stor opdatering",
"Programs": "Programmer",
"Payout delay": "Udbetalingsforsinkelse",
"How many days after an order you expect the money. Used for the expected payout date. 0 hides it.": "Hvor mange dage efter køber har bekræftet modtagelse, du forventer pengene. Bruges til den forventede udbetalingsdato. 0 skjuler den.",
"Menu": "Menu",
"Drag a page, or use the arrows, to change the order. The star pins it to the top.": "Træk en side, eller brug pilene, for at ændre rækkefølgen. Stjernen fastgør den øverst.",
"Reset menu": "Nulstil menu",
"All news and changes": "Alle nyheder og ændringer",
"Changes from GitHub": "Ændringer fra GitHub",
"The dashboard starts these programs and starts them again if they stop. Restart one if it seems stuck.": "Dashboardet starter disse programmer og starter dem igen, hvis de stopper. Genstart et, hvis det virker hængt.",
"Growth": "Vækst",
"Growth this month": "Vækst denne måned",
"compared with the same days last month": "sammenlignet med de samme dage sidste måned",
"against": "mod",
"same days last month": "samme dage sidste måned",
"Not enough history yet.": "Ikke nok historik endnu.",
"Edit overview": "Redigér overblik",
"drag a module, or tap it and use the arrows": "træk et modul, eller tryk på det og brug pilene",
"Move earlier": "Flyt tidligere",
"Move later": "Flyt senere",
"Remove": "Fjern",
"Reset": "Nulstil",
"Hidden modules": "Skjulte moduler",
"Stock panel": "Lagerpanel",
"Other currencies": "Andre valutaer",
"Send test notification": "Send testbesked",
"Test notification": "Testbesked",
"Sent. It should arrive in a few seconds, also if the app is closed.": "Sendt. Den bør komme om få sekunder, også når appen er lukket.",
"On iPhone, open the app from the home screen icon first.": "På iPhone: åbn først appen fra ikonet på hjemmeskærmen.",
"This browser cannot receive notifications when closed.": "Denne browser kan ikke modtage beskeder, når den er lukket.",
"The server cannot send notifications yet": "Serveren kan ikke sende beskeder endnu",
"The server did not accept this device": "Serveren accepterede ikke denne enhed",
"Could not register this device": "Kunne ikke registrere denne enhed",
"pywebpush is not installed on the VPS. Run opdater.bat and restart.": "pywebpush er ikke installeret på VPS'en. Kør opdater.bat og start igen.",
"No device is registered for you. Turn notifications on from the installed app.": "Ingen enhed er registreret til dig. Slå beskeder til fra den installerede app.",
"Stock value": "Lagerværdi",
"worth": "værd",
"profit each": "profit pr. stk.",
"Cost per unit": "Indkøbspris pr. enhed",
"profit": "profit",
"PROGRAM IS DOWN": "PROGRAM ER NEDE",
"PROGRAMS ARE DOWN": "PROGRAMMER ER NEDE",
"The dashboard tries to start them again by itself. Tap to see why.": "Dashboardet prøver selv at starte dem igen. Tryk for at se hvorfor.",
"Backup": "Backup",
"Back up now": "Tag backup nu",
"Backup taken.": "Backup taget.",
"manual": "manuel",
"before a restore": "før en gendannelse",
"Download": "Hent",
"Restore": "Gendan",
"Restored": "Gendannede",
"Could not restore.": "Kunne ikke gendanne.",
"No backups yet. The first one is taken within a few minutes.": "Ingen backups endnu. Den første tages inden for få minutter.",
"Restart the dashboard now so everything is read again.": "Genstart dashboardet nu, så alt bliver læst igen.",
"(Your data from before is saved as a safety backup.)": "(Dine data fra før er gemt som en sikkerhedskopi.)",
"A copy of all your data (orders, history, users, notes, keys) is taken automatically every day. The last 14 are kept in the folder \"backups\" next to dashboard.py. Your .env and secret keys are not included.": "En kopi af alle dine data (ordrer, historik, brugere, noter, keys) tages automatisk hver dag. De seneste 14 gemmes i mappen \"backups\" ved siden af dashboard.py. Din .env og hemmelige nøgler er ikke med.",
"Saved": "Gemt",
"Month forecast": "Månedsforecast",
"Too early in the month.": "For tidligt på måneden.",
"Server": "Server",
"Running for": "Kører i",
"since": "siden",
"Disk space": "Diskplads",
"free of": "ledig af",
"running low": "ved at løbe tør",
"Memory": "Hukommelse",
"Latest backup": "Seneste backup",
"none yet": "ingen endnu",
"Your data": "Dine data",
"War-Room file": "War-Room-fil",
"not managed here": "styres ikke her",
"Version": "Version",
"not a git clone": "ikke en git-klon",
"Computer": "Computer",
"running": "kører",
"demo": "demo",
"d": "d",
"h": "t",
"Restart the dashboard": "Genstart dashboardet",
"Restarting stops the programs and starts everything again. It takes about half a minute. The page reloads itself.": "Genstart stopper programmerne og starter alt igen. Det tager omkring et halvt minut. Siden genindlæser sig selv.",
"Restart is only possible when the dashboard is started with  py start_all.py  (or the autostart).": "Genstart kan kun bruges, når dashboardet er startet med  py start_all.py  (eller autostart).",
"Restarting... this page reloads when the dashboard is back.": "Genstarter... siden genindlæser, når dashboardet er tilbage.",
"Demo: nothing restarted.": "Demo: intet genstartet.",
"It is taking longer than normal. Check the window on the server.": "Det tager længere end normalt. Kig på vinduet på serveren.",
"The dashboard was not started with start_all.py, so nothing would start it again. Start it with  py start_all.py  (or the autostart).": "Dashboardet er ikke startet med start_all.py, så intet ville starte det igen. Start det med  py start_all.py  (eller autostart).",
"Password": "Adgangskode",
"Old password": "Gammel adgangskode",
"(at least 8 characters)": "(mindst 8 tegn)",
"New password again": "Ny adgangskode igen",
"Change password": "Skift adgangskode",
"Your other devices are logged out when you change it.": "Dine andre enheder bliver logget ud, når du skifter den.",
"The new password must be at least 8 characters.": "Den nye adgangskode skal være mindst 8 tegn.",
"The two new passwords are not the same.": "De to nye adgangskoder er ikke ens.",
"Password changed. Your other devices are logged out.": "Adgangskoden er skiftet. Dine andre enheder er logget ud.",
"Password changed.": "Adgangskoden er skiftet.",
"The old password is not right.": "Den gamle adgangskode er forkert.",
"Pick a password that is different from the old one.": "Vælg en adgangskode, der er forskellig fra den gamle.",
"That password is too long.": "Den adgangskode er for lang.",
"Too many attempts. Try again in a few minutes.": "For mange forsøg. Prøv igen om nogle minutter.",
"Attach a picture or PDF": "Vedhæft et billede eller PDF",
"Uploading...": "Uploader...",
"The file is too big (max 5 MB).": "Filen er for stor (maks. 5 MB).",
"Only pictures (png, jpg, gif, webp) and PDF files.": "Kun billeder (png, jpg, gif, webp) og PDF-filer.",
"No file.": "Ingen fil.",
"Sales left": "Salg tilbage",
"payout due": "udbetaling forfalden",
"payout around": "udbetaling ca.",
"Expected payout": "Forventet udbetaling",
"your own estimate": "dit eget estimat",
"counted from when the buyer confirms receipt": "regnes fra køber bekræfter modtagelse",
"No new news right now.": "Ingen nye nyheder lige nu.",
"Earlier news": "Tidligere nyheder",
"The change log shows when this folder is a Git clone (updated with opdater.bat).": "Ændringsloggen vises, når mappen er en Git-klon (opdateret med opdater.bat).",
"The dashboard is not starting the programs. Run it with  py dashboard.py  (without --no-programs).": "Dashboardet starter ikke programmerne. Kør det med  py dashboard.py  (uden --no-programs).",
"stopped": "stoppet",
"All running": "Alle kører",
"Restarting": "Genstarter",
"File not found": "Filen findes ikke",
"Stopped, starting again": "Stoppet, starter igen",
"Stopped": "Stoppet",
"last output": "sidste output",
"restarted": "genstartet",
"Hide log": "Skjul log",
"Show log": "Vis log",
"Restart": "Genstart",
"Move up": "Flyt op",
"Move down": "Flyt ned",
"Pin": "Fastgør",
"More tools": "Flere værktøjer"
};

const $=id=>document.getElementById(id);
const qs=(s,r)=>(r||document).querySelector(s),qsa=(s,r)=>[...(r||document).querySelectorAll(s)];
const esc=s=>String(s==null?"":s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const lsGet=(k,def)=>{try{const v=localStorage.getItem(k);return v===null?def:v;}catch(e){return def;}};
const lsSet=(k,v)=>{try{localStorage.setItem(k,v);}catch(e){}};
const SHOP=qs(".brand span").textContent;
const VERSION="2026-10-27b";

// ---------- language ----------
let LANG=lsGet("lang","")||((navigator.language||"").toLowerCase().startsWith("da")?"da":"en");
const t=s=>(LANG==="da"&&Object.prototype.hasOwnProperty.call(DA,s))?DA[s]:s;
const LOC=()=>LANG==="da"?"da-DK":"en-GB";
const DAPL={order:["ordre","ordrer"],key:["key","keys"],offer:["tilbud","tilbud"],unit:["enhed","enheder"],file:["fil","filer"],review:["anmeldelse","anmeldelser"],device:["enhed","enheder"],day:["dag","dage"],event:["hændelse","hændelser"],program:["program","programmer"],time:["gang","gange"]};
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
let PREFS={lang:"",accent:"",currency:"",sound:"ding",gross:null,tax:37,emoji:"",color:"",bg:"",hide:[],menu:[],pins:[],payout:5,ovorder:[],notify:{warroom:true,orders:true,reviews:true,keys:true}};
const hid=k=>(PREFS.hide||[]).includes(k);
const BGS=[["","None"],["dots","Dots"],["grid","Grid"],["waves","Waves"],["aurora","Aurora"],["diagonal","Diagonal"]];
function applyBg(){document.body.dataset.bg=PREFS.bg||"";lsSet("bg",PREFS.bg||"");}
let GROSS=lsGet("gross","0")==="1",HIDE=lsGet("hide","0")==="1",CURSEL=lsGet("cur","");
let MAIN="USD",RATES={},RATES_LIVE=false,RATES_DATE=null,isAdmin=false,prefsApplied=false,saveTimer=null;
const CID=(()=>{try{let c=localStorage.getItem("cid");if(!c||!/^[A-Za-z0-9_-]{6,40}$/.test(c)){c=Array.from(crypto.getRandomValues(new Uint8Array(12)),b=>b.toString(36).padStart(2,"0")).join("").slice(0,20);localStorage.setItem("cid",c);}return c;}catch(e){return "";}})();
if(CID){const _f=window.fetch.bind(window);window.fetch=(u,o)=>{o=o||{};if(typeof u==="string"&&u[0]==="/"){const h=new Headers(o.headers||{});h.set("X-Client",CID);o={...o,headers:h};}return _f(u,o);};}
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
 PREFS.menu=p.menu||[];PREFS.pins=p.pins||[];PREFS.payout=p.payout==null?5:p.payout;PREFS.ovorder=p.ovorder||[];PREFS.tax=p.tax==null?37:p.tax;PREFS.emoji=p.emoji||"";PREFS.color=p.color||"";PREFS.bg=p.bg||"";PREFS.hide=p.hide||[];
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
const PAGES=["overview","sales","history","orders","stock","reviews","keys","warroom","mindmap","profit","programs","server","users","settings","news"];
const ADMIN_PAGES=["warroom","mindmap","profit","programs","server","users"];
const TITLES={overview:"Overview",sales:"Sales",history:"History",programs:"Programs",server:"Server",orders:"Orders",stock:"Stock",reviews:"Reviews",keys:"Keys",warroom:"War-Room",mindmap:"Mindmap",profit:"Profit",users:"Users",settings:"Settings",news:"What's new"};
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
// growth: this month so far against the same days of last month (net or gross, like the rest of the page)
function growthInfo(s){
 const [y,m,dd]=s.date.split("-").map(Number),py=m===1?y-1:y,pm=m===1?12:m-1,key=(Y,M,D)=>Y+"-"+String(M).padStart(2,"0")+"-"+String(D).padStart(2,"0");
 let cur=0,prev=0;
 for(let i=1;i<=dd;i++){const a=s.days[key(y,m,i)],b=s.days[key(py,pm,i)];if(a)cur+=GROSS?a.g:a.a;if(b)prev+=GROSS?b.g:b.a;}
 return prev>0?{pct:(cur/prev-1)*100,cur,prev}:null;
}
const grCls=p=>p>=0?"up":"down",grTxt=p=>(p>=0?"▲ +":"▼ −")+fmt(Math.abs(p),0)+"%";
function growthBadge(s){const g=growthInfo(s);return g?`<span class="gr ${grCls(g.pct)}" title="${esc(t("compared with the same days last month"))}">${grTxt(g.pct)}</span>`:"";}
function forecastInfo(s){
 const [y,m,dd]=s.date.split("-").map(Number),dim=new Date(y,m,0).getDate(),key=i=>y+"-"+String(m).padStart(2,"0")+"-"+String(i).padStart(2,"0");
 if(dd<3)return null;
 let mtd=0,l7=0;
 for(let i=1;i<=dd;i++){const a=s.days[key(i)],v=a?(GROSS?a.g:a.a):0;mtd+=v;if(i>dd-7)l7+=v;}
 const p7=l7/Math.min(7,dd),pm=mtd/dd,rem=dim-dd;
 return {exp:mtd+(p7+pm)/2*rem,lo:mtd+Math.min(p7,pm)*rem,hi:mtd+Math.max(p7,pm)*rem,mtd,rem};
}
function stockValue(d){
 const cv=(a,c)=>RATES[c]&&RATES[MAIN]?a/RATES[c]*RATES[MAIN]:a,fee=(d.sales&&d.sales.fee_percent)||0,uc=d.unitcosts||{};
 let gross=0,profit=0,costed=0,units=0;
 d.stock.offers.forEach(o=>{const q=o.quantity||0,p=o.price.amount||0;units+=q;gross+=cv(q*p,o.price.currency);
  if(uc[o.title]!==undefined&&q){costed++;profit+=cv(q*(p*(1-fee/100)-uc[o.title]),o.price.currency);}});
 return {gross,profit,costed,units};
}
function alarmUi(al){
 const a=$("alarm");document.body.classList.toggle("alarmon",al.length>0);
 if(!al.length){a.hidden=true;return;}
 a.hidden=false;a.innerHTML="⚠ "+t(al.length>1?"PROGRAMS ARE DOWN":"PROGRAM IS DOWN")+": "+esc(al.map(x=>x.name).join(", "))+`<small>${t("The dashboard tries to start them again by itself. Tap to see why.")}</small>`;
 document.documentElement.style.setProperty("--alh",(a.offsetHeight+4)+"px");
}
function tiles(d){
 const s=d.sales,cur=esc(shownCur()),r=s.records;
 const tile0=(mod,l,key,v,sub,extra)=>`<div class="tile" data-mod="${mod}" data-help="${key}"><div class="l">${l} ${extra||""}</div><div class="v">${cuHtml(key,mv(v))} <small>${cur}</small></div><div class="s">${sub}</div></div>`;
 const other=o=>s.fee_percent?` · ${GROSS?t("net"):t("gross")} ${fmt(mv(GROSS?o.amount:o.gross))}`:"";
 const avg=o=>o.orders?amtOf(o)/o.orders:0;
 const tile=(id,...a)=>hid(id)?"":tile0(id,...a);
 let h=tile("today",t("Today"),"t-today",amtOf(s.today),plural(s.today.orders,"order")+other(s.today),recBadge(r.day.record))
  +tile("month",t("This month"),"t-month",amtOf(s.month),plural(s.month.orders,"order")+other(s.month),recBadge(r.month.record)+growthBadge(s))
  +tile("all",t("All time"),"t-all",amtOf(s.all),plural(s.all.orders,"order")+other(s.all))
  +tile("avg",t("Average order"),"t-avg",avg(s.all),t("Today")+": "+(s.today.orders?fmt(mv(avg(s.today))):"-")+" "+cur)
  +(hid("stock")?"":`<div class="tile" data-mod="stock" data-help="t-stock"><div class="l">${t("In stock")}</div><div class="v">${cuHtml("t-stock",d.stock.units,0)} <small>${t("units")}</small></div><div class="s">${plural(d.stock.offers.length,"offer")}</div></div>`);
 if(!hid("stockval")){const sv=stockValue(d);if(sv.units){h+=tile0("stockval",t("Stock value"),"t-stockval",sv.gross,plural(d.stock.offers.length,"offer")+" · "+plural(sv.units,"unit")+(sv.costed?" · "+t("profit")+" "+fmt(mv(sv.profit))+" "+cur:""));}}
 if(!hid("forecast")){const f=forecastInfo(s);if(f)h+=tile0("forecast",t("Month forecast"),"t-forecast",f.exp,fmt(mv(f.lo),0)+" – "+fmt(mv(f.hi),0)+" "+cur+" · "+plural(f.rem,"day")+" "+t("left"));}
 if(d.profit)h+=tile("profit",t("Profit this month"),"t-profit",d.profit.month,t("All time")+": "+fmt(mv(d.profit.all))+" "+cur);
 if(!hid("lastorder")){const lo=d.orders[0],mins=lo?(Date.now()-new Date(lo.time))/6e4:0,cls=!lo?"":mins>360?"bad":mins>120?"warn":"";
  h+=`<div class="tile" data-mod="lastorder" data-help="lastorder"><div class="l">${t("Latest order")}</div><div class="v ${cls}">${lo?esc(waited(lo.time)):"-"}${lo?` <small>${t("ago")}</small>`:""}</div><div class="s">${lo?esc(lo.buyer)+" · "+esc(tm(lo.time)):t("No orders yet.")}</div></div>`;}
 if(!hid("revrate")){const rv=d.reviews,tot=rv.positive+rv.negative,n=s.all.orders,pc=n?Math.min(100,tot*100/n):null;
  h+=`<div class="tile" data-mod="revrate" data-help="revrate"><div class="l">${t("Reviews per order")}</div><div class="v">${pc===null?"-":fmt(pc,0)} <small>%</small></div><div class="s">${plural(tot,"review")} ${t("of")} ${plural(n,"order")}</div></div>`;}
 if(!hid("others"))s.others.forEach(o=>{h+=`<div class="tile" data-mod="others"><div class="l">${esc(o.currency)} (${t("all time")})</div><div class="v">${fmt(o.all.amount)} <small>${esc(o.currency)}</small></div><div class="s">${plural(o.all.orders,"order")}</div></div>`;});
 $("tiles").innerHTML=h;runCountUps($("tiles"));
}
function taxpot(d){
 const el=$("taxpot");if(!isAdmin||!d.profit||hid("taxpot")){el.hidden=true;return;}
 const pct=PREFS.tax==null?37:PREFS.tax,all=Math.max(0,d.profit.all_dkk)*pct/100,mo=Math.max(0,d.profit.month_dkk)*pct/100;
 el.hidden=false;el.dataset.help="taxpot";
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
 const st=document.querySelector('#ovg [data-mod="status"]');if(st)st.style.display=hid("status")?"none":"";
}
function niceStep(peak){for(const s of [5,10,20,25,50,100,200,250,500,1000,2000,2500,5000,10000,20000,50000]) if(peak/s<=4)return s;return 100000;}
const monthTitle=()=>GROSS?t("Gross per month"):t("Net per month");
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
 box.innerHTML=`<svg class="ch" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" role="img" aria-label="${esc(monthTitle())}">${g}</svg><div class="tip"></div>`;
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
function recvTime(o){const l=o.log||{};return l.Received||(o.state==="Received"?o.time:null);}
function payoutDate(o){const r=recvTime(o);return PREFS.payout>0&&r?new Date(new Date(r).getTime()+PREFS.payout*864e5):null;}
function payoutTxt(o){const d=payoutDate(o);if(!d)return "";
 return " · "+(d.getTime()<Date.now()?t("payout due"):t("payout around")+" "+d.toLocaleDateString(LOC(),{day:"numeric",month:"short"}));}
function pendHtml(d,limit){
 const p=d.pending;remember(p.rows);
 if(!p.n)return `<div class="empty">${t("Nothing is waiting. All orders are completed.")}</div>`;
 return p.rows.slice(0,limit||8).map(o=>`<div class="row2" data-oid="${esc(o.id)}" style="cursor:pointer"><div class="t">${esc(o.item)}<small>${esc(o.buyer)} · ${t("waiting")} ${esc(waited(o.time))}${payoutTxt(o)}</small></div><div class="e"><div class="mono">${money(ordAmt(o),o.price.currency)}</div><span class="pill ${stClass(o.state)}">${esc(stateName(o.state))}</span></div></div>`).join("")
  +(p.n>(limit||8)?`<div class="muted" style="padding-top:8px">+ ${p.n-(limit||8)} ${t("more")}</div>`:"");
}
function pending(d){
 $("pend").innerHTML=pendHtml(d,5);
}
function mini(d){
 const r=d.reviews,tot=r.positive+r.negative,pct=tot?Math.round(r.positive*100/tot):null,k=d.keys,low=k.left<=10;
 const lowStock=d.stock.offers.filter(o=>o.quantity<=5).length;
 $("mini").innerHTML=
  (hid("reviews")?"":`<div class="panel" data-mod="reviews" data-help="mini-rev"><h2>${t("Reviews")} <a href="#reviews">${t("Open")}</a></h2><div class="big">${pct===null?"-":pct+"%"}</div><div class="muted">${r.positive} ${t("good")} · ${r.negative} ${t("bad")}</div></div>`)
  +(hid("keys")?"":`<div class="panel" data-mod="keys" data-help="mini-keys"><h2>${t("Keys left")} <a href="#keys">${t("Open")}</a></h2><div class="big">${fmt(k.left,0)}</div><div style="margin-top:4px">${low?`<span class="pill ${k.left===0?"bad":"warn"}">${k.left===0?t("Out of keys"):t("Running low")}</span>`:`<span class="muted">${fmt(k.used,0)} ${t("used so far")}</span>`}</div><div class="muted" style="font-size:12.5px;margin-top:6px">${fcText(k)}</div></div>`)
  +(hid("stockp")?"":`<div class="panel" data-mod="stockp" data-help="mini-stock"><h2>${t("Stock")} <a href="#stock">${t("Open")}</a></h2><div class="big">${fmt(d.stock.units,0)}</div><div style="margin-top:4px">${lowStock?`<span class="pill warn">${plural(lowStock,"offer")} ${t("low")}</span>`:`<span class="muted">${t("All offers stocked")}</span>`}</div></div>`);
}

// ================= sales =================
let calMonth=null,selDay=null;
function salesTiles(d){
 const s=d.sales,r=s.records,cur=esc(shownCur());
 const avg=o=>o.orders?amtOf(o)/o.orders:0;
 const bd=r.day.key?s.days[r.day.key]:null;
 $("stiles").innerHTML=
  `<div class="tile" data-help="s-avg"><div class="l">${t("Average order")}</div><div class="v">${cuHtml("s-avg",mv(avg(s.all)))} <small>${cur}</small></div><div class="s">${t("This month")}: ${s.month.orders?fmt(mv(avg(s.month))):"-"} ${cur}</div></div>`
  +`<div class="tile" data-help="s-best"><div class="l">${t("Best day ever")} ${recBadge(r.day.record)}</div><div class="v">${cuHtml("s-best",mv(bd?dayAmt(bd):0))} <small>${cur}</small></div><div class="s">${r.day.key?esc(dayLabel2(r.day.key)):"-"}${r.day.orders?" · "+plural(r.day.orders,"order"):""}</div></div>`
  +(()=>{const f=forecastInfo(s);return `<div class="tile" data-help="s-forecast"><div class="l">${t("Month forecast")}</div><div class="v">${f?fmt(mv(f.exp),0):"-"} <small>${cur}</small></div><div class="s">${f?fmt(mv(f.lo),0)+" – "+fmt(mv(f.hi),0)+" "+cur+" · "+plural(f.rem,"day")+" "+t("left"):t("Too early in the month.")}</div></div>`;})()
  +(()=>{const g=growthInfo(s);return `<div class="tile" data-help="s-growth"><div class="l">${t("Growth this month")}</div><div class="v ${g?(g.pct>=0?"":"bad"):""}">${g?(g.pct>=0?"+":"−")+fmt(Math.abs(g.pct),0):"-"} <small>%</small></div><div class="s">${g?fmt(mv(g.cur))+" "+t("against")+" "+fmt(mv(g.prev))+" "+cur+" · "+t("same days last month"):t("Not enough history yet.")}</div></div>`;})()
  +`<div class="tile" data-help="s-ords"><div class="l">${t("Orders this month")}</div><div class="v">${cuHtml("s-ords",s.month.orders,0)}</div><div class="s">${t("All time")}: ${fmt(s.all.orders,0)}</div></div>`;
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
  h+=`<button class="${cls}" data-day="${k}" style="--lv:${max?(a/max).toFixed(2):0}" aria-label="${esc(dayLabel2(k))}"><i>${i}</i><b>${x?fmt(mv(a),0)+"<em>"+esc(shownCur())+"</em>":""}</b><s>${x?x.n:""}</s></button>`;}
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
 $("months").innerHTML=`<table><thead><tr><th>${t("Month")}</th><th class="r">${t("Sales")}</th><th class="r">${t("Fees")}</th><th class="r">${t("Orders")}</th><th class="r">${t("Growth")}</th></tr></thead><tbody>${
  rows.map((x,i)=>{const pv=rows[i+1],v=GROSS?x.gross:x.amount,pvv=pv?(GROSS?pv.gross:pv.amount):0,gp=pvv>0?(v/pvv-1)*100:null;
  return `<tr><td>${esc(monthLabel(x.key))}</td><td class="r mono">${money(GROSS?x.gross:x.amount,c)}</td><td class="r mono muted">${money(x.gross-x.amount,c)}</td><td class="r muted">${x.orders}</td><td class="r">${gp===null?'<span class="muted">-</span>':`<span class="gr ${grCls(gp)}">${grTxt(gp)}</span>`}</td></tr>`;}).join("")}</tbody></table>`;
}

// ================= stock / reviews / keys =================
function stock(d){
 const sv=stockValue(d);$("stocksum").textContent=fmt(d.stock.units,0)+" "+t("units")+" · "+t("worth")+" "+fmt(mv(sv.gross),0)+" "+shownCur();
 const fee=(d.sales&&d.sales.fee_percent)||0,uc=d.unitcosts||{};
 $("stock").innerHTML=d.stock.offers.length?d.stock.offers.map(o=>{const w=Math.min(100,o.quantity),c=uc[o.title];
  const each=c===undefined?"":` · ${t("profit each")}: ${money(o.price.amount*(1-fee/100)-c,o.price.currency)}`;
  const cost=isAdmin?`<div class="ucost"><label>${t("Cost per unit")} (${esc(o.price.currency)})</label><input type="number" step="0.01" min="0" inputmode="decimal" data-ucost="${esc(o.title)}" value="${c===undefined?"":c}" placeholder="–">${each}</div>`:"";
  return `<div class="row2"><div class="t">${esc(o.title)}<small>${esc(o.category)}</small><div class="qbar ${o.quantity<=5?"warn":""}"><i style="width:${w}%"></i></div>${cost}</div>
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
   if(n.orders){ding();toast(t("New order"),money(ordAmt(o),o.price.currency)+" · "+o.buyer,()=>openOrder(o.id));if(window.FX)FX.celebrate(t("New order"),money(ordAmt(o),o.price.currency));}});}
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
 ["navusers","navwar","navmind","navprofit","navprog","navserver"].forEach(id=>{$(id).hidden=!isAdmin;});
 if(ADMIN_PAGES.includes(page())&&!isAdmin){location.hash="#overview";return;}
 MAIN=d.rates.base;RATES=d.rates.rates;RATES_LIVE=d.rates.live;RATES_DATE=d.rates.date;
 if(!prefsApplied){prefsApplied=true;applyServerPrefs(d.prefs);translateStatic();setTitle();settingsUi();}
 const q=$("quote");q.hidden=!d.quote;q.textContent=d.quote||"";
 $("who").textContent=d.user.name;$("role").textContent=t(d.user.role==="admin"?"admin":"viewer");$("av").textContent=d.user.name.slice(0,1);
 curUi();detectEvents(d);once("alarm",[d.alarms,LANG],()=>alarmUi(d.alarms||[]));newsNav();once("menu",[PREFS.menu,PREFS.pins,isAdmin],applyMenu);once("ovs",[PREFS.ovorder],ovStyle);once("tax",[d.profit,PREFS.tax,PREFS.hide,K0()],()=>taxpot(d));
 const p=page(),K=[GROSS,shownCur(),HIDE,LANG];
 if(p==="overview"){applyHides();once("status",[d.status,K],()=>statusPanel(d));once("welcome",[d.sales,d.reviews,d.pending.n,d.keys.left,K],()=>welcome(d));
  once("tiles",[d.sales,d.stock.units,d.stock.offers.length,d.profit,d.orders[0],d.reviews,PREFS.hide,K],()=>tiles(d));$("cur1").textContent=shownCur()+" · "+feeNote();$("mt1").textContent=monthTitle();
  once("c1",[d.sales.months,$("chart1").clientWidth,K],()=>chart(d,"chart1",6));once("latest",[d.orders,K],()=>latest(d));
  once("pend",[d.pending,K],()=>pending(d));once("mini",[d.reviews,d.keys,d.stock,PREFS.hide,K],()=>mini(d));}
 if(p==="sales"){$("cur2").textContent=shownCur()+" · "+feeNote();$("mt2").textContent=monthTitle();
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
  ${PREFS.payout>0?`<div class="r1"><div>${t("Expected payout")}<small>${payoutDate(o)?t("your own estimate"):t("counted from when the buyer confirms receipt")}</small></div><div class="v" style="font-weight:500">${payoutDate(o)?esc(payoutDate(o).toLocaleDateString(LOC(),{weekday:"short",day:"numeric",month:"short"})):"–"}</div></div>`:""}
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
 $("ptiles").innerHTML=`<div class="tile" data-help="p-month"><div class="l">${t("Profit this month")}</div><div class="v">${pill(m.profit)} <small>${cur}</small></div><div class="s">${t("Sales")} ${fmt(mv(m.sales))} − ${t("costs")} ${fmt(mv(m.costs+m.keys))}</div></div>
  <div class="tile" data-help="p-all"><div class="l">${t("Profit all time")}</div><div class="v">${pill(p.total.profit)} <small>${cur}</small></div><div class="s">${plural(p.total.orders,"order")}</div></div>
  <div class="tile" data-help="p-costs"><div class="l">${t("Costs all time")}</div><div class="v">${fmt(mv(p.total.costs+p.total.keys))} <small>${cur}</small></div><div class="s">${t("incl. keys")} ${fmt(mv(p.total.keys))}</div></div>`;
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
 const tile=(l,v,sub,cls,hk)=>`<div class="tile" data-help="${hk}"><div class="l">${l}</div><div class="v ${cls||""}">${v}</div><div class="s">${sub}</div></div>`;
 const sg=(v,s)=>(Math.abs(v)<0.005?"":s>0?"+":"−")+fmt(mv(Math.abs(v)));
 $("htiles").innerHTML=
  tile(t("Added today"),sg(j.added_today,1)+" <small>"+esc(shownCur())+"</small>",plural(j.n_added_today,"order"),"","h-added")
  +tile(t("Removed today"),sg(j.removed_today,-1)+" <small>"+esc(shownCur())+"</small>",plural(j.n_removed_today,"order"),j.removed_today?"bad":"","h-removed")
  +tile(t("Net this month"),sg(j.added_month-j.removed_month,j.added_month-j.removed_month>=0?1:-1)+" <small>"+esc(shownCur())+"</small>",t("Added")+" "+fmt(mv(j.added_month))+" · "+t("Removed")+" "+fmt(mv(j.removed_month)),"","h-net")
  +tile(t("Balance now"),fmt(mv(j.balance))+" <small>"+esc(shownCur())+"</small>",feeNote(),"","h-bal");
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
 if(isAdmin&&Date.now()-bkAt>20000)loadBackups();$("backupbox").style.display=isAdmin?"":"none";
 curUi();tglUi();menuUi();if(document.activeElement!==$("payout"))$("payout").value=PREFS.payout==null?5:PREFS.payout;
 $("bgSeg").innerHTML=BGS.map(b=>`<button type="button" class="chip${(PREFS.bg||"")===b[0]?" on":""}" data-bg="${b[0]}">${esc(t(b[1]))}</button>`).join("");
 const defs=[["today","Today"],["month","This month"],["all","All time"],["avg","Average order"],["stock","In stock"],["stockval","Stock value"],["forecast","Month forecast"],["profit","Profit this month",1],["taxpot","Tax pot",1],["lastorder","Latest order"],["revrate","Reviews per order"],["chart","Sales per month"],["latest","Latest orders"],["pending","Waiting to be completed"],["reviews","Reviews"],["keys","Keys left"],["stockp","Stock panel"],["status","Eldorado connection"],["others","Other currencies"]];
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
const NEWS=[{v:"2026-10-27 · 2",d:"2026-10-27",title:["More tools","Flere værktøjer"],items:[
 ["Programs page: the dashboard now starts order alerts, reviews, stock, stats and offer itself, shows if each one runs, and lets you restart one or watch its log live","Programmer-side: dashboardet starter nu ordre-alarmer, anmeldelser, lager, statistik og offer selv, viser om hver kører, og lader dig genstarte en eller se dens log live"],
 ["Growth in percent against the same days of last month, on the overview, on Sales and per month","Vækst i procent mod de samme dage sidste måned, på overblikket, på Salg og pr. måned"],
 ["Expected payout date: 5 days after the buyer confirms receipt (change the number of days in Settings)","Forventet udbetalingsdato: 5 dage efter køber har bekræftet modtagelse (ret antal dage i Indstillinger)"],
 ["Tap any number or box for a short explanation","Tryk på et tal eller en boks for en kort forklaring"],
 ["Change the order of the menu and pin your favourite pages (Settings)","Skift rækkefølgen på menuen og fastgør dine favoritsider (Indstillinger)"],
 ["News archive, and the latest changes from GitHub on this page","Nyhedsarkiv og de seneste ændringer fra GitHub på denne side"],
 ["Now you only need to run py dashboard.py","Nu behøver du kun at køre py dashboard.py"]]},
{v:"2026-10-27",d:"2026-10-27",title:["History","Historik"],items:[
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
 const on=newsActive().length>0;
 qsa('[data-p="news"]').forEach(x=>{x.hidden=!on&&page()!=="news";});
 $("newdot").hidden=!on||lsGet("seen_ver","")===VERSION;
}
function newsRender(){
 const act=new Set(newsActive().map(n=>n.v)),li=n=>`<div class="relnote"><h3>${esc(n.title[LANG==="da"?1:0])} <span class="muted" style="font-weight:400;font-size:13px">${esc(n.v)}</span></h3><ul>${n.items.map(i=>`<li>${esc(i[LANG==="da"?1:0])}</li>`).join("")}</ul></div>`;
 const now=NEWS.filter(n=>act.has(n.v)),old=NEWS.filter(n=>!act.has(n.v));
 $("newsbox").innerHTML=(now.length?now.map(li).join(""):`<div class="muted">${t("No new news right now.")}</div>`)
  +(old.length?`<h2 style="margin:20px 0 8px;font-size:15px">${t("Earlier news")}</h2>`+old.map(li).join(""):"");
 lsSet("seen_ver",VERSION);$("newdot").hidden=true;loadChangelog();
}
async function loadChangelog(){
 try{const r=await fetch("/api/changelog");if(!r.ok)return;const j=await r.json();
  $("chhead").innerHTML=j.head?`<span class="pill">${esc(j.head)}</span>`:"";
  $("chlog").innerHTML=j.rows.length?j.rows.map(x=>`<div class="chrow"><time>${esc(new Date(x.date).toLocaleDateString(LOC(),{day:"numeric",month:"short",year:"numeric"}))}</time><div>${esc(x.text)}</div></div>`).join("")
   :`<div class="empty">${t("The change log shows when this folder is a Git clone (updated with opdater.bat).")}</div>`;
 }catch(e){}
}

// ================= programs (admin) =================
const PRG={open:{},last:{},busy:{}};
const dur=s=>{s=Math.max(0,Math.floor(s));if(s<60)return s+" s";const m=Math.floor(s/60);if(m<60)return m+" min";const h=Math.floor(m/60);if(h<48)return h+" h "+(m%60)+" min";return plural(Math.floor(h/24),"day");};
async function loadPrograms(){
 if(!isAdmin)return;
 try{const r=await fetch("/api/programs");if(!r.ok)return;const j=await r.json();
  if(!j.managed){$("proglist").innerHTML=`<div class="empty">${t("The dashboard is not starting the programs. Run it with  py dashboard.py  (without --no-programs).")}</div>`;$("progsum").innerHTML="";return;}
  const bad=j.programs.filter(p=>!p.running).length;
  $("progsum").innerHTML=bad?`<span class="pill bad">${plural(bad,"program")} ${t("stopped")}</span>`:`<span class="pill good">${t("All running")}</span>`;
  const keepLog={};qsa("#proglist .plog").forEach(e=>{keepLog[e.dataset.n]=e.scrollTop+e.clientHeight>=e.scrollHeight-30;});
  $("proglist").innerHTML=j.programs.map(p=>{
   const cls=p.running?(p.quiet!==null&&p.quiet>3600?"warn":"ok"):(p.state==="restarting"?"warn":"bad");
   const st=p.running?t("Running for")+" "+dur(p.uptime):({restarting:t("Restarting"),missing:t("File not found"),crashed:t("Stopped, starting again")}[p.state]||t("Stopped"));
   const open=!!PRG.open[p.name];
   return `<div class="prog" data-n="${esc(p.name)}"><div class="ph"><span class="pdot ${cls}"></span>
    <div class="pn"><b>${esc(p.name)}</b> <span class="muted">${esc(p.script)}</span><small>${esc(st)}${p.quiet!==null?" · "+t("last output")+" "+dur(p.quiet)+" "+t("ago"):""}${p.restarts?" · "+t("restarted")+" "+plural(p.restarts,"time"):""}</small></div>
    <button class="btn" data-plog="${esc(p.name)}">${open?t("Hide log"):t("Show log")}</button>
    <button class="btn" data-prestart="${esc(p.name)}">${PRG.busy[p.name]?t("Sure?"):t("Restart")}</button></div>
    ${open?`<pre class="plog" data-n="${esc(p.name)}"></pre>`:""}</div>`;}).join("");
  for(const n of Object.keys(PRG.open)){if(PRG.open[n]){PRG.last[n]=PRG.last[n]||0;drawLog(n,true);}}
 }catch(e){}
}
const LOGS={};
async function drawLog(n,fresh){
 const el=qs('.plog[data-n="'+n+'"]');if(!el)return;
 if(fresh){el.innerHTML=(LOGS[n]||[]).map(logLine).join("");el.scrollTop=el.scrollHeight;}
 try{const r=await fetch("/api/programs/"+encodeURIComponent(n)+"/log?after="+(PRG.last[n]||0));if(!r.ok)return;const j=await r.json();
  if(j.lines.length){const stick=el.scrollTop+el.clientHeight>=el.scrollHeight-30;
   LOGS[n]=(LOGS[n]||[]).concat(j.lines).slice(-400);PRG.last[n]=j.last;
   el.insertAdjacentHTML("beforeend",j.lines.map(logLine).join(""));
   while(el.childNodes.length>400)el.removeChild(el.firstChild);
   if(stick||fresh)el.scrollTop=el.scrollHeight;}
 }catch(e){}
}
const logLine=l=>`<div class="${/error|traceback|exception|failed|fejl|stopped \(code [1-9]/i.test(l.x)?"e":""}"><span class="tt">${esc(new Date(l.t).toLocaleTimeString(LOC()))}</span> ${esc(l.x)}</div>`;
document.addEventListener("click",async e=>{
 const lg=e.target.closest("[data-plog]");
 if(lg){const n=lg.dataset.plog;PRG.open[n]=!PRG.open[n];if(!PRG.open[n]){delete LOGS[n];PRG.last[n]=0;}loadPrograms();return;}
 const rs=e.target.closest("[data-prestart]");
 if(rs){const n=rs.dataset.prestart;
  if(!PRG.busy[n]){PRG.busy[n]=true;rs.textContent=t("Sure?");setTimeout(()=>{PRG.busy[n]=false;loadPrograms();},3000);return;}
  PRG.busy[n]=false;rs.disabled=true;await post("/api/programs/"+encodeURIComponent(n)+"/restart");PRG.last[n]=0;LOGS[n]=[];setTimeout(loadPrograms,1200);}
});

// ================= menu order and pins =================
const MENU_DEFAULT=()=>PAGES;
function menuOrder(){
 const base=[...(PREFS.menu||[]),...MENU_DEFAULT()].filter((x,i,a)=>PAGES.includes(x)&&a.indexOf(x)===i);
 const pins=new Set(PREFS.pins||[]);return [...base.filter(x=>pins.has(x)),...base.filter(x=>!pins.has(x))];
}
function applyMenu(){
 const nav=$("nav");if(!nav)return;const by={};qsa("a",nav).forEach(a=>{by[a.dataset.p]=a;});
 const pins=new Set(PREFS.pins||[]);
 menuOrder().forEach(p=>{if(by[p]){nav.appendChild(by[p]);by[p].classList.toggle("pinned",pins.has(p));}});
}
function menuSave(order,pins){PREFS.menu=order;PREFS.pins=pins;savePrefs();applyMenu();menuUi();}
function menuUi(){
 const box=$("menuedit");if(!box)return;
 const vis=p=>!ADMIN_PAGES.includes(p)||isAdmin,list=menuOrder().filter(vis),pins=new Set(PREFS.pins||[]);
 box.innerHTML=list.map((p,i)=>`<div class="mrow" draggable="true" data-m="${p}"><span class="muted">⋮⋮</span><span class="nm">${esc(t(TITLES[p]))}</span>
  <button type="button" data-mup="${p}" ${i===0?"disabled":""} aria-label="${esc(t("Move up"))}">▲</button><button type="button" data-mdn="${p}" ${i===list.length-1?"disabled":""} aria-label="${esc(t("Move down"))}">▼</button>
  <button type="button" class="${pins.has(p)?"on":""}" data-mpin="${p}" aria-label="${esc(t("Pin"))}">${pins.has(p)?"★":"☆"}</button></div>`).join("");
}
function menuMove(p,dir){const o=menuOrder(),i=o.indexOf(p),vis=x=>!ADMIN_PAGES.includes(x)||isAdmin;
 let j=i+dir;while(j>=0&&j<o.length&&!vis(o[j]))j+=dir;if(j<0||j>=o.length)return;
 [o[i],o[j]]=[o[j],o[i]];menuSave(o,PREFS.pins||[]);}
$("menuedit").onclick=e=>{
 const u=e.target.closest("[data-mup]"),d=e.target.closest("[data-mdn]"),p=e.target.closest("[data-mpin]");
 if(u)menuMove(u.dataset.mup,-1);else if(d)menuMove(d.dataset.mdn,1);
 else if(p){const s=new Set(PREFS.pins||[]);s.has(p.dataset.mpin)?s.delete(p.dataset.mpin):s.add(p.dataset.mpin);menuSave(menuOrder(),[...s]);}
};
let mdrag=null;
$("menuedit").addEventListener("dragstart",e=>{const r=e.target.closest(".mrow");if(!r)return;mdrag=r.dataset.m;r.classList.add("drag");try{e.dataTransfer.setData("text/plain",mdrag);e.dataTransfer.effectAllowed="move";}catch(x){}});
$("menuedit").addEventListener("dragover",e=>{const r=e.target.closest(".mrow");if(!r||!mdrag)return;e.preventDefault();qsa(".mrow.over").forEach(x=>x.classList.remove("over"));r.classList.add("over");});
$("menuedit").addEventListener("dragend",()=>{mdrag=null;qsa(".mrow").forEach(x=>x.classList.remove("drag","over"));});
$("menuedit").addEventListener("drop",e=>{const r=e.target.closest(".mrow");if(!r||!mdrag)return;e.preventDefault();
 const o=menuOrder().filter(x=>x!==mdrag),to=o.indexOf(r.dataset.m);o.splice(to<0?o.length:to,0,mdrag);mdrag=null;menuSave(o,PREFS.pins||[]);});
$("menureset").onclick=()=>menuSave([],[]);
$("payout").onchange=e=>{let v=parseInt(e.target.value,10);if(!(v>=0))v=5;v=Math.min(90,v);PREFS.payout=v;e.target.value=v;savePrefs();rerender();};

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
const TT={srv:0,orders:0,profit:0,users:0,dev:0,hist:0};
function pageLoad(force){
 const p=page(),now=Date.now();
 if(p==="orders"&&(force||now-TT.orders>4500)){TT.orders=now;loadOrders();}
 if(p==="profit"&&isAdmin&&(force||now-TT.profit>15000)){TT.profit=now;loadProfit();}
 if(p==="history"&&(force||now-TT.hist>6000)){TT.hist=now;loadHistory();}
 if(p==="programs"&&isAdmin&&force){loadPrograms();}
 if(p==="server"&&isAdmin&&(force||now-TT.srv>8000)){TT.srv=now;loadServer();}
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

// ================= overview editing =================
const OV_DEFAULT=["today","month","all","avg","stock","stockval","forecast","profit","lastorder","revrate","others","chart","latest","pending","reviews","keys","stockp","status"];
const OV_NAMES={today:"Today",month:"This month",all:"All time",avg:"Average order",stock:"In stock",stockval:"Stock value",forecast:"Month forecast",profit:"Profit this month",lastorder:"Latest order",revrate:"Reviews per order",others:"Other currencies",chart:"Sales per month",latest:"Latest orders",pending:"Waiting to be completed",reviews:"Reviews",keys:"Keys left",stockp:"Stock panel",status:"Eldorado connection"};
let OVEDIT=false,OVSEL="";
function ovOrder(){const o=(PREFS.ovorder||[]).filter(x=>OV_DEFAULT.includes(x));return [...o,...OV_DEFAULT.filter(x=>!o.includes(x))];}
function ovStyle(){let st=$("ovstyle");if(!st){st=document.createElement("style");st.id="ovstyle";document.head.appendChild(st);}
 st.textContent=ovOrder().map((k,i)=>`#ovg [data-mod="${k}"]{order:${i+1}}`).join("");}
function ovPresent(){return ovOrder().filter(k=>document.querySelector(`#ovg [data-mod="${k}"]`)&&!hid(k));}
function ovMove(k,to){const o=ovOrder(),from=o.indexOf(k);if(from<0||k===to)return;o.splice(from,1);let i=o.indexOf(to);if(i<0)return;if(from<=o.indexOf(to)+0&&false)i++;
 o.splice(from<ovOrder().indexOf(to)?i+1:i,0,k);PREFS.ovorder=o;savePrefs();ovStyle();ovUi();}
function ovStep(k,dir){const v=ovPresent(),i=v.indexOf(k),n=v[i+dir];if(i<0||!n)return;ovMove(k,n);}
function ovUi(){const bar=$("ovbar");document.body.classList.toggle("ovedit",OVEDIT);
 if(!OVEDIT){bar.hidden=true;document.querySelectorAll("#ovg [data-mod]").forEach(e=>{e.removeAttribute("draggable");e.classList.remove("sel","drag","over");});$("ovedit").hidden=false;return;}
 $("ovedit").hidden=true;bar.hidden=false;
 document.querySelectorAll("#ovg [data-mod]").forEach(e=>{e.draggable=true;e.classList.toggle("sel",e.dataset.mod===OVSEL);});
 const rem=OV_DEFAULT.filter(k=>hid(k)&&(k!=="profit"||isAdmin)&&(k!=="others"||true));
 bar.innerHTML=`<b>${t("Edit overview")}</b><span class="hint">${OVSEL?esc(t(OV_NAMES[OVSEL]||OVSEL))+": ":""}${t("drag a module, or tap it and use the arrows")}</span><span class="sp"></span>`
  +(OVSEL?`<button class="btn" data-ovs="-1" aria-label="${t("Move earlier")}">‹</button><button class="btn" data-ovs="1" aria-label="${t("Move later")}">›</button><button class="btn" data-ovrm="1">${t("Remove")}</button>`:"")
  +`<button class="btn" id="ovreset">${t("Reset")}</button><button class="btn pri" id="ovdone">${t("Done")}</button>`
  +(rem.length?`<div style="flex-basis:100%;display:flex;flex-wrap:wrap;gap:6px;align-items:center"><span class="hint">${t("Hidden modules")}:</span>${rem.map(k=>`<button class="chip" data-ovadd="${k}">+ ${esc(t(OV_NAMES[k]||k))}</button>`).join("")}</div>`:"");}
$("ovedit").onclick=()=>{OVEDIT=true;OVSEL="";ovUi();};
$("ovbar").onclick=e=>{const b=e.target.closest("button");if(!b)return;
 if(b.id==="ovdone"){OVEDIT=false;OVSEL="";ovUi();return;}
 if(b.id==="ovreset"){PREFS.ovorder=[];PREFS.hide=(PREFS.hide||[]).filter(x=>!OV_DEFAULT.includes(x)||x==="profit"&&false);savePrefs();ovStyle();rerender();setTimeout(ovUi,50);return;}
 if(b.dataset.ovs){ovStep(OVSEL,parseInt(b.dataset.ovs,10));return;}
 if(b.dataset.ovrm){PREFS.hide=[...new Set([...(PREFS.hide||[]),OVSEL])];OVSEL="";savePrefs();rerender();setTimeout(ovUi,50);return;}
 if(b.dataset.ovadd){PREFS.hide=(PREFS.hide||[]).filter(x=>x!==b.dataset.ovadd);savePrefs();rerender();setTimeout(ovUi,50);}};
$("ovg").addEventListener("click",e=>{if(!OVEDIT)return;e.preventDefault();e.stopPropagation();const m=e.target.closest("[data-mod]");OVSEL=m&&m.dataset.mod!==OVSEL?m.dataset.mod:"";ovUi();},true);
$("ovg").addEventListener("dragstart",e=>{const m=e.target.closest&&e.target.closest("[data-mod]");if(!OVEDIT||!m){return;}OVSEL=m.dataset.mod;e.dataTransfer.effectAllowed="move";try{e.dataTransfer.setData("text/plain",OVSEL);}catch(x){}m.classList.add("drag");});
$("ovg").addEventListener("dragover",e=>{if(!OVEDIT)return;const m=e.target.closest("[data-mod]");if(!m)return;e.preventDefault();document.querySelectorAll("#ovg .over").forEach(x=>{if(x!==m)x.classList.remove("over");});if(m.dataset.mod!==OVSEL)m.classList.add("over");});
$("ovg").addEventListener("drop",e=>{if(!OVEDIT)return;const m=e.target.closest("[data-mod]");e.preventDefault();if(m&&OVSEL)ovMove(OVSEL,m.dataset.mod);});
let ovY=-1,ovRaf=0;
function ovScroll(){if(ovY<0){ovRaf=0;return;}const z=Math.min(110,innerHeight*.18);let v=0;
 if(ovY<z)v=-Math.ceil((z-ovY)/z*26);else if(ovY>innerHeight-z)v=Math.ceil((ovY-(innerHeight-z))/z*26);
 if(v)window.scrollBy(0,v);ovRaf=requestAnimationFrame(ovScroll);}
function ovScrollStop(){ovY=-1;}
document.addEventListener("dragover",e=>{if(!OVEDIT||e.clientY===undefined)return;ovY=e.clientY;if(!ovRaf)ovRaf=requestAnimationFrame(ovScroll);});
document.addEventListener("drop",ovScrollStop);document.addEventListener("dragend",ovScrollStop);
$("ovg").addEventListener("dragend",()=>{document.querySelectorAll("#ovg .drag,#ovg .over").forEach(x=>x.classList.remove("drag","over"));});
new MutationObserver(()=>{if(OVEDIT)document.querySelectorAll("#ovg [data-mod]").forEach(e=>{if(e.draggable!==true)e.draggable=true;if(e.classList.contains("sel")!==(e.dataset.mod===OVSEL))e.classList.toggle("sel",e.dataset.mod===OVSEL);});}).observe($("ovg"),{childList:true,subtree:true});

// ================= stock cost, backups, alarm click =================
$("alarm").onclick=()=>{location.hash="#programs";};
$("stock").addEventListener("change",async e=>{const i=e.target.closest("[data-ucost]");if(!i)return;
 const v=i.value.trim()===""?null:parseFloat(i.value.replace(",","."));if(v!==null&&!(v>=0)){i.value="";return;}
 try{const r=await post("/api/unitcost",{title:i.dataset.ucost,cost:v},"PUT");if(r.ok){const L=window.__last;if(L){L.unitcosts=L.unitcosts||{};if(v===null)delete L.unitcosts[i.dataset.ucost];else L.unitcosts[i.dataset.ucost]=v;}toast(t("Saved"),"");rerender();}}catch(x){}});
let bkAt=0;
function bkSize(n){return n>1048576?(n/1048576).toFixed(1)+" MB":Math.max(1,Math.round(n/1024))+" KB";}
async function loadBackups(act){
 if(!isAdmin)return;bkAt=Date.now();
 try{const r=act==="now"?await post("/api/backups",{}):await fetch("/api/backups");if(!r.ok)return;const j=await r.json();
  $("bklist").innerHTML=j.backups.length?j.backups.slice(0,8).map(b=>`<div class="bkrow"><div>${esc(full(b.time))}<small class="muted" style="display:block">${bkSize(b.size)}${/-manual/.test(b.name)?" · "+t("manual"):/-safety/.test(b.name)?" · "+t("before a restore"):""}</small></div>
   <div class="mini2"><a class="btn" href="/api/backups/${encodeURIComponent(b.name)}" download>${t("Download")}</a><button class="btn" data-bkrestore="${esc(b.name)}" type="button">${t("Restore")}</button></div></div>`).join(""):`<div class="empty">${t("No backups yet. The first one is taken within a few minutes.")}</div>`;
 }catch(e){}
}
$("bknow").onclick=async()=>{$("bknow").disabled=true;await loadBackups("now");$("bknow").disabled=false;toast(t("Backup"),t("Backup taken."));};
let bkArm=null;
$("bklist").addEventListener("click",async e=>{const b=e.target.closest("[data-bkrestore]");if(!b)return;
 if(bkArm!==b.dataset.bkrestore){bkArm=b.dataset.bkrestore;b.textContent=t("Sure?");setTimeout(()=>{if(bkArm===b.dataset.bkrestore){bkArm=null;b.textContent=t("Restore");}},4000);return;}
 bkArm=null;b.disabled=true;
 try{const r=await post("/api/backups/restore",{name:b.dataset.bkrestore});const j=await r.json();
  $("bkmsg").textContent=r.ok?t("Restored")+" "+plural(j.restored,"file")+". "+t("Restart the dashboard now so everything is read again.")+" "+t("(Your data from before is saved as a safety backup.)"):(j.error||t("Could not restore."));
 }catch(x){$("bkmsg").textContent=t("Could not restore.");}
 b.disabled=false;b.textContent=t("Restore");loadBackups();});

// ================= server page, restart, password =================
const gb=n=>n==null?"-":(n/1073741824>=10?(n/1073741824).toFixed(0):(n/1073741824).toFixed(1))+" GB";
const mbs=n=>n>1048576?(n/1048576).toFixed(1)+" MB":Math.max(1,Math.round((n||0)/1024))+" KB";
function upText(sec){const d=Math.floor(sec/86400),h=Math.floor(sec%86400/3600),m=Math.floor(sec%3600/60);return d?d+" "+t("d")+" "+h+" "+t("h"):h?h+" "+t("h")+" "+m+" min":m+" min";}
async function loadServer(){
 if(!isAdmin)return;
 try{const r=await fetch("/api/server");if(!r.ok)return;const j=await r.json();
  const row=(l,v,sub)=>`<div class="r1"><div>${t(l)}${sub?`<small>${sub}</small>`:""}</div><div class="v">${v}</div></div>`;
  const bar=(used,total,warn)=>`<div class="qbar ${warn?"warn":""}"><i style="width:${Math.min(100,Math.round(used*100/total))}%"></i></div>`;
  let h=row("Running for",esc(upText(j.uptime)),esc(t("since"))+" "+esc(full(j.started)));
  if(j.disk){const freePct=j.disk.free*100/j.disk.total,low=freePct<10||j.disk.free<5*1073741824;
   h+=`<div class="r1"><div>${t("Disk space")}<small>${gb(j.disk.free)} ${t("free of")} ${gb(j.disk.total)}</small></div><div class="v">${low?`<span class="pill warn">${t("running low")}</span>`:`<span class="pill good">OK</span>`}${bar(j.disk.used,j.disk.total,low)}</div></div>`;}
  if(j.mem){const used=j.mem.total-j.mem.free,low=j.mem.free*100/j.mem.total<10;
   h+=`<div class="r1"><div>${t("Memory")}<small>${gb(j.mem.free)} ${t("free of")} ${gb(j.mem.total)}</small></div><div class="v">${low?`<span class="pill warn">${t("running low")}</span>`:`<span class="pill good">OK</span>`}${bar(used,j.mem.total,low)}</div></div>`;}
  const old=j.backups.last&&(Date.now()-new Date(j.backups.last))>36*36e5;
  h+=row("Latest backup",j.backups.last?`<span class="pill ${old?"warn":"good"}">${esc(ago(j.backups.last))}</span>`:`<span class="pill warn">${t("none yet")}</span>`,plural(j.backups.n,"backup")+" · "+mbs(j.backups.size));
  h+=row("Your data",mbs(j.data),j.files.n?plural(j.files.n,"War-Room file")+" · "+mbs(j.files.size):"");
  h+=row("Programs",j.programs.managed?`<span class="pill ${j.programs.running===j.programs.total?"good":"warn"}">${j.programs.running} / ${j.programs.total} ${t("running")}</span>`:t("not managed here"));
  h+=row("Version",j.commit?esc(j.commit.hash):"-",j.commit?esc(full(j.commit.date))+" · "+esc(j.commit.subject):esc(t("not a git clone")));
  h+=row("Computer",esc(j.system),"Python "+esc(j.python));
  $("srvbox").innerHTML=h;$("srvsum").textContent=j.demo?t("demo"):"";
  $("srvrestart").disabled=!j.supervised;
  if(!j.supervised)$("srvmsg").textContent=t("Restart is only possible when the dashboard is started with  py start_all.py  (or the autostart).");
 }catch(e){}
}
let srvArm=false;
$("srvrestart").onclick=async()=>{
 const b=$("srvrestart");
 if(!srvArm){srvArm=true;b.textContent=t("Sure?");setTimeout(()=>{srvArm=false;b.textContent=t("Restart the dashboard");},4000);return;}
 srvArm=false;b.disabled=true;
 try{const r=await post("/api/restart",{});const j=await r.json();
  if(!r.ok){$("srvmsg").textContent=t(j.error||"Error");b.disabled=false;b.textContent=t("Restart the dashboard");return;}
  if(j.demo){$("srvmsg").textContent=t("Demo: nothing restarted.");b.disabled=false;b.textContent=t("Restart the dashboard");return;}
 }catch(e){}
 $("srvmsg").textContent=t("Restarting... this page reloads when the dashboard is back.");
 const t0=Date.now();await new Promise(r=>setTimeout(r,4000));
 const tick=async()=>{try{const r=await fetch("/api/server",{cache:"no-store"});if(r.ok){location.reload();return;}}catch(e){}
  if(Date.now()-t0<120000)setTimeout(tick,2000);else{$("srvmsg").textContent=t("It is taking longer than normal. Check the window on the server.");b.disabled=false;b.textContent=t("Restart the dashboard");}};
 tick();
};
$("pwsave").onclick=async()=>{
 const o=$("pwold").value,n=$("pwnew").value,n2=$("pwnew2").value,m=$("pwmsg");
 if(n.length<8){m.textContent=t("The new password must be at least 8 characters.");return;}
 if(n!==n2){m.textContent=t("The two new passwords are not the same.");return;}
 $("pwsave").disabled=true;
 try{const r=await post("/api/password",{old:o,new:n});const j=await r.json();
  if(r.ok){$("pwold").value=$("pwnew").value=$("pwnew2").value="";m.textContent=t("Password changed. Your other devices are logged out.");toast(t("Password"),t("Password changed."));}
  else m.textContent=t(j.error||"Error");
 }catch(e){m.textContent=t("Could not reach the server.");}
 $("pwsave").disabled=false;
};

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
let pushOn=false,pushErr="";
const b64u8=s=>{s=s.replace(/-/g,"+").replace(/_/g,"/");s+="=".repeat((4-s.length%4)%4);const r=atob(s);return Uint8Array.from(r,c=>c.charCodeAt(0));};
async function pushSubscribe(){
 pushOn=false;
 try{
  if(!("serviceWorker" in navigator)||!("PushManager" in window)){pushErr=iosWeb?t("On iPhone, open the app from the home screen icon first."):t("This browser cannot receive notifications when closed.");return;}
  const k=await (await fetch("/api/push/key")).json();if(!k.enabled){pushErr=k.reason?t("The server cannot send notifications yet")+" ("+k.reason+")":t("The server cannot send notifications yet");return;}
  const reg=await navigator.serviceWorker.ready;let sub=await reg.pushManager.getSubscription();
  if(sub){const cur=sub.options&&sub.options.applicationServerKey;
   if(cur&&btoa(String.fromCharCode(...new Uint8Array(cur))).replace(/\+/g,"-").replace(/\//g,"_").replace(/=+$/,"")!==k.key){await sub.unsubscribe();sub=null;}}
  if(!sub)sub=await reg.pushManager.subscribe({userVisibleOnly:true,applicationServerKey:b64u8(k.key)});
  const r=await post("/api/push/subscribe",{subscription:sub.toJSON()});pushOn=r.ok;if(!r.ok)pushErr=t("The server did not accept this device");else pushErr="";
 }catch(e){pushOn=false;pushErr=t("Could not register this device")+" ("+(e&&e.name||"error")+")";}
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
  if(!pushOn&&pushErr)toast(t("Notifications"),pushErr);
  try{const reg=await navigator.serviceWorker.getRegistration();const o={body:pushOn?t("You will get notifications even when the app is closed."):t("Notifications are on while the page is open."),icon:"/icon-192.png"};
   if(reg)await reg.showNotification("War-Room",o);else new Notification("War-Room",o);}catch(e){}}
}
$("pushtest").onclick=async()=>{const b=$("pushtest");b.disabled=true;try{const r=await post("/api/push/test",{});const j=await r.json();
 toast(t("Test notification"),j.ok?t("Sent. It should arrive in a few seconds, also if the app is closed.")+" "+(j.results||[]).join(", "):(j.error?t(j.error):"")+" "+(j.results||[]).join(", "));}catch(e){toast(t("Test notification"),t("Could not reach the server."));}b.disabled=false;};
$("tnote").onclick=toggleNotifications;$("setnote").onclick=toggleNotifications;
document.addEventListener("pointerdown",()=>audio(),{once:true});
document.addEventListener("keydown",()=>audio(),{once:true});
function wrAlert(msgs){
 const others=msgs.filter(m=>m.user!==wrMe);if(!others.length||!PREFS.notify.warroom)return;
 ding();
 others.filter(m=>(m.mentions||[]).includes(wrMe)).forEach(m=>toast(m.user+" "+t("mentioned you"),(m.text||("📎 "+(m.file&&m.file.name||""))).slice(0,90),()=>{location.hash="#warroom";}));
 try{if(navigator.vibrate)navigator.vibrate(80);}catch(e){}
 const away=document.hidden||page()!=="warroom";
 if(away){wrUnreadTitle+=others.length;document.title="("+wrUnreadTitle+") "+t("War-Room");}
 if(away&&noteOn&&notifyOK()&&Notification.permission==="granted"){
  const m=others[others.length-1];
  const title="War-Room · "+m.user,opts={body:(m.text||("📎 "+(m.file&&m.file.name||""))).slice(0,140),tag:"warroom",renotify:true,icon:"/icon-192.png",badge:"/icon-192.png"};
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
function fileHtml(m){
 const f=m.file;if(!f||!/^[0-9a-f]{32}\.(png|jpg|gif|webp|pdf)$/.test(f.id||""))return "";
 const u="/api/warroom/file/"+f.id,sz=f.size>1048576?(f.size/1048576).toFixed(1)+" MB":Math.max(1,Math.round(f.size/1024))+" KB";
 return f.kind==="image"?`<a href="${u}" target="_blank" rel="noopener"><img class="wimg" src="${u}" alt="${esc(f.name)}" loading="lazy"></a>`
  :`<a class="wpdf" href="${u}" target="_blank" rel="noopener">📄 ${esc(f.name)} · ${sz}</a>`;
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
  else body=`<div class="bub" title="${esc(full(m.time))}">${m.text?mentionHtml(m.text):""}${fileHtml(m)}${m.edited?'<span class="edited">('+t("edited")+')</span>':""}</div>`
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
 else if(a==="save"){const t=$("ed-"+id).value.trim(),m0=wrMsgs.find(x=>x.id===id);if(!t&&!(m0&&m0.file))return;
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

// ---- pictures and PDFs in the War-Room ----
async function wrUpload(file){
 if(!file)return;
 if(file.size>5*1048576){$("wmsg").textContent=t("The file is too big (max 5 MB).");return;}
 $("wsend").disabled=true;$("wattach").disabled=true;$("wmsg").textContent=t("Uploading...");
 const fd=new FormData();fd.append("file",file,file.name||"picture.png");fd.append("text",$("wt").value.trim());
 try{const r=await fetch("/api/warroom/upload",{method:"POST",headers:{"X-Requested-With":"dashboard"},body:fd});const j=await r.json();
  if(r.ok){$("wt").value="";$("wt").style.height="";$("wmsg").textContent="";await wrPoll();$("msgs").scrollTop=$("msgs").scrollHeight;}
  else $("wmsg").textContent=t(j.error||"Error");
 }catch(e){$("wmsg").textContent=t("Could not reach the server.");}
 $("wsend").disabled=false;$("wattach").disabled=false;$("wfile").value="";
}
$("wattach").onclick=()=>$("wfile").click();
$("wfile").onchange=e=>wrUpload(e.target.files[0]);
$("wt").addEventListener("paste",e=>{const f=[...(e.clipboardData&&e.clipboardData.files||[])].find(x=>/^image\//.test(x.type));if(f){e.preventDefault();wrUpload(f);}});
$("msgs").addEventListener("dragover",e=>{if(e.dataTransfer&&[...e.dataTransfer.types].includes("Files"))e.preventDefault();});
$("msgs").addEventListener("drop",e=>{const f=e.dataTransfer&&e.dataTransfer.files[0];if(f){e.preventDefault();wrUpload(f);}});

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


// ================= short explanations when you tap a number =================
const HELP={
 "t-today":["Sales today, after Eldorado's fees (or before them if you chose Gross). The small line shows the number of orders.","Dagens salg efter Eldorados gebyrer (eller før, hvis du har valgt Brutto). Den lille linje viser antal ordrer."],
 "t-month":["Sales so far this month. The arrow compares with the same days of last month.","Salg hidtil denne måned. Pilen sammenligner med de samme dage sidste måned."],
 "t-all":["Everything counted since the dashboard started following your orders.","Alt der er talt med, siden dashboardet begyndte at følge dine ordrer."],
 "t-avg":["The average sale: the total divided by the number of orders.","Gennemsnitligt salg: samlet beløb delt med antal ordrer."],
 "t-stockval":["What everything you have for sale is worth at your listed prices (items and accounts). Add what each unit cost you on the Stock page to see the expected profit after Eldorado fees.","Hvad alt, du har til salg, er værd til dine priser (items og konti). Skriv hvad hver enhed kostede dig på Lager-siden, så ser du forventet profit efter Eldorados gebyr."],
 "t-forecast":["Where this month ends if the pace holds: average of this month's daily pace and the last 7 days. The range goes from the slower to the faster of the two.","Hvor måneden ender, hvis tempoet holder: gennemsnit af månedens daglige tempo og de sidste 7 dage. Spændet går fra den langsomste til den hurtigste af de to."],
 "s-forecast":["Where this month ends if the pace holds: average of this month's daily pace and the last 7 days.","Hvor måneden ender, hvis tempoet holder: gennemsnit af månedens daglige tempo og de sidste 7 dage."],
 "t-stock":["Units in stock across all your offers on Eldorado.","Antal enheder på lager på tværs af alle dine tilbud på Eldorado."],
 "t-profit":["Sales after fees minus your costs (VPS, keys and so on) this month. Add costs on the Profit page.","Salg efter gebyrer minus dine omkostninger (VPS, keys osv.) denne måned. Tilføj omkostninger på Profit-siden."],
 "taxpot":["A joke counter: the percent you set in Settings, of your profit, in kroner. It shows how much tax we would have paid.","En joke-tæller: den procent, du har sat i Indstillinger, af din profit, i kroner. Viser hvor meget skat vi ville have betalt."],
 "lastorder":["Time since the latest order. It turns amber after 2 hours and red after 6 hours without a sale.","Tid siden seneste ordre. Den bliver gul efter 2 timer og rød efter 6 timer uden salg."],
 "revrate":["The share of all your orders that have got a review.","Andelen af alle dine ordrer, der har fået en anmeldelse."],
 "s-avg":["The average sale: the total divided by the number of orders.","Gennemsnitligt salg: samlet beløb delt med antal ordrer."],
 "s-best":["Your best day so far, counted after fees.","Din bedste dag indtil nu, regnet efter gebyrer."],
 "s-ords":["How many orders you have had this month.","Hvor mange ordrer du har haft denne måned."],
 "s-growth":["This month so far, compared with the same days of last month. Green is more, red is less.","Denne måned indtil nu sammenlignet med de samme dage sidste måned. Grøn er mere, rød er mindre."],
 "records":["Your best day, week and month so far. “New record!” means it is happening right now.","Din bedste dag, uge og måned indtil nu. “Ny rekord!” betyder, at det sker lige nu."],
 "fees":["What Eldorado keeps from your sales, and how much of the buyers' money you keep.","Hvad Eldorado tager af dit salg, og hvor stor en del af købernes penge du beholder."],
 "months":["Every month with sales, fees and orders. Growth compares with the month before.","Hver måned med salg, gebyrer og ordrer. Vækst sammenligner med måneden før."],
 "calendar":["Every day shows its sales and number of orders. The darker green, the better the day. Tap a day to see its orders.","Hver dag viser sit salg og antal ordrer. Jo mørkere grøn, jo bedre dag. Tryk på en dag for at se ordrerne."],
 "h-added":["Money added today from new orders, after fees.","Penge lagt til i dag fra nye ordrer, efter gebyrer."],
 "h-removed":["Money taken off today because orders were cancelled or refunded.","Penge trukket fra i dag, fordi ordrer blev annulleret eller refunderet."],
 "h-net":["Added minus removed this month.","Tilføjet minus fratrukket denne måned."],
 "h-bal":["Your total sales right now, after everything added and removed.","Dit samlede salg lige nu, efter alt der er lagt til og trukket fra."],
 "p-month":["This month's sales after fees, minus your costs and the cost of the keys sold.","Månedens salg efter gebyrer, minus dine omkostninger og prisen på de solgte keys."],
 "p-all":["Profit since the start: all sales after fees minus all costs.","Profit siden start: alt salg efter gebyrer minus alle omkostninger."],
 "p-costs":["Everything you have added as costs, plus the price of the keys you have sold.","Alt hvad du har tilføjet som omkostninger, plus prisen på de keys, du har solgt."],
 "mini-rev":["The share of good reviews out of all reviews.","Andelen af gode anmeldelser ud af alle anmeldelser."],
 "mini-keys":["Keys waiting to be uploaded to Eldorado. The line below estimates how long they last at the pace of the last 7 days.","Keys der venter på at blive uploadet til Eldorado. Linjen under anslår, hvor længe de rækker i tempoet fra de seneste 7 dage."],
 "mini-stock":["Units that are for sale on Eldorado right now.","Enheder, der er til salg på Eldorado lige nu."],
 "status":["Shows if the dashboard can reach Eldorado. If something fails, it tries again by itself.","Viser om dashboardet kan nå Eldorado. Hvis noget fejler, prøver det igen af sig selv."]
};
let helpTimer=null,helpAt=0;
function helpHide(){const h=$("help");h.hidden=true;clearTimeout(helpTimer);}
document.addEventListener("click",e=>{
 const h=$("help");
 if(!h.hidden&&!e.target.closest("[data-help]"))helpHide();
 const el=e.target.closest("[data-help]");if(!el)return;
 if(e.target.closest("button,a,input,select,textarea,label,[data-oid],[data-buyer],[data-copy],.row2,.cd,.hrow"))return;
 const lab=el.querySelector(el.classList.contains("tile")?".l":":scope>h2");if(!lab)return;
 const rg=document.createRange();rg.selectNodeContents(lab);const rs=rg.getClientRects(),lr=rs[rs.length-1];if(!lr)return;
 if(e.clientX<lr.right-2||e.clientX>lr.right+26||e.clientY<lr.top-8||e.clientY>lr.bottom+8)return;
 const tx=HELP[el.dataset.help];if(!tx)return;
 h.textContent=tx[LANG==="da"?1:0];h.hidden=false;
 const r=el.getBoundingClientRect(),w=h.offsetWidth,hh=h.offsetHeight;
 let top=r.bottom+8;if(top+hh>innerHeight-8)top=Math.max(8,r.top-hh-8);
 h.style.top=top+"px";h.style.left=Math.min(Math.max(8,r.left+12),innerWidth-w-8)+"px";
 helpAt=Date.now();clearTimeout(helpTimer);helpTimer=setTimeout(helpHide,9000);
});
document.addEventListener("keydown",e=>{if(e.key==="Escape")helpHide();});
window.addEventListener("scroll",()=>{if(Date.now()-helpAt>600)helpHide();},{passive:true});
setInterval(()=>{if(page()==="programs"&&isAdmin&&!document.hidden)loadPrograms();},2000);

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

PREFS.bg=lsGet("bg","");applyBg();PREFS.accent=lsGet("accent","");PREFS.sound=lsGet("sound","ding")||"ding";PREFS.lang=lsGet("lang","");PREFS.currency=CURSEL;
document.body.classList.toggle("hide",HIDE);
newsNav();
applyAccent();translateStatic();settingsUi();setTitle();
show();load(true);setInterval(load,5000);
setInterval(()=>{if(window.__last&&!document.hidden)render(window.__last);},30000);

// ================= NEXO EVO: living background, sliding menu light, spotlight, motion, command palette =================
(function(){
"use strict";
const RM=matchMedia("(prefers-reduced-motion:reduce)").matches;
const FINE=matchMedia("(hover:hover) and (pointer:fine)").matches;
const q=(s,r)=>(r||document).querySelector(s),qa=(s,r)=>[...(r||document).querySelectorAll(s)];
const small=()=>innerWidth<=820;
const lsGet=k=>{try{return localStorage.getItem(k);}catch(e){return null;}};
const lsPut=(k,v)=>{try{localStorage.setItem(k,v);}catch(e){}};
let FXON=lsGet("fx")!=="0"&&!RM;
const on=()=>FXON&&!document.body.classList.contains("fxoff");
function setFx(v){FXON=!!v&&!RM;lsPut("fx",v?"1":"0");document.body.classList.toggle("fxoff",!FXON);if(FXON)loop();}
const hooks={frame:[]};

// ---------- 1. background: aurora, grain, sparkle network, cursor glow ----------
const bg=document.createElement("div");bg.id="fxbg";bg.setAttribute("aria-hidden","true");
bg.innerHTML='<i class="a1"></i><i class="a2"></i><i class="a3"></i><i class="cur"></i><div class="grain"></div><canvas id="fxc"></canvas>';
document.body.prepend(bg);
const defs=document.createElement("div");
defs.innerHTML='<svg width="0" height="0" style="position:absolute" aria-hidden="true" focusable="false"><defs>'
 +'<linearGradient id="fxbar" x1="0" y1="0" x2="0" y2="1"><stop offset="0" style="stop-color:color-mix(in srgb,var(--accent) 78%,#fff)"/><stop offset="1" style="stop-color:var(--accent2)"/></linearGradient>'
 +'<linearGradient id="fxbarcur" x1="0" y1="0" x2="0" y2="1"><stop offset="0" style="stop-color:color-mix(in srgb,var(--accent) 55%,#fff)"/><stop offset=".55" style="stop-color:var(--accent)"/><stop offset="1" style="stop-color:color-mix(in srgb,var(--accent) 70%,#a855f7)"/></linearGradient>'
 +'<linearGradient id="fxsp" x1="0" y1="0" x2="0" y2="1"><stop offset="0" style="stop-color:var(--c);stop-opacity:.34"/><stop offset="1" style="stop-color:var(--c);stop-opacity:0"/></linearGradient>'
 +'</defs></svg>';
document.body.prepend(defs.firstChild);
const bar=document.createElement("div");bar.id="fxbar";document.body.appendChild(bar);
const flash=document.createElement("div");flash.id="fxflash";document.body.appendChild(flash);

const PC={overview:"#38bdf8",sales:"#34d399",history:"#a78bfa",orders:"#60a5fa",stock:"#fbbf24",reviews:"#f472b6",keys:"#2dd4bf",warroom:"#fb923c",mindmap:"#c084fc",profit:"#facc15",programs:"#94a3b8",server:"#22d3ee",users:"#818cf8",settings:"#cbd5e1",news:"#f0abfc"};
function curPage(){const h=(location.hash||"#overview").slice(1);return PC[h]?h:"overview";}
function setPageColor(){const p=curPage();document.body.dataset.page=p;document.body.style.setProperty("--pc",PC[p]);}
setPageColor();

const cv=q("#fxc"),cx=cv.getContext("2d"),cur=q("#fxbg .cur");
let W=0,H=0,DPR=1,P=[],mx=-9999,my=-9999,cxp=-9999,cyp=-9999,accent="#38bdf8",tick=0,running=false;
function size(){DPR=Math.min(devicePixelRatio||1,1.5);W=innerWidth;H=innerHeight;cv.width=Math.round(W*DPR);cv.height=Math.round(H*DPR);cx.setTransform(DPR,0,0,DPR,0,0);
 const n=small()?18:Math.min(70,Math.round(W*H/28000));P=[];
 for(let i=0;i<n;i++)P.push({x:Math.random()*W,y:Math.random()*H,r:.7+Math.random()*1.9,vx:(Math.random()-.5)*.14,vy:-.04-Math.random()*.2,ph:Math.random()*6.3,sp:.5+Math.random()*1.5,hot:Math.random()<.2});}
function draw(t){
 cx.clearRect(0,0,W,H);
 const light=document.documentElement.dataset.theme==="light";
 if(!(tick++%50)){const v=getComputedStyle(document.body).getPropertyValue("--pc").trim();if(v)accent=v;}
 cx.fillStyle=accent;cx.strokeStyle=accent;cx.lineWidth=1;
 const net=!small();
 for(let i=0;i<P.length;i++){const p=P[i];
  p.x+=p.vx;p.y+=p.vy;
  const dx=p.x-mx,dy=p.y-my,d2=dx*dx+dy*dy;
  if(d2<19600&&d2>1){const d=Math.sqrt(d2),f=(140-d)/140*.9;p.x+=dx/d*f;p.y+=dy/d*f;}
  if(p.y<-12){p.y=H+12;p.x=Math.random()*W;}if(p.x<-12)p.x=W+12;if(p.x>W+12)p.x=-12;
  const tw=.5+.5*Math.sin(t/1000*p.sp+p.ph),a=(light?.25:.22)+tw*(light?.45:.6);
  cx.globalAlpha=a*(p.hot?1:.7);const r=p.r;
  cx.beginPath();cx.moveTo(p.x,p.y-r*3.2);cx.lineTo(p.x+r*.9,p.y);cx.lineTo(p.x,p.y+r*3.2);cx.lineTo(p.x-r*.9,p.y);cx.closePath();cx.fill();
  if(p.hot){cx.beginPath();cx.moveTo(p.x-r*3.2,p.y);cx.lineTo(p.x,p.y+r*.9);cx.lineTo(p.x+r*3.2,p.y);cx.lineTo(p.x,p.y-r*.9);cx.closePath();cx.fill();}
  if(net){for(let j=i+1;j<P.length;j++){const o=P[j],ax=p.x-o.x,ay=p.y-o.y,dd=ax*ax+ay*ay;
   if(dd<14400){cx.globalAlpha=(1-dd/14400)*(light?.14:.18);cx.beginPath();cx.moveTo(p.x,p.y);cx.lineTo(o.x,o.y);cx.stroke();}}}
 }
 cx.globalAlpha=1;
}
function loop(){
 if(running)return;running=true;
 const step=t=>{
  if(!on()){running=false;cx.clearRect(0,0,W,H);return;}
  if(!document.hidden){draw(t);
   if(FINE&&mx>-999){cxp+=(mx-cxp)*.12;cyp+=(my-cyp)*.12;cur.style.transform="translate3d("+cxp+"px,"+cyp+"px,0)";}
   for(const f of hooks.frame)f(t);}
  requestAnimationFrame(step);};
 requestAnimationFrame(step);
}
size();let rz=0;addEventListener("resize",()=>{clearTimeout(rz);rz=setTimeout(()=>{size();navMove(true);},120);});
if(!on())document.body.classList.add("fxoff");
if(RM){size();draw(0);}else if(on())loop();

// ---------- 2. spotlight + 3D tilt on slabs, magnetic buttons ----------
let hot=null,magEl=null,lastE=null,raf=0;
const MAG="button.btn,a.btn,.ck-chip,.logowrap,.seg button";
function frame(){raf=0;const e=lastE;if(!e)return;
 const el=e.target.closest?e.target.closest(".tile,.panel"):null;
 if(hot&&hot!==el){hot.style.transform="";hot=null;}
 if(el){
  const r=el.getBoundingClientRect(),x=e.clientX-r.left,y=e.clientY-r.top;
  el.style.setProperty("--mx",x+"px");el.style.setProperty("--my",y+"px");
  if(on()&&el.classList.contains("tile")&&!el.classList.contains("sk")&&!document.body.classList.contains("ovedit")){
   const rx=((y/r.height)-.5)*-9,ry=((x/r.width)-.5)*12;
   el.style.transform="perspective(850px) rotateX("+rx.toFixed(2)+"deg) rotateY("+ry.toFixed(2)+"deg) translateY(-4px)";hot=el;}}
 const m=e.target.closest?e.target.closest(MAG):null;
 if(magEl&&magEl!==m){magEl.style.translate="";magEl=null;}
 if(m&&on()&&!small()){const r=m.getBoundingClientRect(),dx=e.clientX-(r.left+r.width/2),dy=e.clientY-(r.top+r.height/2);
  m.style.translate=(dx*.2).toFixed(1)+"px "+(dy*.28).toFixed(1)+"px";magEl=m;}
}
document.addEventListener("pointermove",e=>{if(e.pointerType!=="mouse")return;
 if(!document.body.classList.contains("mouse"))document.body.classList.add("mouse");
 mx=e.clientX;my=e.clientY;if(cxp<-999){cxp=mx;cyp=my;}
 lastE=e;if(!raf)raf=requestAnimationFrame(frame);},{passive:true});
document.documentElement.addEventListener("mouseleave",()=>{mx=my=-9999;if(hot){hot.style.transform="";hot=null;}if(magEl){magEl.style.translate="";magEl=null;}});

// ---------- 3. count-up for loose numbers (tiles have their own) ----------
const CU=new Map(),tok=new WeakMap();
function parseNum(s){
 const m=s.match(/^([^\d-]*)(-?\d[\d.,  ]*\d|-?\d)(.*)$/s);if(!m)return null;
 const raw=m[2];let dec="",th="";
 const ld=raw.lastIndexOf("."),lc=raw.lastIndexOf(",");
 if(ld>-1&&lc>-1){dec=ld>lc?".":",";th=dec==="."?",":".";}
 else if(ld>-1||lc>-1){const ch=ld>-1?".":",",cnt=raw.split(ch).length-1,after=raw.length-raw.lastIndexOf(ch)-1;
  if(cnt>1||after===3){th=ch;}else dec=ch;}
 if(/[  ]/.test(raw))th=th||(raw.match(/[  ]/)[0]);
 let clean=raw.replace(/[  ]/g,"");
 if(th&&th!==" ")clean=clean.split(th).join("");
 if(dec)clean=clean.replace(dec,".");
 const v=parseFloat(clean);if(!isFinite(v))return null;
 return {pre:m[1],post:m[3],v,dec,th,nd:dec?raw.length-raw.lastIndexOf(dec)-1:0};
}
function fmtNum(v,p){let s=Math.abs(v).toFixed(p.nd);let [i,f]=s.split(".");if(p.th)i=i.replace(/\B(?=(\d{3})+(?!\d))/g,p.th);return (v<0?"-":"")+i+(p.nd?(p.dec||".")+f:"");}
function countUp(el,key){
 if(!on()||!el||el.closest(".sk"))return;
 const n=el.firstChild;if(!n||n.nodeType!==3)return;
 const p=parseNum(n.textContent);if(!p)return;
 const prev=CU.has(key)?CU.get(key):0;CU.set(key,p.v);
 if(Math.abs(prev-p.v)<Math.pow(10,-p.nd)/2)return;
 const id={};tok.set(el,id);const t0=performance.now(),dur=Math.min(1300,500+Math.abs(p.v-prev)**.3*60);
 const step=t=>{if(tok.get(el)!==id||!n.parentNode)return;
  const k=Math.min(1,(t-t0)/dur),e=k===1?1:1-Math.pow(2,-10*k);
  n.textContent=p.pre+fmtNum(prev+(p.v-prev)*e,p)+p.post;
  if(k<1)requestAnimationFrame(step);};
 n.textContent=p.pre+fmtNum(prev,p)+p.post;requestAnimationFrame(step);
}
const sectionOf=el=>{const s=el.closest(".page");return s?s.id:"x";};
function numbersIn(root){
 const els=[];
 if(root.matches&&root.matches(".big,.taxpot b"))els.push(root);
 if(root.querySelectorAll)root.querySelectorAll(".big,.taxpot b").forEach(e=>els.push(e));
 els.forEach((e,i)=>countUp(e,sectionOf(e)+"|"+e.className+i));
}

// ---------- 4. entrances (staggered, deferred while off screen) ----------
let seq=0;
const io="IntersectionObserver" in window?new IntersectionObserver(es=>{es.forEach(en=>{if(en.isIntersecting){io.unobserve(en.target);play(en.target,0);}});},{rootMargin:"0px 0px -6% 0px"}):null;
function play(el,i){
 el.style.setProperty("--i",i);el.classList.add("fx-in");
 el.addEventListener("animationend",function f(e){if(e.target!==el)return;el.classList.remove("fx-in");el.removeEventListener("animationend",f);});
}
function enter(el){
 if(!on()||el.dataset.fxd||el.classList.contains("sk"))return;
 el.dataset.fxd="1";
 const top=el.getBoundingClientRect().top;
 if(io&&top>innerHeight*.98){io.observe(el);return;}
 play(el,Math.min(seq++,12));
}
const settle=new Map();
function pageIn(sec){
 seq=0;settle.set(sec.id,performance.now());
 for(const k of [...CU.keys()])if(k.indexOf(sec.id+"|")===0)CU.delete(k);
 qa(".tile,.panel,.bar2,.mmbar,.score,#cockpit",sec).forEach(el=>{delete el.dataset.fxd;});
 if(on()&&!small()){sec.classList.add("pg-in");setTimeout(()=>sec.classList.remove("pg-in"),800);}
 qa(":scope #cockpit,:scope .tile:not(.sk),:scope .panel:not(.welcome):not(.chat),:scope .chat,:scope .bar2,:scope .mmbar",sec).forEach(enter);
 sec.querySelectorAll(".dyn").forEach(d=>numbersIn(d));
 numbersIn(sec);
}
qa(".page").forEach(sec=>{
 new MutationObserver(()=>{if(sec.classList.contains("on")&&!sec._on){sec._on=1;pageIn(sec);}if(!sec.classList.contains("on"))sec._on=0;}).observe(sec,{attributes:true,attributeFilter:["class"]});
});
let lastCount=0;
new MutationObserver(ms=>{
 for(const m of ms){
  for(const n of m.addedNodes){
   if(n.nodeType!==1)continue;
   if(n.closest&&n.closest("#toasts,#cmdk,#fxbg,#drawer,#cockpit"))continue;
   const sec=n.closest&&n.closest(".page");
   if(sec){
    const age=performance.now()-(settle.get(sec.id)||0);
    if(age<1800){(n.matches&&n.matches(".tile,.panel,.bar2"))?enter(n):qa(".tile:not(.sk),.panel,.bar2",n).forEach(enter);}
    numbersIn(n);
   }
  }
 }
 const ms2=q("#msgs");if(ms2){const all=qa(".m",ms2);if(lastCount>0&&all.length>lastCount&&on())all.slice(lastCount).forEach(x=>x.classList.add("fresh"));lastCount=all.length;}
}).observe(document.querySelector("main"),{childList:true,subtree:true});
qa(".page.on").forEach(sec=>{sec._on=1;settle.set(sec.id,performance.now());qa("#cockpit,.panel,.bar2,.chat",sec).forEach(enter);});

// ---------- 5. page title: letters spring in ----------
const h1=q("#title");let lastTitle="";
function splitTitle(){
 if(!h1)return;const txt=h1.textContent;
 if(txt===lastTitle||!txt.trim())return;lastTitle=txt;
 h1.setAttribute("aria-label",txt);
 if(!on()||RM)return;
 h1.innerHTML=[...txt].map((c,i)=>c===" "?'<span class="ch" aria-hidden="true" style="--i:'+i+'">&nbsp;</span>':'<span class="ch" aria-hidden="true" style="--i:'+i+'">'+c.replace(/&/g,"&amp;").replace(/</g,"&lt;")+'</span>').join("");
 lastTitle=h1.textContent;
}
if(h1)new MutationObserver(()=>{if(!h1.querySelector(".ch")||h1.textContent!==lastTitle)splitTitle();}).observe(h1,{childList:true,characterData:true,subtree:true});
splitTitle();

// ---------- 6. menu: sliding light behind the active page ----------
const nav=q("#nav"),ind=document.createElement("div");ind.className="navind";nav.prepend(ind);
function navMove(instant){
 const a=q("#nav a.on");
 if(!a||a.hidden||!a.offsetWidth){if(ind.classList.contains("ready"))ind.classList.remove("ready");return;}
 const first=!ind.classList.contains("ready");
 if(instant||first){ind.style.transition="none";}
 ind.style.top=a.offsetTop+"px";ind.style.left=a.offsetLeft+"px";ind.style.width=a.offsetWidth+"px";ind.style.height=a.offsetHeight+"px";
 if(instant||first){void ind.offsetWidth;ind.style.transition="";}
 if(first)ind.classList.add("ready");
 if(small()){try{a.scrollIntoView({inline:"center",block:"nearest",behavior:instant||RM?"auto":"smooth"});}catch(e){}}
}
new MutationObserver(ms=>{if(ms.some(m=>m.target!==ind))navMove();}).observe(nav,{attributes:true,attributeFilter:["class","hidden"],subtree:true,childList:true});
addEventListener("hashchange",()=>{setPageColor();setTimeout(()=>navMove(),30);
 if(navigator.vibrate&&!FINE)try{navigator.vibrate(8);}catch(e){}});
if(document.fonts&&document.fonts.ready)document.fonts.ready.then(()=>navMove(true));
setTimeout(()=>navMove(true),60);setTimeout(()=>navMove(true),600);

// ---------- 7. logo: shine + secret celebration ----------
const lg=q("#logo");
if(lg){const w=document.createElement("span");w.className="logowrap";lg.parentNode.insertBefore(w,lg);w.appendChild(lg);
 let c=0,t0=0;w.addEventListener("click",()=>{const n=performance.now();if(n-t0>2200)c=0;t0=n;if(++c>=5){c=0;celebrate();}});}

// ---------- 8. celebration burst ----------
function celebrate(){
 if(!on())return;
 flash.classList.remove("on");void flash.offsetWidth;flash.classList.add("on");
 if(window.FX&&FX.gemBurst)FX.gemBurst();
 let c=q("#fxcel");if(!c){c=document.createElement("canvas");c.id="fxcel";document.body.appendChild(c);}
 const d=Math.min(devicePixelRatio||1,2),w=innerWidth,h=innerHeight;c.width=w*d;c.height=h*d;const g=c.getContext("2d");g.setTransform(d,0,0,d,0,0);
 const cols=[accent,"#ffffff","#a78bfa","#67e8f9","#fbbf24","#f472b6"],ox=w/2,oy=Math.min(220,h*.28),L=[];
 for(let i=0;i<130;i++){const a=-Math.PI/2+(Math.random()-.5)*2.6,s=5+Math.random()*11;
  L.push({x:ox,y:oy,vx:Math.cos(a)*s,vy:Math.sin(a)*s-2,r:4+Math.random()*8,rot:Math.random()*6.3,vr:(Math.random()-.5)*.3,c:cols[i%cols.length],life:1,dec:.005+Math.random()*.008});}
 let ring=0;const t0=performance.now();
 (function st(){
  g.clearRect(0,0,w,h);ring=(performance.now()-t0)/800;
  if(ring<1){g.globalAlpha=1-ring;g.strokeStyle=accent;g.lineWidth=3;g.beginPath();g.arc(ox,oy,ring*Math.min(w,760)*.5,0,6.3);g.stroke();}
  let alive=0;
  L.forEach(p=>{if(p.life<=0)return;alive++;p.vy+=.28;p.vx*=.992;p.x+=p.vx;p.y+=p.vy;p.rot+=p.vr;p.life-=p.dec;
   g.save();g.translate(p.x,p.y);g.rotate(p.rot);g.globalAlpha=Math.max(0,Math.min(1,p.life*1.6));g.fillStyle=p.c;
   g.beginPath();g.moveTo(0,-p.r*1.5);g.lineTo(p.r,0);g.lineTo(0,p.r*1.5);g.lineTo(-p.r,0);g.closePath();g.fill();g.restore();});
  if(alive||ring<1)requestAnimationFrame(st);else c.remove();
 })();
}

// ---------- 9. loading line ----------
(function(){const of=window.fetch;let pend=0,tm=0;
 window.fetch=function(u){const url=typeof u==="string"?u:(u&&u.url)||"",tr=url.indexOf("/api/")===0&&url.indexOf("/api/data")!==0&&url.indexOf("/api/warroom")!==0||url.indexOf("/api/data")===0&&url.indexOf("h=")<0;
  if(tr){pend++;clearTimeout(tm);tm=setTimeout(()=>{if(pend>0&&on())bar.classList.add("on");},300);}
  const p=of.apply(this,arguments);
  if(tr){const done=()=>{pend=Math.max(0,pend-1);if(!pend){clearTimeout(tm);bar.classList.remove("on");}};p.then(done,done);}
  return p;};
})();

// ---------- 10. command palette ----------
const ICO={search:'<svg class="i" viewBox="0 0 24 24"><circle cx="11" cy="11" r="7"/><path d="M20 20l-3.5-3.5"/></svg>',
 act:'<svg class="i" viewBox="0 0 24 24"><path d="M13 2L4 14h7l-1 8 9-12h-7z"/></svg>',
 order:'<svg class="i" viewBox="0 0 24 24"><path d="M6 3h12v18l-3-2-3 2-3-2-3 2z"/><path d="M9 8h6M9 12h6"/></svg>',
 key:'<svg class="i" viewBox="0 0 24 24"><circle cx="8" cy="15" r="4"/><path d="M11 12l9-9M16 7l3 3"/></svg>'};
const mac=/Mac|iPhone|iPad/.test(navigator.platform||"");
const ck=document.createElement("div");ck.id="cmdk";ck.setAttribute("role","dialog");ck.setAttribute("aria-modal","true");ck.setAttribute("aria-label",t("Search or jump to..."));
ck.innerHTML='<div class="cmdk-box"><div class="cmdk-in">'+ICO.search+'<input id="cmdkq" type="text" autocomplete="off" spellcheck="false" aria-label="'+t("Search or jump to...")+'" placeholder="'+t("Search or jump to...")+'"><kbd>Esc</kbd></div><div class="cmdk-l" id="cmdkl" role="listbox"></div><div class="cmdk-f"><span><kbd>&uarr;</kbd> <kbd>&darr;</kbd> '+t("move")+'</span><span><kbd>Enter</kbd> '+t("open")+'</span></div></div>';
document.body.appendChild(ck);
let items=[],sel=0,prevFocus=null;
function entries(qs){
 const out=[],s=qs.trim().toLowerCase(),toks=s.split(/\s+/).filter(Boolean);
 const match=txt=>{const x=txt.toLowerCase();return toks.every(k=>x.indexOf(k)>-1);};
 const pages=qa("#nav a:not([hidden])").map(a=>({g:t("Go to"),ico:a.querySelector("svg")?a.querySelector("svg").outerHTML:ICO.act,label:a.textContent.trim(),hint:"",run:()=>{location.hash=a.getAttribute("href");}}));
 const acts=[
  {label:t("Hide or show numbers"),run:()=>$("hide").click()},
  {label:t("Switch light or dark"),run:()=>$("theme").click()},
  {label:t("Currency calculator"),run:()=>$("calcbtn").click()},
  {label:t("Refresh data"),run:()=>refreshAll()},
  {label:t("Animated background")+": "+(on()?t("off"):t("on")),run:()=>{setFx(!on());const c=q("#setFx");if(c)c.checked=on();}},
  {label:t("Celebrate"),run:()=>celebrate()},
  {label:t("Sign out"),run:()=>$("logout").click()}].map(a=>({g:t("Actions"),ico:ICO.act,hint:"",...a}));
 pages.concat(acts).forEach(e=>{if(!toks.length||match(e.label))out.push(e);});
 if(toks.length){
  const L=window.__last;
  if(L&&L.orders){let n=0;for(const o of L.orders){const hay=[o.id,o.buyer,o.item,o.state].join(" ");
   if(match(hay)){out.push({g:t("Orders"),ico:ICO.order,label:(o.item||"?")+" - "+(o.buyer||"?"),hint:money(ordAmt(o),o.price.currency),run:()=>openOrder(o.id)});if(++n>=7)break;}}}
  if(isAdmin&&/^[a-z0-9]{3,}-[a-z0-9-]{4,}$/i.test(qs.trim()))out.push({g:t("Keys"),ico:ICO.key,label:t("Find this key in the orders"),hint:qs.trim(),run:()=>{location.hash="#keys";setTimeout(()=>{const f=$("fk");if(f){f.value=qs.trim();$("fkgo").click();}},250);}});
 }
 return out;
}
function paint(){
 const list=q("#cmdkl");items=entries(q("#cmdkq").value);
 if(sel>=items.length)sel=Math.max(0,items.length-1);
 let h="",g="";
 items.forEach((e,i)=>{if(e.g!==g){g=e.g;h+='<div class="cmdk-g">'+esc(g)+'</div>';}
  h+='<div class="cmdk-i'+(i===sel?" on":"")+'" role="option" data-i="'+i+'">'+e.ico+'<b>'+esc(e.label)+'</b>'+(e.hint?'<small>'+esc(e.hint)+'</small>':"")+'</div>';});
 list.innerHTML=h||'<div class="cmdk-e">'+t("Nothing found.")+'</div>';
 const on_=q(".cmdk-i.on",list);if(on_)on_.scrollIntoView({block:"nearest"});
}
function openK(){if(ck.classList.contains("on"))return;prevFocus=document.activeElement;ck.classList.add("on");q("#cmdkq").value="";sel=0;paint();setTimeout(()=>q("#cmdkq").focus(),10);}
function closeK(){ck.classList.remove("on");if(prevFocus&&prevFocus.focus)try{prevFocus.focus({preventScroll:true});}catch(e){}}
function run(i){const e=items[i];if(!e)return;closeK();setTimeout(()=>e.run(),30);}
q("#cmdkq").addEventListener("input",()=>{sel=0;paint();});
q("#cmdkq").addEventListener("keydown",e=>{
 if(e.key==="ArrowDown"){sel=Math.min(items.length-1,sel+1);paint();e.preventDefault();}
 else if(e.key==="ArrowUp"){sel=Math.max(0,sel-1);paint();e.preventDefault();}
 else if(e.key==="Enter"){run(sel);e.preventDefault();}
 else if(e.key==="Tab"){e.preventDefault();}});
q("#cmdkl").addEventListener("click",e=>{const i=e.target.closest(".cmdk-i");if(i)run(+i.dataset.i);});
q("#cmdkl").addEventListener("pointermove",e=>{const i=e.target.closest(".cmdk-i");if(i&&+i.dataset.i!==sel){sel=+i.dataset.i;qa(".cmdk-i",ck).forEach((x,k)=>x.classList.toggle("on",k===sel));}});
ck.addEventListener("pointerdown",e=>{if(e.target===ck)closeK();});
document.addEventListener("keydown",e=>{
 if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==="k"){e.preventDefault();ck.classList.contains("on")?closeK():openK();}
 else if(e.key==="Escape"&&ck.classList.contains("on")){closeK();e.stopPropagation();}
 else if(e.key==="/"&&!/INPUT|TEXTAREA|SELECT/.test((document.activeElement||{}).tagName||"")&&!(document.activeElement||{}).isContentEditable){e.preventDefault();openK();}
},true);
const ht=q(".header-tools");
if(ht){const b=document.createElement("button");b.className="btn";b.id="cmdkbtn";b.type="button";b.setAttribute("aria-label",t("Search or jump to..."));
 b.innerHTML=ICO.search+'<span>'+t("Search")+'</span><kbd>'+(mac?"&#8984;K":"Ctrl K")+'</kbd>';b.onclick=openK;ht.prepend(b);}

// ---------- 11. settings switch, preview badge ----------
const fxc=q("#setFx");if(fxc){fxc.checked=on();fxc.onchange=()=>setFx(fxc.checked);}
if(window.NEXO_PREVIEW){const b=document.createElement("div");b.className="pvbadge";b.textContent=t("New design - preview");document.body.appendChild(b);}
window.FX={celebrate,setFx,openK,on,small,hooks,q,qa,get accent(){return accent;}};
})();

// ================= NEXO EVO: overview cockpit (3D gem, odometer, ticker) + tile decorations =================
(function(){
"use strict";
const q=(s,r)=>(r||document).querySelector(s),qa=(s,r)=>[...(r||document).querySelectorAll(s)];
const FXo=()=>window.FX&&FX.on();
const sec=q("#p-overview");if(!sec)return;
const RM=matchMedia("(prefers-reduced-motion:reduce)").matches;

const ck=document.createElement("div");ck.id="cockpit";
ck.innerHTML='<div class="ck-left"><div class="ck-lab"><i></i><span id="ckl"></span></div><div class="ck-big" id="ckbig"></div><div class="ck-sub" id="cksub"></div><div class="ck-chips" id="ckchips"></div><div class="ck-bars" id="ckbars"></div><div class="ck-cap"><span id="ckc1"></span><span id="ckc2"></span></div></div>'
 +'<div class="ck-gem"><canvas id="gem" aria-label="3D"></canvas><div class="ck-hint" id="ckhint"></div></div>'
 +'<div class="ck-ticker" id="ckticker" hidden><div class="ck-track" id="cktrack"></div></div>';
sec.prepend(ck);

let odoKey="";
function odo(el,str){
 const key=str.replace(/\d/g,"0");
 if(key!==odoKey||!el.querySelector(".odo")){
  odoKey=key;const keep=el.querySelector("small");
  el.innerHTML='<span class="odo" aria-label="'+str.replace(/"/g,"")+'">'+[...str].map(c=>/\d/.test(c)
   ?'<span class="dg"><b style="--d:0">'+"0123456789".split("").map(n=>"<i>"+n+"</i>").join("")+"</b></span>"
   :'<span class="sp">'+(c===" "?"&nbsp;":c.replace(/&/g,"&amp;"))+"</span>").join("")+"</span>";
  if(keep)el.appendChild(keep);
  void el.offsetWidth;
 }
 const ds=qa(".dg b",el);let k=0;
 [...str].forEach(c=>{if(/\d/.test(c)){const b=ds[k++];if(b)requestAnimationFrame(()=>requestAnimationFrame(()=>b.style.setProperty("--d",c)));}});
}

let lastSig="",seenIds=null;
function hourBars(d){
 const now=new Date(),b=new Array(24).fill(0);
 (d.orders||[]).forEach(o=>{const ago=Math.floor((now-new Date(o.time))/36e5);if(ago>=0&&ago<24)b[23-ago]++;});
 return {b,mxv:Math.max(1,...b),total:b.reduce((a,c)=>a+c,0)};
}
function fill(d){
 const s=d.sales,td=s.today,cur=shownCur();
 const sig=JSON.stringify([td,s.month.orders,d.pending.n,d.keys.left,d.reviews.positive,d.reviews.negative,(d.orders[0]||{}).id,cur,HIDE,GROSS,LANG,d.orders.length]);
 if(sig===lastSig)return;lastSig=sig;
 $("ckl").textContent=t("Today")+" · "+new Date().toLocaleDateString(LOC(),{weekday:"long",day:"numeric",month:"long"});
 odo($("ckbig"),fmt(mv(amtOf(td)),td.orders?2:0));
 const big=$("ckbig");let sm=big.querySelector("small");if(!sm){sm=document.createElement("small");big.appendChild(sm);}sm.textContent=cur;
 const g=growthInfo(s);
 $("cksub").innerHTML=plural(td.orders,"order")+" "+t("today")+(g?" · "+growthBadge(s):"");
 const todayStr=new Date().toDateString(),revs=d.reviews.items.filter(r=>new Date(r.time).toDateString()===todayStr);
 const chips=[
  {c:"var(--c2)",h:"#orders",l:t("Waiting to be completed"),v:d.pending.n},
  {c:"var(--c5)",h:"#reviews",l:t("Reviews"),v:revs.length},
  {c:d.keys.left<=10?"var(--amber)":"var(--c3)",h:"#keys",l:t("Keys"),v:d.keys.left},
  {c:"var(--c1)",h:"#sales",l:t("This month"),v:fmt(mv(amtOf(s.month)),0)+" "+cur}];
 $("ckchips").innerHTML=chips.map(c=>'<a class="ck-chip" href="'+c.h+'" style="--cc:'+c.c+'"><i></i>'+esc(c.l)+' <b>'+esc(String(c.v))+'</b></a>').join("");
 const hb=hourBars(d);
 $("ckbars").innerHTML=hb.b.map((v,i)=>'<i class="'+(i===23?"now":"")+'" style="--h:'+(v/hb.mxv).toFixed(3)+';--i:'+i+'" title="'+v+'"></i>').join("");
 $("ckc1").textContent="-24 "+t("hours");$("ckc2").textContent=t("now");
 const os=d.orders.slice(0,14),tk=$("ckticker");
 if(!os.length){tk.hidden=true;}
 else{
  tk.hidden=false;
  const ids=new Set(os.map(o=>o.id));
  const item=o=>'<span class="ck-ord'+(seenIds&&!seenIds.has(o.id)?" new":"")+'" data-oid="'+esc(o.id)+'"><s>'+esc((o.buyer||"?").slice(0,1).toUpperCase())+'</s><b>'+esc(o.item||"?")+'</b><em>'+esc(o.buyer||"")+' · '+esc(tm(o.time))+'</em><b>'+esc(money(ordAmt(o),o.price.currency))+'</b></span>';
  const html=os.map(item).join("");
  $("cktrack").innerHTML=html+html;
  $("cktrack").style.setProperty("--tk",Math.max(30,os.length*6)+"s");
  seenIds=ids;
 }
}
$("cktrack").addEventListener("click",e=>{const o=e.target.closest(".ck-ord");if(o&&window.openOrder)openOrder(o.dataset.oid);});
$("ckhint").textContent=t("Drag the diamond");

const baseRender=window.__render;
window.__render=function(d){baseRender(d);try{fill(d);decorate(d);}catch(e){console.error(e);}};
setInterval(()=>{if(window.__last&&!document.hidden){try{fill(window.__last);decorate(window.__last);}catch(e){}}},15000);

// ---------- tile decorations: watermark icon, sparkline, ring ----------
const WM={today:'<path d="M12 3v18M16.5 7.5C15.6 6.4 14 6 12 6c-2.3 0-4 1.1-4 3s1.7 2.6 4 3 4 1.1 4 3-1.7 3-4 3c-2 0-3.6-.6-4.5-1.7"/>',
 month:'<rect x="3" y="5" width="18" height="16" rx="3"/><path d="M3 10h18M8 3v4M16 3v4"/>',
 all:'<path d="M4 20V10M10 20V4M16 20v-8M22 20H2"/>',
 avg:'<path d="M3 12h18M12 3v18"/><circle cx="12" cy="12" r="9"/>',
 stock:'<path d="M21 8l-9-5-9 5v8l9 5 9-5zM3 8l9 5 9-5M12 13v8"/>',
 stockval:'<circle cx="12" cy="12" r="9"/><path d="M9 9h4.5a2 2 0 010 4H9m0 0h5a2 2 0 010 4H9M9 7v10"/>',
 forecast:'<path d="M3 17l6-6 4 4 8-9M15 6h6v6"/>',
 profit:'<path d="M12 2l3 6 6 .9-4.5 4.4 1.1 6.2L12 16.5 6.4 19.5l1.1-6.2L3 8.9 9 8z"/>',
 lastorder:'<circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/>',
 revrate:'<path d="M12 3l2.7 5.6 6.1.9-4.4 4.3 1 6.1L12 17l-5.4 2.9 1-6.1L3.2 9.5l6.1-.9z"/>',
 others:'<circle cx="12" cy="12" r="9"/><path d="M8 12h8M12 8v8"/>'};
function sparkPath(vals,w,h){
 const mxv=Math.max(...vals,1e-9),mnv=Math.min(...vals,0),r=mxv-mnv||1,n=vals.length;
 const pts=vals.map((v,i)=>[i/(n-1)*w,h-4-(v-mnv)/r*(h-14)]);
 let ln="M"+pts[0][0].toFixed(1)+" "+pts[0][1].toFixed(1);
 for(let i=1;i<n;i++){const [x0,y0]=pts[i-1],[x1,y1]=pts[i],cx_=(x0+x1)/2;ln+=" C"+cx_.toFixed(1)+" "+y0.toFixed(1)+" "+cx_.toFixed(1)+" "+y1.toFixed(1)+" "+x1.toFixed(1)+" "+y1.toFixed(1);}
 return {ln,fill:ln+" L"+w+" "+h+" L0 "+h+"Z"};
}
function dayVals(s,n){
 const [y,m,dd]=s.date.split("-").map(Number),out=[];
 for(let i=n-1;i>=0;i--){const dt=new Date(y,m-1,dd-i),k=dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0")+"-"+String(dt.getDate()).padStart(2,"0"),a=s.days[k];out.push(a?(GROSS?a.g:a.a):0);}
 return out;
}
function decorate(d){
 const s=d.sales,stamp=String(s.date)+(GROSS?"g":"n")+s.all.orders+"|"+s.today.orders;
 qa("#tiles .tile[data-mod]").forEach(tl=>{
  if(tl.dataset.dec===stamp&&tl.querySelector(".wm"))return;
  tl.dataset.dec=stamp;
  qa(".wm,.spark,.ringw",tl).forEach(x=>x.remove());
  const mod=tl.dataset.mod,ic=WM[mod];
  if(ic)tl.insertAdjacentHTML("afterbegin",'<svg class="wm" viewBox="0 0 24 24" aria-hidden="true">'+ic+'</svg>');
  let vals=null;
  if(mod==="today")vals=dayVals(s,14);
  else if(mod==="month")vals=dayVals(s,30);
  else if(mod==="all"){const ms=(s.months||[]).slice(-12);if(ms.length>2)vals=ms.map(m=>GROSS&&m.gross!=null?m.gross:(m.amount!=null?m.amount:m.a||0));}
  else if(mod==="avg")vals=dayVals(s,14);
  if(vals&&vals.length>2&&Math.max(...vals)>0){
   const w=240,h=110,p=sparkPath(vals,w,h);
   tl.insertAdjacentHTML("afterbegin",'<svg class="spark" viewBox="0 0 '+w+' '+h+'" preserveAspectRatio="none" aria-hidden="true"><path class="f" d="'+p.fill+'"/><path class="s" pathLength="1000" style="--len:1000" d="'+p.ln+'"/></svg>');
  }
  if(mod==="revrate"){
   const rv=d.reviews,tot=rv.positive+rv.negative,n=s.all.orders,pc=n?Math.min(100,tot*100/n):0,cl=2*Math.PI*26;
   tl.insertAdjacentHTML("afterbegin",'<div class="ringw" style="--cl:'+cl.toFixed(1)+';--co:'+(cl*(1-pc/100)).toFixed(1)+'"><svg viewBox="0 0 64 64"><circle class="t" cx="32" cy="32" r="26"/><circle class="p" cx="32" cy="32" r="26" style="stroke-dashoffset:'+(cl*(1-pc/100)).toFixed(1)+'"/></svg></div>');
  }
 });
}

// ---------- the 3D gem (brilliant cut), canvas 2D, drag + inertia ----------
const cv=$("gem"),g=cv.getContext("2d");
let GW=0,GH=0,GD=1;
function gsize(){const r=cv.getBoundingClientRect();GD=Math.min(devicePixelRatio||1,2);GW=Math.max(10,r.width);GH=Math.max(10,r.height);cv.width=Math.round(GW*GD);cv.height=Math.round(GH*GD);g.setTransform(GD,0,0,GD,0,0);}
const V=[],F=[];
(function build(){
 const TOP=.62,GIR=0,GB=-.06,CUL=-1.02;
 const tab=[],gt=[],gb=[],ring=[];
 for(let k=0;k<8;k++){const a=k*Math.PI/4;tab.push(V.push([Math.cos(a)*.56,TOP,Math.sin(a)*.56])-1);}
 for(let k=0;k<16;k++){const a=k*Math.PI/8;gt.push(V.push([Math.cos(a),GIR,Math.sin(a)])-1);}
 for(let k=0;k<16;k++){const a=k*Math.PI/8;gb.push(V.push([Math.cos(a)*.99,GB,Math.sin(a)*.99])-1);}
 for(let k=0;k<8;k++){const a=(k+.5)*Math.PI/4;ring.push(V.push([Math.cos(a)*.5,-.58,Math.sin(a)*.5])-1);}
 const cul=V.push([0,CUL,0])-1;
 const m=(i,n)=>((i%n)+n)%n;
 F.push({v:tab.slice(),t:"table"});
 for(let k=0;k<8;k++){
  F.push({v:[tab[k],gt[m(2*k-1,16)],gt[2*k],gt[m(2*k+1,16)]],t:"bezel"});
  F.push({v:[tab[k],tab[m(k+1,8)],gt[m(2*k+1,16)]],t:"star"});
 }
 for(let k=0;k<16;k++)F.push({v:[gt[k],gt[m(k+1,16)],gb[m(k+1,16)],gb[k]],t:"girdle"});
 for(let k=0;k<8;k++){
  F.push({v:[gb[2*k],gb[2*k+1],ring[k]],t:"pav"});
  F.push({v:[gb[2*k+1],gb[m(2*k+2,16)],ring[k]],t:"pav"});
  F.push({v:[ring[k],ring[m(k+1,8)],gb[m(2*k+2,16)]],t:"pav"});
  F.push({v:[cul,ring[k],ring[m(k+1,8)]],t:"pav"});
 }
})();
let ay=.6,ax=.38,vy=.006,vx=0,drag=false,lx=0,ly=0,pulse=0,gvis=true,gT=0,hoverX=0,hoverY=0;
function hex2rgb(h){h=h.trim();if(h[0]==="#"){if(h.length===4)h="#"+h[1]+h[1]+h[2]+h[2]+h[3]+h[3];const n=parseInt(h.slice(1),16);return [n>>16&255,n>>8&255,n&255];}
 const m=h.match(/\d+/g);return m?[+m[0],+m[1],+m[2]]:[56,189,248];}
let base=[56,189,248];
function gframe(t){
 g.clearRect(0,0,GW,GH);
 const cxm=GW/2,cym=GH/2+GH*.02,sc=Math.min(GW*.4,GH*.34)*(1+pulse*.12);
 if(!(gT++%30)){const a=getComputedStyle(document.body).getPropertyValue("--pc").trim();if(a)base=hex2rgb(a);}
 const gl=g.createRadialGradient(cxm,cym,sc*.1,cxm,cym,sc*1.9);
 gl.addColorStop(0,"rgba("+base+",.38)");gl.addColorStop(.5,"rgba("+base+",.10)");gl.addColorStop(1,"rgba("+base+",0)");
 g.fillStyle=gl;g.fillRect(0,0,GW,GH);
 g.save();g.translate(cxm,cym+sc*1.28);g.scale(1,.2);
 const sh=g.createRadialGradient(0,0,0,0,0,sc*1.1);sh.addColorStop(0,"rgba("+base+",.34)");sh.addColorStop(1,"rgba("+base+",0)");
 g.fillStyle=sh;g.beginPath();g.arc(0,0,sc*1.1,0,6.3);g.fill();g.restore();
 const bob=Math.sin(t/900)*sc*.04;
 const cA=Math.cos(ay),sA=Math.sin(ay),cX=Math.cos(ax),sX=Math.sin(ax);
 const P3=V.map(p=>{let x=p[0]*cA+p[2]*sA,z=-p[0]*sA+p[2]*cA,y=p[1];
  const y2=y*cX-z*sX,z2=y*sX+z*cX;
  const f=3.2/(3.2+z2*.55);return {x:cxm+x*sc*f,y:cym+bob-y2*sc*f,z:z2,X:x,Y:y2,Z:z2};});
 const L=[-.45,.8,.55],ll=Math.hypot(...L);L[0]/=ll;L[1]/=ll;L[2]/=ll;
 const out=F.map((f,fi)=>{
  const a=P3[f.v[0]],b=P3[f.v[1]],c=P3[f.v[2]];
  let nx=(b.Y-a.Y)*(c.Z-a.Z)-(b.Z-a.Z)*(c.Y-a.Y),ny=(b.Z-a.Z)*(c.X-a.X)-(b.X-a.X)*(c.Z-a.Z),nz=(b.X-a.X)*(c.Y-a.Y)-(b.Y-a.Y)*(c.X-a.X);
  const nl=Math.hypot(nx,ny,nz)||1;nx/=nl;ny/=nl;nz/=nl;
  let zc=0,cx2=0,cy2=0;f.v.forEach(i=>{zc+=P3[i].z;cx2+=P3[i].x;cy2+=P3[i].y;});zc/=f.v.length;cx2/=f.v.length;cy2/=f.v.length;
  const sx1=P3[f.v[1]].x-P3[f.v[0]].x,sy1=P3[f.v[1]].y-P3[f.v[0]].y,sx2=P3[f.v[2]].x-P3[f.v[0]].x,sy2=P3[f.v[2]].y-P3[f.v[0]].y;
  const front=(sx1*sy2-sy1*sx2)<0;
  return {f,fi,zc,cx2,cy2,front,nx:front?nx:-nx,ny:front?ny:-ny,nz:front?nz:-nz};
 });
 out.sort((p,q2)=>q2.zc-p.zc);
 const tt=t/1000;
 out.forEach(o=>{
  const d=Math.max(0,o.nx*L[0]+o.ny*L[1]+o.nz*L[2]);
  const rx=2*d*o.nz-L[2],spec=Math.pow(Math.max(0,rx),18)+Math.pow(Math.max(0,d),8)*.6;
  const ph=Math.sin(o.fi*1.7+ay*2.3+tt*.6)*.5+.5;
  const tint=[ [167,139,250],[103,232,249],[244,114,182] ][o.fi%3];
  const mix=.22*ph;
  let r=base[0]*(1-mix)+tint[0]*mix,gg=base[1]*(1-mix)+tint[1]*mix,b=base[2]*(1-mix)+tint[2]*mix;
  const br=.16+d*.72+(o.f.t==="table"?.1:0);
  r=r*br+255*spec*.85;gg=gg*br+255*spec*.85;b=b*br+255*spec*.85;
  const al=o.front?.9:.5;
  g.fillStyle="rgba("+Math.min(255,r|0)+","+Math.min(255,gg|0)+","+Math.min(255,b|0)+","+al+")";
  g.beginPath();o.f.v.forEach((i,k)=>{const p=P3[i];k?g.lineTo(p.x,p.y):g.moveTo(p.x,p.y);});g.closePath();g.fill();
  g.lineWidth=o.front?1:.6;g.strokeStyle="rgba(255,255,255,"+(o.front?.32:.12)+")";g.stroke();
  if(o.front&&spec>.55){const s2=sc*.07*Math.min(1.4,spec);g.save();g.translate(o.cx2,o.cy2);g.globalAlpha=Math.min(1,spec);g.fillStyle="#fff";g.shadowColor="rgb("+base+")";g.shadowBlur=14;
   g.beginPath();g.moveTo(0,-s2);g.lineTo(s2*.22,-s2*.22);g.lineTo(s2,0);g.lineTo(s2*.22,s2*.22);g.lineTo(0,s2);g.lineTo(-s2*.22,s2*.22);g.lineTo(-s2,0);g.lineTo(-s2*.22,-s2*.22);g.closePath();g.fill();g.restore();}
 });
}
let gRun=false;
function gloop(){
 if(gRun)return;gRun=true;
 const step=t=>{
  const r=ck.getBoundingClientRect();
  gvis=r.bottom>0&&r.top<innerHeight&&sec.classList.contains("on")&&!document.hidden;
  if(gvis){
   if(!drag){ay+=vy;ax+=(.38+hoverY*.25-ax)*.05+vx;vx*=.9;vy+=((FXo()?.0075:0)-vy)*.02;}
   pulse*=.93;gframe(t);}
  if(sec.classList.contains("on"))requestAnimationFrame(step);else gRun=false;};
 requestAnimationFrame(step);
}
cv.addEventListener("pointerdown",e=>{drag=true;lx=e.clientX;ly=e.clientY;cv.setPointerCapture(e.pointerId);cv.classList.add("drag");$("ckhint").style.opacity=0;});
cv.addEventListener("pointermove",e=>{
 const r=cv.getBoundingClientRect();hoverX=(e.clientX-r.left)/r.width-.5;hoverY=(e.clientY-r.top)/r.height-.5;
 if(!drag)return;const dx=e.clientX-lx,dy=e.clientY-ly;lx=e.clientX;ly=e.clientY;
 ay+=dx*.012;ax=Math.max(-.2,Math.min(1.1,ax+dy*.006));vy=dx*.012;});
const endDrag=()=>{drag=false;cv.classList.remove("drag");};
cv.addEventListener("pointerup",endDrag);cv.addEventListener("pointercancel",endDrag);
cv.addEventListener("dblclick",()=>{vy=.25;pulse=1;});
cv.addEventListener("pointerleave",()=>{hoverX=hoverY=0;});
new MutationObserver(()=>{if(sec.classList.contains("on"))gloop();}).observe(sec,{attributes:true,attributeFilter:["class"]});
if(window.ResizeObserver)new ResizeObserver(()=>{gsize();if(RM||!gRun)gframe(0);}).observe(cv);else addEventListener("resize",gsize);
gsize();gloop();
if(RM)gframe(0);
window.FX=Object.assign(window.FX||{},{gemBurst(){vy=.3;pulse=1;}});
if(window.__last)fill(window.__last);
})();

</script></body></html>"""


# ======================= command line =======================

def main():
    global DEMO, PREVIEW, PORT, HOST
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", nargs="?", default="run", choices=["run", "demo", "adduser"])
    ap.add_argument("name", nargs="?")
    ap.add_argument("--admin", action="store_true")
    ap.add_argument("--show", action="store_true", help="show the password while typing")
    ap.add_argument("--preview", action="store_true", help="run the new design next to the old dashboard (own port, no pushes, no backups, no programs)")
    ap.add_argument("--no-programs", action="store_true", help="do not start order_alerts, review_alerts, stock_board, stats_board and offer")
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
    if a.preview:
        PREVIEW = True
        a.no_programs = True
        if "DASHBOARD_PORT" not in os.environ:
            PORT = 8124
        if "DASHBOARD_HOST" not in os.environ:
            HOST = "127.0.0.1"
        print("PREVIEW of the new design - the real dashboard is not touched. No notifications, no backups, no programs.")
    if a.cmd == "demo":
        DEMO = True
        _demo_users["demo"] = {"name": "demo", "role": "admin", "hash": generate_password_hash("demodemo")}
        print("DEMO mode with fake data. Log in with  demo / demodemo")
    else:
        if not load_users():
            raise SystemExit("No users yet. Create the first one:  py dashboard.py adduser YOURNAME --admin")
        threading.Thread(target=poll_loop, daemon=True).start()
        if not PREVIEW:
            threading.Thread(target=_backup_loop, daemon=True).start()
        if not a.no_programs and os.getenv("MANAGE_PROGRAMS", "1") != "0":
            only = {x.strip() for x in os.getenv("PROGRAMS", "").split(",") if x.strip()}
            start_programs(only or None)
            print("Starting the other programs: " + ", ".join(n for n, _, _ in PROGRAM_LIST if not only or n in only))

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
