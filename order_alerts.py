"""Order alerts: regularly checks for new orders and notifies you.

Checks the states Paid, Delivered, Received and Completed, so orders that are delivered
automatically (like accounts with instant delivery) are caught too.

READ ONLY. Does not change anything on your Eldorado account.
- Console: plain text
- Discord: embed (set DISCORD_WEBHOOK_URL in .env)
- Telegram: plain text (set TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID in .env)

Every message ends with total sales today and total sales all time.
Totals are kept in ledger.json (see the note in format_totals).

Run:  py order_alerts.py
Stop: Ctrl+C
"""
import json
import math
import os
import socket
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests
from dotenv import load_dotenv

from eldorado_client import EldoradoClient

load_dotenv()

LEDGER_FILE = Path("ledger.json")
POLL_SECONDS = int(os.getenv("POLL_SECONDS", "60"))
EMBED_COLOR = 0x2ECC71  # green bar on the left
SHOP_NAME = os.getenv("SHOP_NAME", "Eldorado Orders")  # footer text
FOOTER_ICON_URL = os.getenv("FOOTER_ICON_URL")  # optional small icon in the footer
# Eldorado takes a fee from every completed sale (rounded UP to the cent per order).
# 10 = standard fee for Accounts, 5 for Currency, 0 = show the full sale price. Change it in .env.
try:
    FEE_PERCENT = float(os.getenv("FEE_PERCENT", "10").replace(",", "."))
except ValueError:
    FEE_PERCENT = 10.0
TIMEZONE = os.getenv("TIMEZONE", "Europe/Copenhagen")  # "today" runs 00:00-24:00 in this timezone
try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo(TIMEZONE)
except Exception:  # missing tzdata (Windows) or unknown name
    TZ = None
    print(f"WARNING: timezone '{TIMEZONE}' not available, using this computer's clock. "
          "Fix on Windows with:  py -m pip install tzdata")
STATES = ["Paid", "Delivered", "Received", "Completed"]
# Orders in a state other than Paid are only announced if they are this fresh.
# Older unseen ones are just added to the totals, so you never get a flood of old orders.
ALERT_WINDOW_MINUTES = 120


# ---------- ledger (remembers orders + amounts for the totals) ----------

def order_time(o):
    raw = o.get("createdDate")
    if raw:
        try:
            dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt
        except ValueError:
            pass
    return datetime.now(timezone.utc)


def local_date(dt):
    """Calendar date of a moment in the chosen timezone (the day runs 00:00-24:00 there)."""
    return (dt.astimezone(TZ) if TZ else dt.astimezone()).date().isoformat()


def today_date():
    return local_date(datetime.now(timezone.utc))


def entry_date(entry):
    """Date of a ledger entry. Newer entries keep the exact time, so the day is always
    worked out in the chosen timezone; older entries only have a stored date."""
    ts = entry.get("ts")
    if ts:
        try:
            return local_date(datetime.fromisoformat(ts))
        except ValueError:
            pass
    return entry["date"]


def record(ledger, o):
    price = o.get("totalPrice") or {}
    ledger[o["id"]] = {
        "ts": order_time(o).astimezone(timezone.utc).isoformat(),
        "date": local_date(order_time(o)),
        "amount": float(price.get("amount") or 0),
        "currency": price.get("currency") or "USD",
        "buyer": o.get("buyerUsername") or "",
        "item": (o.get("orderOfferDetails") or {}).get("offerTitle") or "",
        "qty": o.get("purchaseQuantity") or 1,
    }


def fee_of(amount):
    """Eldorado's fee for one order, rounded up to the cent."""
    return math.ceil(round(float(amount) * FEE_PERCENT, 6)) / 100 if FEE_PERCENT > 0 else 0.0


def net_of(amount):
    """What you keep from one order after Eldorado's fee."""
    return round(float(amount) - fee_of(amount), 2)


def totals(ledger, only_date=None):
    """Returns {currency: (sum, order_count)}."""
    result = {}
    for entry in ledger.values():
        if only_date and entry_date(entry) != only_date:
            continue
        s, n = result.get(entry["currency"], (0.0, 0))
        result[entry["currency"]] = (s + net_of(entry["amount"]), n + 1)
    return result


def format_totals(t, sep="\n"):
    if not t:
        return "0.00 USD (0 orders)"
    lines = []
    for cur, (s, n) in sorted(t.items()):
        lines.append(f"{s:.2f} {cur} ({n} order{'s' if n != 1 else ''})")
    return sep.join(lines)


def load_ledger():
    if LEDGER_FILE.exists():
        try:
            return json.loads(LEDGER_FILE.read_text())
        except (ValueError, OSError):
            pass
    return None  # None = first run


def save_ledger(ledger):
    LEDGER_FILE.write_text(json.dumps(ledger))


# ---------- messages ----------

def build_message(o, ledger):
    """Returns (plain_text, discord_embed)."""
    details = o.get("orderOfferDetails") or {}
    price = o.get("totalPrice") or {}
    item = details.get("offerTitle") or details.get("gameCategoryTitle") or "?"
    quantity = o.get("purchaseQuantity", "?")
    price_text = f"{price.get('amount', '?')} {price.get('currency', '')}".strip()
    buyer = o.get("buyerUsername", "?")
    order_id = o.get("id")

    net_text = f"{net_of(price.get('amount') or 0):.2f} {price.get('currency', '')}".strip()
    after = " (after fees)" if FEE_PERCENT > 0 else ""
    today = today_date()
    today_text = format_totals(totals(ledger, today))
    all_text = format_totals(totals(ledger))

    text = (
        "New order on Eldorado!\n"
        f"Item: {item}\n"
        f"Quantity: {quantity}\n"
        f"Price: {price_text}\n"
        + (f"You get: {net_text} (after {FEE_PERCENT:g}% fee)\n" if FEE_PERCENT > 0 else "") +
        f"Buyer: {buyer}\n"
        f"Order ID: {order_id}\n"
        f"\nSold today{after}:\n{today_text}\n"
        f"\nSold all time{after}:\n{all_text}"
    )

    # Embed style: bold title, plain label + `code` value, bold label + plain value
    code = lambda v: str(v).replace("`", "'")
    today_line = format_totals(totals(ledger, today), sep=", ")
    all_line = format_totals(totals(ledger), sep=", ")
    description = (
        f"Item: `{code(item)}`\n"
        f"Quantity: `{code(quantity)}`\n"
        f"Price: `{code(price_text or '?')}`\n"
        + (f"You get: `{code(net_text)}` *(after {FEE_PERCENT:g}% fee)*\n" if FEE_PERCENT > 0 else "") +
        f"\n"
        f"**Buyer:** {buyer}\n"
        f"**Order ID:** `{code(order_id)}`\n"
        f"\n"
        f"**Sold today{after}:** `{today_line}`\n"
        f"**Sold all time{after}:** `{all_line}`"
    )
    footer = {"text": SHOP_NAME}
    if FOOTER_ICON_URL:
        footer["icon_url"] = FOOTER_ICON_URL

    embed = {
        "title": "New Order",
        "description": description,
        "color": EMBED_COLOR,
        "footer": footer,
        "timestamp": order_time(o).astimezone(timezone.utc).isoformat(),
    }
    return text, embed


def notify(text, embed=None):
    print(text + "\n" + "-" * 30, flush=True)

    token = os.getenv("TELEGRAM_BOT_TOKEN")
    chat_id = os.getenv("TELEGRAM_CHAT_ID")
    if token and chat_id:
        try:
            requests.post(
                f"https://api.telegram.org/bot{token}/sendMessage",
                json={"chat_id": chat_id, "text": text},
                timeout=10,
            )
        except requests.RequestException as e:
            print("Telegram error:", type(e).__name__)

    webhook = os.getenv("DISCORD_WEBHOOK_URL")
    if webhook:
        payload = {"embeds": [embed]} if embed else {"content": text}
        try:
            r = requests.post(webhook, json=payload, timeout=10)
            if r.status_code >= 400:
                print("Discord error:", r.status_code)
        except requests.RequestException as e:
            print("Discord error:", type(e).__name__)


# ---------- main loop ----------

_LOCK = None


def only_one_copy(port=47231):
    """Exits if this script is already running on this computer (prevents double messages)."""
    global _LOCK
    _LOCK = socket.socket()
    try:
        _LOCK.bind(("127.0.0.1", port))
        _LOCK.listen(1)
    except OSError:
        print("order_alerts.py is ALREADY running on this computer (another window?).")
        print("Close the other one first, then start this again.")
        sys.exit(1)


def fetch_orders(client):
    """Newest orders (first 50 per state) as a list of (state, order)."""
    found, seen = [], set()
    for state in STATES:
        data = client.request(
            "GET",
            "/api/v1/orders/me/seller/orders",
            params={
                "displayFilter": "DisplaySellingOrders",
                "orderState": state,
                "isAscendingDateOrder": "false",
                "pageSize": 50,
            },
        ) or {}
        for o in data.get("results") or []:
            if o.get("id") and o["id"] not in seen:
                seen.add(o["id"])
                found.append((state, o))
    return found


IGNORE_FILE = Path("ignore_orders.txt")


def load_ignored():
    """Order IDs you removed by hand (py order_alerts.py remove ID). They never count."""
    try:
        lines = IGNORE_FILE.read_text(encoding="utf-8").splitlines()
    except OSError:
        return set()
    return {l.split("#")[0].strip() for l in lines if l.split("#")[0].strip()}


def fetch_canceled_ids(client):
    """IDs of your newest cancelled orders (first 50). They must not count in the totals."""
    data = client.request(
        "GET",
        "/api/v1/orders/me/seller/orders",
        params={
            "displayFilter": "DisplaySellingOrders",
            "orderState": "Canceled",
            "isAscendingDateOrder": "false",
            "pageSize": 50,
        },
    ) or {}
    return {o["id"] for o in data.get("results") or [] if o.get("id")}


def is_fresh(o):
    age = datetime.now(timezone.utc) - order_time(o)
    return age.total_seconds() <= ALERT_WINDOW_MINUTES * 60


def check_once(client, ledger, send=notify):
    """Fetches orders, notifies about new ones, returns the updated ledger."""
    orders = fetch_orders(client)
    canceled = fetch_canceled_ids(client) | load_ignored()
    removed = [oid for oid in canceled if oid in ledger]
    for oid in removed:  # cancelled / refunded: take it out of the totals again
        del ledger[oid]
    if removed:
        print(f"Removed {len(removed)} cancelled order(s) from the totals.", flush=True)
    orders = [(st, o) for st, o in orders if o["id"] not in canceled]
    orders.sort(key=lambda so: order_time(so[1]))  # oldest first, so totals build up in order
    # Orders from before the first day in the ledger are ignored, so "all time"
    # keeps meaning "since the bot started" and not "everything in your history".
    floor = min((entry_date(e) for e in ledger.values()), default=None)
    for state, o in orders:
        if o["id"] in ledger:
            continue
        if floor and local_date(order_time(o)) < floor:
            continue
        record(ledger, o)  # record first, so the totals include this order
        if state == "Paid" or is_fresh(o):
            send(*build_message(o, ledger))
    return ledger


def cli(args):
    """py order_alerts.py list   |   py order_alerts.py remove ORDER_ID [ORDER_ID ...]"""
    ledger = load_ledger() or {}
    if args[0] == "list":
        rows = sorted(ledger.items(), key=lambda kv: kv[1]["ts"], reverse=True)[:int(args[1]) if len(args) > 1 else 20]
        for oid, e in rows:
            print(f"{oid}   {entry_date(e)}   {float(e['amount']):.2f} {e['currency']}")
        print(f"({len(ledger)} orders in the ledger. Remove one with:  py order_alerts.py remove <start of the id>)")
    elif args[0] == "remove" and len(args) > 1:
        for want in args[1:]:
            hits = [oid for oid in ledger if oid.lower().startswith(want.lower())]
            if len(hits) > 1:
                print(f"'{want}' matches {len(hits)} orders, type more of the id.")
                continue
            oid = hits[0] if hits else want
            with IGNORE_FILE.open("a", encoding="utf-8") as f:
                f.write(oid + "\n")
            if oid in ledger:
                e = ledger.pop(oid)
                print(f"Removed {oid} ({entry_date(e)}, {float(e['amount']):.2f} {e['currency']}).")
            else:
                print(f"{oid} was not in the ledger, but it is now ignored for good.")
        save_ledger(ledger)
        print("Done. A running order_alerts.py also picks this up by itself within a minute.")
    else:
        print(cli.__doc__)


def main():
    if len(sys.argv) > 1:
        return cli(sys.argv[1:])
    only_one_copy()
    client = EldoradoClient()
    ledger = load_ledger()

    if ledger is None:
        # First run: record existing orders without sending notifications
        ledger = {}
        for _, o in fetch_orders(client):
            record(ledger, o)
        save_ledger(ledger)
        print(f"Started. Recorded {len(ledger)} existing orders (no notifications for them).")
    else:
        print(f"Started. {len(ledger)} orders in ledger.")

    print(f"Checking every {POLL_SECONDS} seconds. Stop with Ctrl+C.")
    delay = POLL_SECONDS
    while True:
        try:
            before = json.dumps(ledger, sort_keys=True)
            ledger = check_once(client, ledger)
            if json.dumps(ledger, sort_keys=True) != before:
                save_ledger(ledger)
            delay = POLL_SECONDS
        except requests.HTTPError as e:
            code = e.response.status_code if e.response is not None else "?"
            print(f"API error {code}. Retrying shortly.")
            delay = min(delay * 2, 600)
        except requests.RequestException as e:
            print(f"Network error ({type(e).__name__}). Retrying shortly.")
            delay = min(delay * 2, 600)
        time.sleep(delay)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nStopped.")
