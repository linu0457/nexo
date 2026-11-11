"""Tries different ways of asking Eldorado for page 2 of your Completed orders (no names/keys printed).
Run: py diagnose_cursor.py"""
from urllib.parse import quote
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"
BASE = {"displayFilter": "DisplaySellingOrders", "orderState": "Completed", "isAscendingDateOrder": "false", "pageSize": 50}


def call(params):
    try:
        return c.request("GET", URL, params=params) or {}
    except Exception as e:
        return {"__error__": str(e)[:160]}


d1 = call(BASE)
ids1 = [o.get("id") for o in d1.get("results") or []]
cur = d1.get("nextPageCursor")
print("page 1:", len(ids1), "orders | nextPageCursor:", bool(cur))
if not cur:
    raise SystemExit("No cursor - there is only one page.")
qs = "&".join(f"{k}={v}" for k, v in BASE.items())
variants = {
    "cursor + pageDirection=Next": {**BASE, "cursor": cur, "pageDirection": "Next"},
    "cursor only": {**BASE, "cursor": cur},
    "Cursor + PageDirection": {**BASE, "Cursor": cur, "PageDirection": "Next"},
    "nextPageCursor": {**BASE, "nextPageCursor": cur},
    "pageCursor": {**BASE, "pageCursor": cur},
    "cursor, pageDirection=Forward": {**BASE, "cursor": cur, "pageDirection": "Forward"},
    "cursor, no pageSize": {k: v for k, v in {**BASE, "cursor": cur, "pageDirection": "Next"}.items() if k != "pageSize"},
    "cursor, no isAscendingDateOrder": {k: v for k, v in {**BASE, "cursor": cur, "pageDirection": "Next"}.items() if k != "isAscendingDateOrder"},
    "cursor with %20 (manual encoding)": qs + "&cursor=" + quote(cur, safe="") + "&pageDirection=Next",
}
for name, p in variants.items():
    d = call(p)
    if "__error__" in d:
        print(f"- {name}: ERROR {d['__error__']}")
        continue
    ids = [o.get("id") for o in d.get("results") or []]
    new = len(set(ids) - set(ids1))
    echo = {k: (bool(v) if "ursor" in k else v) for k, v in d.items() if k != "results" and not isinstance(v, (list, dict))}
    print(f"- {name}: {len(ids)} orders, {new} NEW | answer: {echo}")
input("\nSend me this text/picture. Press Enter to close.")
