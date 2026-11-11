"""Looks for the last reviews: other order states and further pages (no names/keys printed). Run: py diagnose_reviews2.py"""
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"


def page(state, cursor=None, direction="Previous", **extra):
    p = {"displayFilter": "DisplaySellingOrders", "orderState": state, "isAscendingDateOrder": "false", "pageSize": 50}
    if cursor:
        p["cursor"] = cursor
        p["pageDirection"] = direction
    p.update(extra)
    try:
        return c.request("GET", URL, params=p) or {}
    except Exception as e:
        return {"__error__": str(e)[:90]}


print("== 1. Other order states (first page) ==")
for st in ("Paid", "Delivered", "PendingReview", "Disputed", "Canceled", "Refunded", "Cancelled", "Completed", "Received"):
    d = page(st)
    if "__error__" in d:
        print(f"  {st}: error {d['__error__']}")
        continue
    r = d.get("results") or []
    print(f"  {st}: {len(r)} orders, {sum(1 for o in r if o.get('review'))} with review, next cursor: {bool(d.get('nextPageCursor'))}")

print("\n== 2. Completed: what does page 2 say about further pages? ==")
d1 = page("Completed")
ids1 = {o["id"] for o in d1.get("results") or []}
d2 = page("Completed", d1.get("nextPageCursor"))
ids2 = {o["id"] for o in d2.get("results") or []}
print("  page 2 answer:", {k: (bool(v) if "ursor" in k else v) for k, v in d2.items() if k != "results" and not isinstance(v, (list, dict))})
seen = ids1 | ids2
for name in ("previousPageCursor", "nextPageCursor"):
    cur = d2.get(name)
    if not cur:
        print(f"  {name}: none"); continue
    for direction in ("Previous", "Next"):
        d3 = page("Completed", cur, direction)
        ids3 = {o["id"] for o in d3.get("results") or []}
        print(f"  {name} + {direction}: {len(ids3)} orders, {len(ids3 - seen)} new, {sum(1 for o in d3.get('results') or [] if o['id'] not in seen and o.get('review'))} new reviews")

print("\n== 3. Oldest orders (ascending order) ==")
d = page("Completed", isAscendingDateOrder="true")
r = d.get("results") or []
print(f"  {len(r)} orders, {sum(1 for o in r if o.get('review'))} with review, new vs page1+2: {len({o['id'] for o in r} - seen)}")
print("  oldest order date:", min((o.get('createdDate', '') for o in r), default="?"), "| isHistorical:", sum(1 for o in r if o.get('isHistorical')))
input("\nSend me this text/picture. Press Enter to close.")
