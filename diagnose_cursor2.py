"""Looks for the query parameter Eldorado uses to get older orders (no names/keys printed). Run: py diagnose_cursor2.py"""
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"
BASE = {"displayFilter": "DisplaySellingOrders", "orderState": "Completed", "isAscendingDateOrder": "false", "pageSize": 50}


def call(p):
    try:
        return c.request("GET", URL, params=p) or {}
    except Exception as e:
        return {"__error__": str(e)[:100]}


d1 = call(BASE)
res1 = d1.get("results") or []
ids1 = {o.get("id") for o in res1}
cur = d1.get("nextPageCursor")
print("page 1:", len(res1), "orders. Fields of an order:", sorted((res1[0] if res1 else {}).keys()))
last = res1[-1] if res1 else {}
dates = {k: v for k, v in last.items() if isinstance(v, str) and v[:2] == "20" and "-" in v[:8]}
print("dates on the oldest order of page 1:", dates)
hits = []


def probe(label, extra, drop=()):
    p = {k: v for k, v in {**BASE, **extra}.items() if k not in drop}
    d = call(p)
    if "__error__" in d:
        print(f"  {label}: error {d['__error__'][:70]}")
        return
    ids = {o.get("id") for o in d.get("results") or []}
    new = len(ids - ids1)
    echo = d.get("cursor")
    flag = "  <<<<<< WORKS" if (new or echo) else ""
    if new or echo:
        hits.append(label)
    print(f"  {label}: {len(ids)} orders, {new} new, echo={bool(echo)}{flag}")


print("\n-- names for the cursor --")
for n in ["cursor", "pageCursor", "paginationCursor", "startCursor", "after", "afterCursor", "pageToken", "continuationToken",
          "token", "nextCursor", "next", "nextPage", "lastId", "lastOrderId", "startAfter", "from", "pagingCursor", "cursorToken",
          "paging.cursor", "pagination.cursor", "request.cursor", "query.cursor", "filter.cursor", "pageRequest.cursor", "model.cursor"]:
    probe(n, {n: cur, "pageDirection": "Next"})
print("\n-- direction Previous with the cursor --")
probe("cursor + Previous", {"cursor": cur, "pageDirection": "Previous"})
d_dates = list(dates.values())
if d_dates:
    dv = d_dates[0]
    print("\n-- date filters (oldest date on page 1:", dv, ") --")
    for n in ["createdTo", "toDate", "dateTo", "endDate", "createdDateTo", "to", "until", "before", "beforeDate", "maxDate", "orderDateTo", "createdBefore", "createdDateBefore"]:
        probe(n, {n: dv})
print("\nWORKING:", hits or "none found")
input("\nSend me this text/picture. Press Enter to close.")
