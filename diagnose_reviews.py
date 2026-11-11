"""Reads all your orders page by page and counts the reviews (no names/keys printed). Run: py diagnose_reviews.py"""
import time
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"


def page(state, cursor=None):
    p = {"displayFilter": "DisplaySellingOrders", "orderState": state, "isAscendingDateOrder": "false", "pageSize": 50}
    if cursor:
        p["cursor"] = cursor
        p["pageDirection"] = "Previous"
    return c.request("GET", URL, params=p) or {}


total = 0
for state in ("Received", "Completed"):
    d = page(state)
    seen = {o["id"] for o in d.get("results") or []}
    rev = sum(1 for o in d.get("results") or [] if o.get("review"))
    pages, tried, cands = 1, set(), [d.get("nextPageCursor")]
    print(f"\n=== {state} ===\n  page 1: {len(seen)} orders, {rev} reviews")
    while pages < 100:
        got = None
        for cur in cands:
            if not cur or cur in tried:
                continue
            tried.add(cur)
            d = page(state, cur)
            new = [o for o in d.get("results") or [] if o.get("id") and o["id"] not in seen]
            if new:
                got = new
                break
        if not got:
            break
        pages += 1
        seen |= {o["id"] for o in got}
        r = sum(1 for o in got if o.get("review"))
        rev += r
        print(f"  page {pages}: {len(got)} new orders, {r} reviews")
        cands = [d.get("previousPageCursor"), d.get("nextPageCursor")]
        time.sleep(0.25)
    print(f"  -> {len(seen)} orders, {rev} reviews in {state}")
    total += rev
print(f"\nREVIEWS IN TOTAL: {total}   (Eldorado shows 88)")
input("\nPress Enter to close.")
