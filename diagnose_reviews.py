"""Tests the page-by-page reading of your orders (no names or keys are printed). Run: py diagnose_reviews.py"""
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"
total = {}
for state in ("Received", "Completed", "Delivered"):
    cursor, pages, orders, reviews, prev = None, 0, 0, 0, None
    print(f"\n=== {state} ===")
    while pages < 100:
        p = {"displayFilter": "DisplaySellingOrders", "orderState": state, "isAscendingDateOrder": "false", "pageSize": 50}
        if cursor:
            p["cursor"] = cursor
            p["pageDirection"] = "Next"
        try:
            d = c.request("GET", URL, params=p) or {}
        except Exception as e:
            print(f"  page {pages + 1}: ERROR {str(e)[:150]}")
            break
        res = d.get("results") or []
        ids = {o.get("id") for o in res}
        pages += 1
        if prev is not None and ids <= prev:
            print(f"  page {pages}: same orders as the page before -> the cursor is NOT understood")
            break
        prev = ids
        orders += len(res)
        reviews += sum(1 for o in res if o.get("review"))
        print(f"  page {pages}: {len(res)} orders, {sum(1 for o in res if o.get('review'))} with review, next cursor: {'yes' if d.get('nextPageCursor') else 'no'}")
        cursor = d.get("nextPageCursor")
        if not cursor or not res:
            break
    total[state] = reviews
    print(f"  -> {orders} orders, {reviews} reviews in {state}")
print(f"\nREVIEWS IN TOTAL (Received + Completed): {total['Received'] + total['Completed']}   (Eldorado shows 88)")
input("\nSend me this text/picture. Press Enter to close.")
