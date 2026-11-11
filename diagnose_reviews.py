"""Shows how Eldorado pages through your orders (no names, no keys are printed). Run: py diagnose_reviews.py"""
from eldorado_client import EldoradoClient

c = EldoradoClient()
URL = "/api/v1/orders/me/seller/orders"


def get(state, **extra):
    p = {"displayFilter": "DisplaySellingOrders", "orderState": state, "isAscendingDateOrder": "false", "pageSize": 50}
    p.update(extra)
    try:
        return c.request("GET", URL, params=p) or {}
    except Exception as e:
        return {"__error__": str(e)[:200]}


for state in ("Received", "Completed", "Delivered", "PendingReview"):
    print(f"\n=== {state} ===")
    d = get(state)
    if "__error__" in d:
        print("  error:", d["__error__"]); continue
    res = d.get("results") or []
    print("  results:", len(res), "| with review:", sum(1 for o in res if o.get("review")))
    print("  other fields in the answer:", {k: v for k, v in d.items() if k != "results" and not isinstance(v, (list, dict))})
    print("  list/dict fields:", [k for k, v in d.items() if k != "results" and isinstance(v, (list, dict))])
    first = {o.get("id") for o in res}
    if len(res) < 50:
        print("  (fewer than 50 -> no more pages in this state)"); continue
    for name in ("pageIndex", "pageNumber", "page", "pageNo", "currentPage", "offset", "skip"):
        for val in ((0, 1, 2, 50) if name in ("offset", "skip") else (0, 1, 2)):
            r = get(state, **{name: val})
            if "__error__" in r:
                print(f"  {name}={val}: error {r['__error__'][:80]}"); continue
            ids = {o.get("id") for o in (r.get("results") or [])}
            print(f"  {name}={val}: {len(ids)} orders, {len(ids - first)} new")
    r = get(state, pageSize=100)
    print("  pageSize=100 ->", len(r.get("results") or []), "orders")
input("\nDone. Take a picture / copy this and send it. Press Enter to close.")
