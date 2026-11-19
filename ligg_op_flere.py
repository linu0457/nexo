"""Adds 25 keys to EACH of your Netflix offers with "12 months" or "1 year" in the title. Runs once and stops:
no auto refill. Keys come from keys.txt (first offer gets the first 25, the next offer the next 25, and so on).
Added keys move to keys_used.txt. Keys that could not be added go back into keys.txt.

  py ligg_op_flere.py               -> 25 keys to each offer
  py ligg_op_flere.py --antal 10    -> 10 keys to each
  py ligg_op_flere.py --kun-se      -> only look: lists the offers it found and what it would do (changes nothing)
  py ligg_op_flere.py --ord "12 month,1 year"   -> which words in the title to look for

The original 12 Months offer (the one with auto refill) is skipped. Skip more with --ignorer id1,id2

Additional info: offers with "1 year" in the title use info_1ar.txt if you have made that file, all others use
additional_info.txt (the same text as always, {KEY} = the key).
"""
import argparse
import time
from pathlib import Path

import offer as O
from eldorado_client import EldoradoClient
from ligg_op_nye import all_offers, give_back, read_all_keys, reserve, title_of

HERE = Path(__file__).resolve().parent
# the ORIGINAL 12 Months offer (it has its own auto refill) - never touched by this file
IGNORE_IDS = {"bf70b7ff-a242-4073-ad3a-08df2f3fdeae"}


def info_for(title):
    t = title.lower()
    f = HERE / "info_1ar.txt"
    if "1 year" in t and f.exists():
        return f.read_text(encoding="utf-8").rstrip(), "info_1ar.txt"
    f = HERE / "additional_info.txt"
    if not f.exists():
        raise SystemExit("additional_info.txt findes ikke i denne mappe.")
    return f.read_text(encoding="utf-8").rstrip(), "additional_info.txt"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--antal", type=int, default=25)
    ap.add_argument("--kun-se", action="store_true")
    ap.add_argument("--ord", default="12 month,1 year")
    ap.add_argument("--ignorer", default="", help="more offer ids to skip, separated by comma")
    a = ap.parse_args()
    words = [w.strip().lower() for w in a.ord.split(",") if w.strip()]
    skip = IGNORE_IDS | {x.strip() for x in a.ignorer.split(",") if x.strip()}

    client = EldoradoClient()
    offers = [(o, st) for o, st in all_offers(client)
              if o.get("id") not in skip and "netflix" in title_of(o).lower() and any(w in title_of(o).lower() for w in words)]
    if not offers:
        print("Fandt ingen Netflix-tilbud med", " eller ".join(words), "i titlen.")
        return
    plan = []
    for o, st in offers:
        info, src = info_for(title_of(o))
        if O.PLACEHOLDER not in info:
            print(f"{src} mangler {O.PLACEHOLDER} der hvor keyen skal staa.")
            return
        plan.append([o, st, info, src])

    n = a.antal
    keys = read_all_keys()
    chunks = [keys[i * n:(i + 1) * n] for i in range(len(plan))]
    print(f"\nPLAN  ({len(plan)} tilbud, {n} keys til hver, keys.txt har {len(keys)} keys)")
    for (o, st, info, src), take in zip(plan, chunks):
        ln = O.check_info_length(info, max(take, key=len) if take else "XXXX-XXXX-XXXX-XXXX-X")
        print(f"  [{st}] {title_of(o)}  (lager nu: {o.get('quantity')})  -> {len(take)} keys, tekst: {src} ({ln} af {O.MAX_INFO} tegn)")
    short = len(plan) * n - len(keys)
    if short > 0:
        print(f"\nBEMAERK: der mangler {short} keys i keys.txt til at fylde alle op. De sidste faar faerre eller ingen.")
    if a.kun_se:
        print("\nKUN SE - der er ikke aendret noget.")
        return
    if not keys:
        print("\nIngen keys i keys.txt.")
        return

    with O.keys_lock():   # the auto refills use keys.txt too - only one at a time takes keys
        keys = read_all_keys()
        chunks = [keys[i * n:(i + 1) * n] for i in range(len(plan))]
        reserve([k for c in chunks for k in c])
    total = 0
    try:
        for (o, st, info, src), todo in zip(plan, chunks):
            title = title_of(o)
            if not todo:
                print(f"\n{title}: ikke flere keys - springer over.")
                continue
            oid = o["id"]
            before = O.quantity(client, oid)
            print(f"\n=== {title}: laegger {len(todo)} keys op (lager foer: {before}) ===", flush=True)
            added = 0
            for attempt in range(6):
                done, error = O.add_keys(client, oid, info, todo)
                added += len(done)
                todo[:] = [k for k in todo if k not in done]
                if not todo:
                    break
                if error == 403:
                    print("STOPPET: ingen tilladelse (403).")
                    break
                print(f"Eldorado afviste nogle keys ({error}). Pause {O.PAUSE_ON_ERROR // 60} min, saa proever jeg de {len(todo)} resterende.", flush=True)
                time.sleep(O.PAUSE_ON_ERROR)
            after = O.quantity(client, oid)
            total += added
            print(f"{title}: {added} lagt op. Lager {before} -> {after}.", flush=True)
    finally:
        left = [k for c in chunks for k in c]
        give_back(left)
        if left:
            print(f"\n{len(left)} key(s) blev IKKE lagt op og ligger igen oeverst i keys.txt.")
    print(f"\nFaerdig. {total} keys lagt op i alt.")


if __name__ == "__main__":
    main()
