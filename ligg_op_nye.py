"""Adds 10 keys to the Netflix "2 Years" offer - exactly the way offer.py does it for the 12-month offer, but with its
own Additional info text. No auto mode: it runs once and stops.

The keys come from keys.txt (the same file as the 12-month restock). Added keys move to keys_used.txt, like always.

  py ligg_op_nye.py              -> add 10 keys
  py ligg_op_nye.py --antal 5    -> add 5
  py ligg_op_nye.py --kun-se     -> only look: shows which offer it found and what it would add (changes nothing)
Option if the offer is not found by its title:  --ar2 "2 year"
Additional info: the text is in this file (INFO_2AR). A file additional_info_2ar.txt next to the script overrides it.
"""
import argparse
import json
import time
from pathlib import Path

import requests

import offer as O
from eldorado_client import EldoradoClient

HERE = Path(__file__).resolve().parent
INFO_2AR = """🔴Your Key

{KEY}


🔵Netflix Key Tutorial

1: Go to https://elitekeys.site/s/nexoshop
2: Click the "Account Button"
3: Create an Account using your email and a password of your choice.
4: Go to the "Redeem" page and enter your key.
5: Go to the "Inventory"
6: Select your preferred device.
7: Press the link for your device
8: If the account stops working or it says payment issues press the get "Different Acc"
9: Just pick a profile, it doesn't matter. If all profiles are locked press get "Different Acc"
10: If the website won't load, use a VPN set to Switzerland (only for the website, not for Netflix). We are working on a fix.

🔵Netflix Account Rules

DO NOT change the password or email.
DO NOT change the subscription plan.
DO NOT create new profiles or edit existing profiles such as names.
ONLY ALLOWED CHANGE: You may change the language setting."""
JOBS = [
    {"name": "2 Years", "words": "2 year", "info_file": "additional_info_2ar.txt", "info": INFO_2AR},
]
STATES = ("Active", "Paused", "Draft", "PendingReview", "Inactive")


def all_offers(client):
    seen, out = set(), []
    for state in STATES:
        page = 1
        while page <= 20:
            try:
                data = client.request("GET", "/api/flexibleOffers/me/search",
                                      params={"offerState": state, "category": "Account", "pageIndex": page, "pageSize": 50}) or {}
            except requests.HTTPError:
                break   # that state name is not known to Eldorado
            for o in data.get("results") or []:
                if o.get("id") not in seen:
                    seen.add(o.get("id"))
                    out.append((o, state))
            if page >= (data.get("totalPages") or 1):
                break
            page += 1
    return out


def title_of(o):
    return o.get("offerTitle") or json.dumps(o)[:80]


def find(offers, words):
    hits = [(o, st) for o, st in offers
            if "netflix" in title_of(o).lower() and words.lower() in title_of(o).lower() and "12 month" not in title_of(o).lower()]
    return hits


def read_all_keys():
    O.absorb_inbox()   # keys uploaded on the website first
    if not O.KEYS_FILE.exists():
        return []
    return [l.strip() for l in O.KEYS_FILE.read_text(encoding="utf-8").splitlines() if l.strip() and not l.strip().startswith("#")]


def reserve(keys):
    """Takes these keys out of keys.txt right now, so the 12-month restock can never pick the same ones."""
    gone = set(keys)
    rest = [l for l in O.KEYS_FILE.read_text(encoding="utf-8").splitlines() if l.strip() and l.strip() not in gone]
    O.KEYS_FILE.write_text("\n".join(rest) + ("\n" if rest else ""), encoding="utf-8")


def give_back(keys):
    """Keys that were NOT added go back to the front of keys.txt."""
    if not keys:
        return
    have = O.KEYS_FILE.read_text(encoding="utf-8") if O.KEYS_FILE.exists() else ""
    O.KEYS_FILE.write_text("\n".join(keys) + "\n" + have, encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--antal", type=int, default=10)
    ap.add_argument("--kun-se", action="store_true")
    ap.add_argument("--ar2", default=None)
    a = ap.parse_args()
    if a.ar2:
        JOBS[0]["words"] = a.ar2

    client = EldoradoClient()
    offers = all_offers(client)
    plan = []
    for j in JOBS:
        hits = find(offers, j["words"])
        if len(hits) != 1:
            print(f"\nKunne ikke finde ENTEN praecis et tilbud til '{j['name']}' (soeger efter Netflix + '{j['words']}'): fandt {len(hits)}.")
            print("Dine Netflix-tilbud:")
            for o, st in offers:
                if "netflix" in title_of(o).lower():
                    print(f"   [{st}] {title_of(o)}")
            print('Koer igen med fx  --ar2 "ord fra titlen"')
            return
        o, st = hits[0]
        f = HERE / j["info_file"]
        info = (f.read_text(encoding="utf-8") if f.exists() else (j["info"] or "")).rstrip()
        if not info:
            print(f"Additional info til '{j['name']}' mangler i scriptet.")
            return
        if O.PLACEHOLDER not in info:
            print(f"Additional info til '{j['name']}' mangler {O.PLACEHOLDER} der hvor keyen skal staa.")
            return
        plan.append([j, o, st, info])

    keys = read_all_keys()
    n = a.antal
    chunks = [keys[i * n:(i + 1) * n] for i in range(len(plan))]
    print("\nPLAN  (keys.txt har " + str(len(keys)) + " keys)")
    for (j, o, st, info), take in zip(plan, chunks):
        ln = O.check_info_length(info, max(take, key=len) if take else "XXXX-XXXX-XXXX-XXXX-X")
        print(f"  {j['name']}: '{title_of(o)}' (status: {st}, lager nu: {o.get('quantity')})")
        print(f"     laegger {len(take)} keys op   (Additional info {ln} af {O.MAX_INFO} tegn)")
    if a.kun_se:
        print("\nKUN SE - der er ikke aendret noget.")
        return
    if not keys:
        print("\nIngen keys i keys.txt.")
        return

    reserve([k for c in chunks for k in c])   # out of keys.txt now; whatever is not added goes back
    try:
        for (j, o, st, info), todo in zip(plan, chunks):
            if not todo:
                print(f"\n{j['name']}: ikke flere keys i keys.txt - springer over.")
                continue
            oid = o["id"]
            before = O.quantity(client, oid)
            print(f"\n=== {j['name']}: laegger {len(todo)} keys op (lager foer: {before}) ===", flush=True)
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
            print(f"{j['name']}: {added} lagt op. Lager {before} -> {after}.", flush=True)
    finally:
        left = [k for c in chunks for k in c]
        give_back(left)
        if left:
            print(f"{len(left)} key(s) blev IKKE lagt op og ligger igen oeverst i keys.txt.")
    print("\nFaerdig.")


if __name__ == "__main__":
    main()
