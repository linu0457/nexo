"""Adds 10 keys to each of the two new Netflix offers (2 Years and Lifetime) - exactly the way offer.py does it for
the 12-month offer, but with its own keys and its own Additional info text. No auto mode: it runs once and stops.

Files (all in this folder):
  keys_2ar.txt              one key per line for the 2 Years offer       (added keys move to keys_used_2ar.txt)
  keys_lifetime.txt         one key per line for the Lifetime offer      (added keys move to keys_used_lifetime.txt)
  additional_info_2ar.txt   Additional info for 2 Years      ({KEY} is replaced by the key)
  additional_info_lifetime.txt  Additional info for Lifetime

  py ligg_op_nye.py              -> add 10 keys to each offer
  py ligg_op_nye.py --antal 5    -> add 5 to each
  py ligg_op_nye.py --kun-se     -> only look: shows which offers it found and what it would add (changes nothing)
Options if the offers are not found by their title:  --ar2 "2 year"   --lifetime "lifetime"
"""
import argparse
import json
import time
from pathlib import Path

import requests

import offer as O
from eldorado_client import EldoradoClient

HERE = Path(__file__).resolve().parent
JOBS = [
    {"name": "2 Years", "words": "2 year", "keys": "keys_2ar.txt", "used": "keys_used_2ar.txt", "info": "additional_info_2ar.txt"},
    {"name": "Lifetime", "words": "lifetime", "keys": "keys_lifetime.txt", "used": "keys_used_lifetime.txt", "info": "additional_info_lifetime.txt"},
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


def read_keys(path):
    if not path.exists():
        path.write_text("# put one key per line below this line\n", encoding="utf-8")
        return []
    return [l.strip() for l in path.read_text(encoding="utf-8").splitlines() if l.strip() and not l.strip().startswith("#")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--antal", type=int, default=10)
    ap.add_argument("--kun-se", action="store_true")
    ap.add_argument("--ar2", default=None)
    ap.add_argument("--lifetime", default=None)
    a = ap.parse_args()
    if a.ar2:
        JOBS[0]["words"] = a.ar2
    if a.lifetime:
        JOBS[1]["words"] = a.lifetime

    # the Additional info files: made from your 12-month text the first time, then YOU change them
    base = HERE / "additional_info.txt"
    made = []
    for j in JOBS:
        p = HERE / j["info"]
        if not p.exists() and base.exists():
            p.write_text(base.read_text(encoding="utf-8"), encoding="utf-8")
            made.append(j["info"])
    if made:
        print("Jeg har lavet disse filer som kopi af additional_info.txt (12 maaneder):")
        for m in made:
            print("   ", m)
        print("\nAabn dem og ret teksten, saa den passer til de nye tilbud (fx 2 Years / Lifetime og garantien).")
        print("Koer derefter filen igen. Der er ikke lagt noget op endnu.")
        return

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
            print(f"Koer igen med fx  --{'ar2' if j is JOBS[0] else 'lifetime'} \"ord fra titlen\"")
            return
        o, st = hits[0]
        info_p = HERE / j["info"]
        if not info_p.exists():
            print(f"{j['info']} findes ikke. Opret den (med {O.PLACEHOLDER} der hvor keyen skal staa).")
            return
        info = info_p.read_text(encoding="utf-8").rstrip()
        if O.PLACEHOLDER not in info:
            print(f"{j['info']} mangler {O.PLACEHOLDER} der hvor keyen skal staa.")
            return
        keys = read_keys(HERE / j["keys"])
        plan.append((j, o, st, info, keys))

    print("\nPLAN")
    for j, o, st, info, keys in plan:
        take = keys[:a.antal]
        n = O.check_info_length(info, max(take, key=len) if take else "XXXX-XXXX-XXXX-XXXX-X")
        print(f"  {j['name']}: '{title_of(o)}' (status: {st}, lager nu: {o.get('quantity')})")
        print(f"     keys i {j['keys']}: {len(keys)}  ->  laegger {len(take)} op   (Additional info {n} af {O.MAX_INFO} tegn)")
    if a.kun_se:
        print("\nKUN SE - der er ikke aendret noget.")
        return

    for j, o, st, info, keys in plan:
        todo = keys[:a.antal]
        if not todo:
            print(f"\n{j['name']}: ingen keys i {j['keys']} - springer over.")
            continue
        O.KEYS_FILE = HERE / j["keys"]
        O.USED_FILE = HERE / j["used"]
        oid = o["id"]
        before = O.quantity(client, oid)
        print(f"\n=== {j['name']}: laegger {len(todo)} keys op (lager foer: {before}) ===", flush=True)
        added = 0
        for attempt in range(6):
            done, error = O.add_keys(client, oid, info, todo)
            added += len(done)
            todo = [k for k in todo if k not in done]
            if not todo:
                break
            if error == 403:
                print("STOPPET: ingen tilladelse (403).")
                break
            print(f"Eldorado afviste nogle keys ({error}). Pause {O.PAUSE_ON_ERROR // 60} min, saa proever jeg de {len(todo)} resterende.", flush=True)
            time.sleep(O.PAUSE_ON_ERROR)
        after = O.quantity(client, oid)
        print(f"{j['name']}: {added} lagt op. Lager {before} -> {after}. {len(todo)} key(s) ikke lagt op (ligger stadig i {j['keys']}).", flush=True)
    print("\nFaerdig.")


if __name__ == "__main__":
    main()
