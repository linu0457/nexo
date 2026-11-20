"""Opretter nye offers som KOPI af et offer du allerede har: titel, beskrivelse, pris, billeder, leveringstid og
spil/kategori-valg. De nye offers bliver sat paa PAUSE med det samme - intet gaar live af sig selv.
Der lægges ingen keys i dem (brug ligg_op_flere.bat / ligg_op_nye.bat bagefter).

  py opret_offer.py                               -> viser dine offers med numre og spoerger hvilket du vil kopiere
  py opret_offer.py --fra "netflix,12 month"      -> kopierer det ene offer hvis titel har alle ordene (stopper hvis flere)
  py opret_offer.py --id <offer-id>               -> kopierer netop dette offer
  --antal 3        antal kopier (standard 1, max 20)
  --titel "..."    ny titel (standard: samme som originalen)
  --pris 7.7       ny pris pr. stk (standard: samme som originalen)
  --lager 1        antal paa lager der staar paa det nye offer (standard 1)
  --kun-se         vis kun hvad der ville blive sendt til Eldorado (opretter intet)
  --ja             spring "skriv ja"-spoergsmaalet over

Sikkerhed: den foerste kopi bliver oprettet, sat paa pause og LAEST TILBAGE fra Eldorado og sammenlignet med originalen.
Er der forskel (fx spil-valg eller billeder), stopper den, saa der ikke kommer flere forkerte.
Adressen kommer fra Eldorados egen API-beskrivelse: POST /api/flexibleOffers/account.
"""
import argparse
import json
import time
from pathlib import Path

import requests

from eldorado_client import EldoradoClient
from ligg_op_nye import all_offers, title_of

HERE = Path(__file__).resolve().parent
LOG = HERE / "opret_log.txt"
MAX_COPIES = 20


def money(m):
    m = m or {}
    return {"amount": m.get("amount"), "currency": m.get("currency")}


def image(i):
    i = i or {}
    return {k: i.get(k) for k in ("smallImage", "largeImage", "originalSizeImage")}


def build_body(src, title=None, price=None, stock=1):
    """The request for POST /api/flexibleOffers/account, built from the private view of an existing offer."""
    pricing = {
        "quantity": int(stock),
        "minQuantity": int(src.get("minQuantity") or 1),
        "pricePerUnit": money(src.get("pricePerUnit")),
    }
    if price is not None:
        pricing["pricePerUnit"]["amount"] = float(price)
    if src.get("volumeDiscounts"):
        pricing["volumeDiscounts"] = [{"quantity": v["quantity"], "percentage": v["percentage"]} for v in src["volumeDiscounts"]]
    details = {
        "offerTitle": title or src.get("offerTitle"),
        "description": src.get("description"),
        "guaranteedDeliveryTime": src.get("guaranteedDeliveryTime"),
        "mainOfferImage": image(src.get("mainOfferImage")),
        "offerImages": [image(i) for i in (src.get("offerImages") or [])],
        "pricing": pricing,
    }
    if src.get("hasOriginalEmail") is not None:
        details["hasOriginalEmail"] = src["hasOriginalEmail"]
    game = {"gameId": src.get("gameId"), "category": src.get("category") or "Account"}
    env = [e.get("id") for e in (src.get("tradeEnvironmentValues") or []) if e.get("id")]
    if env:
        game["tradeEnvironmentId"] = env[0]
    attrs = [{"id": a["id"]} for a in (src.get("offerAttributeIdValues") or []) if a.get("id")]
    if attrs:
        game["offerAttributes"] = attrs
    return {"details": details, "augmentedGame": game}


def differences(src, new, title=None, price=None):
    """What differs between the original and the new offer (as Eldorado reports it back). Empty list = identical."""
    out = []

    def cmp(name, a, b):
        if a != b:
            out.append(f"{name}: original={a!r} ny={b!r}")

    cmp("gameId", src.get("gameId"), new.get("gameId"))
    cmp("kategori", src.get("category"), new.get("category"))
    cmp("titel", title or src.get("offerTitle"), new.get("offerTitle"))
    cmp("beskrivelse", (src.get("description") or "").strip(), (new.get("description") or "").strip())
    cmp("leveringstid", src.get("guaranteedDeliveryTime"), new.get("guaranteedDeliveryTime"))
    cmp("pris", price if price is not None else (src.get("pricePerUnit") or {}).get("amount"),
        (new.get("pricePerUnit") or {}).get("amount"))
    cmp("valuta", (src.get("pricePerUnit") or {}).get("currency"), (new.get("pricePerUnit") or {}).get("currency"))
    ids = lambda o, k: sorted(str(x.get("id")) for x in (o.get(k) or []))
    cmp("valg (attributter)", ids(src, "offerAttributeIdValues"), ids(new, "offerAttributeIdValues"))
    cmp("miljoe", ids(src, "tradeEnvironmentValues"), ids(new, "tradeEnvironmentValues"))
    cmp("hovedbillede", bool((src.get("mainOfferImage") or {}).get("originalSizeImage") or (src.get("mainOfferImage") or {}).get("largeImage")),
        bool((new.get("mainOfferImage") or {}).get("originalSizeImage") or (new.get("mainOfferImage") or {}).get("largeImage")))
    cmp("antal billeder", len(src.get("offerImages") or []), len(new.get("offerImages") or []))
    return out


def err_text(e):
    r = getattr(e, "response", None)
    if r is None:
        return str(e)
    return f"{r.status_code} {r.text[:600]}"


def private(client, offer_id):
    return (client.request("GET", f"/api/flexibleOffers/{offer_id}/private") or {}).get("offer") or {}


def price_text(o):
    p = o.get("pricePerUnit") or {}
    return f"{p.get('amount')} {p.get('currency')}" if p.get("amount") is not None else "?"


def choose(offers, args):
    """Returns the offer id to copy."""
    if args.id:
        return args.id
    if args.fra:
        words = [w.strip().lower() for w in args.fra.split(",") if w.strip()]
        hits = [(o, st) for o, st in offers if all(w in title_of(o).lower() for w in words)]
        if len(hits) == 1:
            return hits[0][0]["id"]
        if not hits:
            raise SystemExit(f"STOPPET: intet offer med alle ordene '{args.fra}' i titlen.")
        raise SystemExit("STOPPET: flere offers passer paa '" + args.fra + "':\n  " +
                         "\n  ".join(f"{title_of(o)} ({st})" for o, st in hits) + "\nBrug flere ord, eller --id.")
    if not offers:
        raise SystemExit("Fandt ingen offers paa din konto.")
    print("\nDine offers:\n")
    for n, (o, st) in enumerate(offers, 1):
        print(f"  {n:>2}) {title_of(o)[:70]:<70} {price_text(o):>10}  {st}")
    while True:
        s = input("\nHvilket nummer vil du kopiere? ").strip()
        if s.isdigit() and 1 <= int(s) <= len(offers):
            return offers[int(s) - 1][0]["id"]
        print("Skriv et af numrene fra listen.")


def main(client=None, argv=None):
    ap = argparse.ArgumentParser(description="Opret nye offers som kopi af et eksisterende (sat paa pause).")
    ap.add_argument("--fra")
    ap.add_argument("--id")
    ap.add_argument("--antal", type=int)
    ap.add_argument("--titel")
    ap.add_argument("--pris", type=float)
    ap.add_argument("--lager", type=int, default=1)
    ap.add_argument("--kun-se", action="store_true")
    ap.add_argument("--ja", action="store_true")
    args = ap.parse_args(argv)

    client = client or EldoradoClient()
    offers = [] if args.id else all_offers(client)
    src_id = choose(offers, args)
    src = private(client, src_id)
    if not src.get("offerTitle"):
        raise SystemExit("STOPPET: kunne ikke laese originalen fra Eldorado.")

    n = args.antal
    if n is None:
        if args.fra or args.id or args.ja:
            n = 1
        else:
            s = input("Hvor mange kopier? (1) ").strip()
            n = int(s) if s.isdigit() else 1
    n = max(1, min(MAX_COPIES, n))
    body = build_body(src, args.titel, args.pris, args.lager)

    print(f"\nOriginal : {src.get('offerTitle')}  ({price_text(src)}, id {src_id})")
    print(f"Nye      : {n} stk. \"{body['details']['offerTitle']}\" til {body['details']['pricing']['pricePerUnit']['amount']} "
          f"{body['details']['pricing']['pricePerUnit']['currency']}, lager {args.lager}, sat paa PAUSE")
    if args.kun_se:
        print("\n--kun-se: dette ville blive sendt til Eldorado (POST /api/flexibleOffers/account):\n")
        print(json.dumps(body, indent=1, ensure_ascii=False))
        return 0
    if not args.ja and input("\nSkriv ja for at oprette: ").strip().lower() not in ("ja", "j", "yes", "y"):
        print("Afbrudt - intet er oprettet.")
        return 0

    made = []
    for i in range(1, n + 1):
        try:
            res = client.request("POST", "/api/flexibleOffers/account", json=body) or {}
        except requests.HTTPError as e:
            print(f"\n[{i}/{n}] Eldorado afviste oprettelsen: {err_text(e)}")
            print("Intet blev oprettet i denne omgang. Send mig teksten ovenfor.")
            break
        new_id = res.get("id") or (res.get("offer") or {}).get("id")
        if not new_id:
            print(f"\n[{i}/{n}] Eldorado svarede, men uden offer-id: {json.dumps(res)[:400]}")
            print("STOPPET. Tjek siden 'My offers' om der er kommet et nyt offer.")
            break
        made.append(new_id)
        with LOG.open("a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {new_id} kopi af {src_id}\n")
        try:
            client.request("PUT", f"/api/flexibleOffersUser/me/{new_id}/pause")
            paused = "sat paa pause"
        except requests.HTTPError as e:
            print(f"\n[{i}/{n}] !!! Offer {new_id} blev oprettet, men kunne IKKE saettes paa pause: {err_text(e)}")
            print("Saet det paa pause paa hjemmesiden nu. STOPPET - der oprettes ikke flere.")
            break
        new = private(client, new_id)
        diff = differences(src, new, args.titel, args.pris)
        print(f"[{i}/{n}] oprettet {new_id} ({paused}, tilstand: {new.get('offerState')})")
        if diff and i == 1:
            print("\nDen foerste kopi er IKKE helt ens med originalen:")
            for d in diff:
                print("   -", d)
            print("STOPPET efter foerste kopi, saa der ikke kommer flere forkerte. Tjek den paa pause paa hjemmesiden,")
            print("slet den hvis den er forkert, og send mig linjerne ovenfor.")
            break
        if diff:
            print("   forskelle:", "; ".join(diff))
    print(f"\nFaerdig: {len(made)} offer(s) oprettet paa pause. Id'er staar i opret_log.txt.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
