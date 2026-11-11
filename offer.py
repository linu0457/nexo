"""Adds accounts to an offer you ALREADY have on Eldorado (like "+ Add additional account").

Every key in keys.txt (one per line) is added as one extra account to your existing
offer (the one with "netflix" in the title). Login, Password and all other required
fields are filled with "Scroll Down"  The text of additional_info.txt is used as Additional info,
with {KEY} replaced by the key. The changes are REAL and visible on Eldorado immediately.

  py offer.py          -> preview only (nothing is changed)
  py offer.py test     -> add ONLY the first key
  py offer.py go       -> add ALL keys in keys.txt
  py offer.py auto     -> keep running and top up the stock by itself: it keeps the stock at
                          the target (default 100) by adding keys from keys.txt as they sell
  Options: --from netflix   (word in the title of the offer, default netflix)
           --target 100  --batch 1  --every 10   (auto mode: wanted stock, smallest top-up,
                                                  seconds between checks)

Keys that were added successfully are moved from keys.txt to keys_used.txt.
Add new keys to keys.txt at any time, also while auto mode is running.
In auto mode a Discord message is sent after every refill (and when it runs out of keys or stops).
Channel: REFILL_WEBHOOK_URL in .env, otherwise DISCORD_WEBHOOK_URL.
"""
import argparse
import json
import os
import socket
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests
from dotenv import load_dotenv

from eldorado_client import EldoradoClient

load_dotenv()
WEBHOOK = os.getenv("REFILL_WEBHOOK_URL") or os.getenv("DISCORD_WEBHOOK_URL")
SHOP_NAME = os.getenv("SHOP_NAME", "Eldorado Orders")
FOOTER_ICON_URL = os.getenv("FOOTER_ICON_URL")
GREEN, AMBER, RED = 0x2ECC71, 0xF39C12, 0xE74C3C
LOW_KEYS = 10  # the message turns orange when this few keys or fewer are left

KEYS_FILE = Path("keys.txt")
USED_FILE = Path("keys_used.txt")
INFO_FILE = Path("additional_info.txt")
PLACEHOLDER = "{KEY}"


def find_offer_id(client, word):
    for state in ("Active", "Paused"):
        page = 1
        while True:
            data = client.request("GET", "/api/flexibleOffers/me/search",
                                  params={"offerState": state, "category": "Account",
                                          "pageIndex": page, "pageSize": 50}) or {}
            for o in data.get("results") or []:
                if word.lower() in json.dumps(o).lower():
                    return o["id"]
            if page >= (data.get("totalPages") or 1) or page >= 50:
                break
            page += 1
    raise SystemExit(f"No account offer containing '{word}' found.")


INBOX_FILE = Path("keys_inbox.txt")  # keys uploaded on the website land here; only this script writes keys.txt


def absorb_inbox():
    """Moves keys uploaded from the dashboard (keys_inbox.txt) into keys.txt."""
    tmp = Path("keys_inbox.merging")
    try:
        if not tmp.exists():
            if not INBOX_FILE.exists():
                return
            INBOX_FILE.replace(tmp)  # atomic: the website starts a fresh inbox file from here
        new = [l.strip() for l in tmp.read_text(encoding="utf-8").splitlines() if l.strip()]
        if new:
            have = KEYS_FILE.read_text(encoding="utf-8") if KEYS_FILE.exists() else ""
            with KEYS_FILE.open("a", encoding="utf-8") as f:
                if have and not have.endswith("\n"):
                    f.write("\n")
                f.writelines(k + "\n" for k in new)
            print(f"Picked up {len(new)} keys uploaded from the website.", flush=True)
        tmp.unlink()
    except OSError as e:
        print("Could not read the website's key inbox yet:", type(e).__name__, flush=True)


def read_keys():
    absorb_inbox()
    if not KEYS_FILE.exists():
        raise SystemExit("keys.txt not found. Create it with one key per line.")
    lines = [l.strip() for l in KEYS_FILE.read_text(encoding="utf-8").splitlines()]
    return [l for l in lines if l and not l.startswith("#")]  # lines starting with # are notes


def read_info():
    text = INFO_FILE.read_text(encoding="utf-8").rstrip() if INFO_FILE.exists() else ""
    if PLACEHOLDER not in text:
        raise SystemExit(f"additional_info.txt is missing, or does not contain {PLACEHOLDER} where the key must go.")
    return text


PAUSE_ON_ERROR = 300   # seconds to wait when Eldorado refuses keys (limit per round)
FILL = "Scroll Down"   # shown in the username/password/email/MFA fields (the real key is in Additional info)


def account_body(info, key, fill=FILL):
    return {"structuredDetails": {
        "accountDetails": {"accountLogin": fill, "accountPassword": fill},
        "emailDetails": {"emailProviderUrl": fill, "emailLogin": fill, "emailPassword": fill},
        "mfaDetails": {"mfaLogin": fill, "mfaPassword": fill},
        "additionalInfo": info.replace(PLACEHOLDER, key),
    }}


def mark_used(done):
    rest = [l for l in KEYS_FILE.read_text(encoding="utf-8").splitlines() if l.strip() and l.strip() not in done]
    with USED_FILE.open("a", encoding="utf-8") as f:
        f.writelines(k + "\n" for k in done)
    KEYS_FILE.write_text("\n".join(rest) + ("\n" if rest else ""), encoding="utf-8")


def quantity(client, offer_id):
    return ((client.request("GET", f"/api/flexibleOffers/{offer_id}/private") or {}).get("offer") or {}).get("quantity")


def add_keys(client, offer_id, info, keys):
    """Adds the keys one by one. Returns (added_keys, error_code_or_None). Moves added keys to keys_used.txt."""
    done, error = [], None
    try:
        for key in keys:
            try:
                try:
                    client.request("POST", f"/api/flexibleOffersUser/me/offers/{offer_id}/secretDetails",
                                   json=account_body(info, key))
                except requests.HTTPError as e0:
                    # if Eldorado does not accept the text in some field, fall back to the old "." filler
                    if e0.response is not None and e0.response.status_code in (400, 422):
                        print(f"Eldorado did not accept '{FILL}' in the fields ({e0.response.status_code}), retrying with '.'")
                        client.request("POST", f"/api/flexibleOffersUser/me/offers/{offer_id}/secretDetails",
                                       json=account_body(info, key, "."))
                    else:
                        raise
            except requests.HTTPError as e:
                error = e.response.status_code if e.response is not None else "?"
                body = e.response.text[:600] if e.response is not None else ""
                print(f"Eldorado refused key {key}: {error} {body}")
                if error == 403:
                    print("403 means your API credentials are not allowed to add account details. "
                          "Send me this message.")
                break
            print(f"Added key {key}")
            done.append(key)
    finally:
        if done:
            mark_used(done)
            print(f"{len(done)} key(s) moved to {USED_FILE}.")
    return done, error


REFILL_LOG = Path("refill_log.json")


def log_refill(added, before, after, left):
    """Keeps a small history of refills, shown on the web dashboard."""
    try:
        try:
            log = json.loads(REFILL_LOG.read_text())
        except (OSError, ValueError):
            log = []
        log.append({"time": datetime.now(timezone.utc).isoformat(), "added": added,
                    "before": before, "after": after, "left": left})
        REFILL_LOG.write_text(json.dumps(log[-200:]))
    except OSError:
        pass


def notify(title, lines, color):
    """Sends a Discord embed (no-op without a webhook). Lines are (label, value) pairs; value None = plain text."""
    print(f"{title}: " + " | ".join(f"{l} {v}" if v is not None else l for l, v in lines), flush=True)
    if not WEBHOOK:
        return
    code = lambda v: str(v).replace("`", "'")
    desc = "\n".join(f"{l} `{code(v)}`" if v is not None else l for l, v in lines)
    footer = {"text": SHOP_NAME}
    if FOOTER_ICON_URL:
        footer["icon_url"] = FOOTER_ICON_URL
    embed = {"title": title, "description": desc, "color": color, "footer": footer,
             "timestamp": datetime.now(timezone.utc).isoformat()}
    try:
        r = requests.post(WEBHOOK, json={"embeds": [embed]}, timeout=10)
        if r.status_code >= 400:
            print("Discord error:", r.status_code)
    except requests.RequestException as e:
        print("Discord error:", type(e).__name__)


def only_one_copy(port=47234):
    global _LOCK
    _LOCK = socket.socket()
    try:
        _LOCK.bind(("127.0.0.1", port))
        _LOCK.listen(1)
    except OSError:
        raise SystemExit("offer.py auto is ALREADY running on this computer (another window?).")


_LOCK = None


def auto(client, offer_id, info, target, batch, every, offer_title="?"):
    """Tops the stock up to the target, in steps of `batch` keys."""
    only_one_copy()
    print(f"Auto mode: keeping the stock at {target}. When it is {batch} or more below, "
          f"I add keys from keys.txt. Checking every {every} seconds. Stop with Ctrl+C.")
    warned = False
    delay = every
    pause_after_error = False
    while True:
        try:
            stock = quantity(client, offer_id)
            if stock is None:
                print("Could not read the stock number. Retrying.")
            else:
                missing = target - stock
                wanted = (missing // batch) * batch if missing >= batch else 0
                if wanted > 0:
                    keys = read_keys()
                    take = min(wanted, (len(keys) // batch) * batch)
                    if take == 0:
                        if not warned:
                            print(f"Stock is {stock} but keys.txt has fewer than {batch} keys. "
                                  "Add more keys to keys.txt, I will pick them up.")
                            notify("Out of Keys", [
                                ("Item:", offer_title),
                                ("Stock:", f"{stock} / {target}"),
                                ("Keys left:", len(keys)),
                                ("**Add more keys to keys.txt, the refill continues by itself.**", None),
                            ], RED)
                            warned = True
                    else:
                        warned = False
                        print(f"Stock is {stock} (target {target}). Adding {take} key(s).")
                        done, error = add_keys(client, offer_id, info, keys[:take])
                        if done:
                            time.sleep(3)
                            after = quantity(client, offer_id)
                            left = len(read_keys())
                            if after is not None and after < stock + len(done):
                                notify("Auto Refill STOPPED", [
                                    ("Item:", offer_title),
                                    ("Added:", f"{len(done)} keys"),
                                    (f"Stock did not go up ({stock} -> {after}). Eldorado does not raise the "
                                     "stock by itself, so the refill was stopped.", None),
                                    ("Keys left:", left),
                                ], RED)
                                raise SystemExit(
                                    f"STOPPED: I added {len(done)} key(s), but the stock went {stock} -> {after}. "
                                    "Eldorado does not raise the stock number by itself, so I stop here "
                                    "instead of adding more keys by mistake. Send me this message.")
                            log_refill(len(done), stock, after, left)
                            notify("Stock Refilled", [
                                ("Item:", offer_title),
                                ("Added:", f"{len(done)} key{'s' if len(done) != 1 else ''}"),
                                ("Stock:", f"{stock} → {after if after is not None else '?'}"),
                                ("", None),
                                ("**Keys left in keys.txt:**", left),
                            ], RED if left == 0 else AMBER if left <= LOW_KEYS else GREEN)
                        if error == 403:
                            notify("Auto Refill STOPPED", [("No permission to add accounts (403).", None)], RED)
                            raise SystemExit("STOPPED: no permission to add accounts.")
                        if error is not None:
                            # Eldorado only lets a limited number of keys through at a time: wait 5 minutes,
                            # then the next round adds the keys that were not added (they are still in keys.txt)
                            print(f"Eldorado refused some keys ({error}). Pausing {PAUSE_ON_ERROR // 60} minutes, "
                                  f"then I add the remaining keys.", flush=True)
                            pause_after_error = True
                else:
                    warned = False
            delay = every
            if pause_after_error:
                delay = PAUSE_ON_ERROR
                pause_after_error = False
        except requests.HTTPError as e:
            print(f"API error {e.response.status_code if e.response is not None else '?'}. Retrying shortly.")
            delay = min(delay * 2, 60)
        except requests.RequestException as e:
            print(f"Network error ({type(e).__name__}). Retrying shortly.")
            delay = min(delay * 2, 60)
        time.sleep(delay)


def gendan(client, offer_id, info, n, skip=0):
    """Adds the latest N keys from keys_used.txt to the offer again (they were marked used but never really
    reached Eldorado). Keys Eldorado refuses stay in keys.txt; on a limit error it waits 5 minutes and goes on."""
    if not USED_FILE.exists():
        raise SystemExit("keys_used.txt not found - nothing to restore.")
    lines = USED_FILE.read_text(encoding="utf-8").splitlines()
    used = [l for l in lines if l.strip()]
    end = len(used) - skip
    pick = [l.strip() for l in used[max(0, end - n):max(0, end)]]
    if not pick:
        raise SystemExit("No keys to restore (keys_used.txt is too short).")
    if skip:
        print(f"Skipping the {skip} very latest used keys ({used[-skip].strip()} ... {used[-1].strip()}).")
    print(f"These {len(pick)} keys will be added to the offer again:")
    for k in pick:
        print("  ", k)
    if input("\nType JA and press Enter to add them: ").strip().lower() not in ("ja", "j", "yes", "y"):
        raise SystemExit("Cancelled - nothing was changed.")
    rest = used[:max(0, end - n)] + used[max(0, end):]
    USED_FILE.write_text("\n".join(rest) + ("\n" if rest else ""), encoding="utf-8")
    todo = list(pick)
    try:
        while todo:
            done, error = add_keys(client, offer_id, info, todo)   # moves the added keys back to keys_used.txt
            todo = [k for k in todo if k not in done]
            if not todo:
                break
            if error == 403:
                print("STOPPED: no permission to add accounts (403).")
                break
            print(f"Eldorado refused some keys ({error}). Pausing {PAUSE_ON_ERROR // 60} minutes, "
                  f"then I add the remaining {len(todo)}.", flush=True)
            time.sleep(PAUSE_ON_ERROR)
    finally:
        if todo:   # never lose a key: whatever was not added goes to the front of keys.txt
            have = KEYS_FILE.read_text(encoding="utf-8") if KEYS_FILE.exists() else ""
            KEYS_FILE.write_text("\n".join(todo) + "\n" + have, encoding="utf-8")
            print(f"{len(todo)} key(s) were NOT added and are back in keys.txt.")
    print(f"Done. {len(pick) - len(todo)} of {len(pick)} keys added. Check the stock number on Eldorado.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", nargs="?", default="preview", choices=["preview", "test", "go", "auto", "gendan"])
    ap.add_argument("--from", dest="word", default="netflix")
    ap.add_argument("--target", type=int, default=100)
    ap.add_argument("--batch", type=int, default=1)
    ap.add_argument("--every", type=int, default=10)
    ap.add_argument("--antal", type=int, default=25, help="gendan: how many used keys to add again")
    ap.add_argument("--spring", type=int, default=0, help="gendan: skip this many of the very latest used keys first")
    a = ap.parse_args()

    client = EldoradoClient()
    offer_id = find_offer_id(client, a.word)
    offer = (client.request("GET", f"/api/flexibleOffers/{offer_id}/private") or {}).get("offer") or {}
    info = read_info()

    if a.mode == "gendan":
        gendan(client, offer_id, info, a.antal, a.spring)
        return

    if a.mode == "auto":
        print(f"Offer    : {offer.get('offerTitle')}  (state: {offer.get('offerState')})")
        print(f"Stock now: {offer.get('quantity')}")
        try:
            auto(client, offer_id, info, a.target, a.batch, a.every, offer.get("offerTitle") or "?")
        except KeyboardInterrupt:
            print("\nStopped.")
        return

    keys = read_keys()
    if a.mode == "test":
        keys = keys[:1]
    if not keys:
        raise SystemExit("keys.txt is empty.")

    before = offer.get("quantity")
    print(f"Offer    : {offer.get('offerTitle')}  (state: {offer.get('offerState')})")
    print(f"Stock now: {before}")
    print(f"Adding   : {len(keys)} account(s)")

    if a.mode == "preview":
        print("\nPREVIEW ONLY - nothing was changed. Run  py offer.py test  to add the first key.")
        print(f"\nAdditional info of account 1 (key: {keys[0]}):\n{'-' * 30}\n{info.replace(PLACEHOLDER, keys[0])}\n{'-' * 30}")
        return

    done, _ = add_keys(client, offer_id, info, keys)
    if done:
        after = quantity(client, offer_id)
        print(f"Stock: {before} -> {after}")
        if before is not None and after is not None and after != before + len(done):
            print("NOTE: the stock number did not go up by the number of accounts added. "
                  "Check the offer on Eldorado and, if needed, change the quantity there.")


if __name__ == "__main__":
    main()
