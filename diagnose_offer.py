"""Looks at your Netflix offer and at Eldorado's seller API so I can build the "copy the offer" tool.
Changes NOTHING on Eldorado (only reads). Run:  py diagnose_offer.py   (or double-click diagnose_offer.bat)
Then send me what it prints (or the file diagnose_offer.txt)."""
import json
import sys

import requests

from eldorado_client import EldoradoClient
from offer import find_offer_id

OUT = []


def say(x=""):
    print(x, flush=True)
    OUT.append(str(x))


def deref(spec, node, depth=0):
    """Resolves $ref links so a request body can be read as plain fields."""
    if depth > 6 or not isinstance(node, (dict, list)):
        return node
    if isinstance(node, list):
        return [deref(spec, x, depth + 1) for x in node]
    if "$ref" in node:
        cur = spec
        for part in node["$ref"].lstrip("#/").split("/"):
            cur = cur.get(part, {}) if isinstance(cur, dict) else {}
        return deref(spec, cur, depth + 1)
    return {k: deref(spec, v, depth + 1) for k, v in node.items()}


def short(schema):
    if not isinstance(schema, dict):
        return schema
    props = schema.get("properties") or {}
    out = {}
    for k, v in props.items():
        t = v.get("type") or ("object" if v.get("properties") else "?")
        if v.get("enum"):
            t = "enum " + "/".join(map(str, v["enum"][:12]))
        out[k] = t if not v.get("properties") else short(v)
    if schema.get("required"):
        out["_required"] = schema["required"]
    return out


def main():
    client = EldoradoClient()
    word = sys.argv[1] if len(sys.argv) > 1 else "netflix,12 month"
    offer_id = find_offer_id(client, word)
    say(f"Offer id: {offer_id}")
    say("\n=== YOUR OFFER (what Eldorado returns) ===")
    for suffix in ("/private", ""):
        try:
            data = client.request("GET", f"/api/flexibleOffers/{offer_id}{suffix}")
            say(f"GET /api/flexibleOffers/{offer_id}{suffix}:")
            say(json.dumps(data, indent=1, ensure_ascii=False)[:9000])
            break
        except requests.HTTPError as e:
            say(f"GET {suffix or '(public)'} -> {e.response.status_code if e.response is not None else '?'}")

    say("\n=== ELDORADO SELLER API (swagger) ===")
    spec = None
    ua = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Safari/537.36",
          "Accept": "application/json,text/html,*/*", "Accept-Language": "en-US,en;q=0.9", "Referer": "https://www.eldorado.gg/swagger/seller/index.html"}
    paths = ["/swagger/seller/v1/swagger.json", "/swagger/v1/swagger.json", "/swagger/seller/swagger.json",
             "/swagger/swagger.json", "/swagger/seller/v1.0/swagger.json", "/swagger/Seller/v1/swagger.json"]
    try:   # the swagger page itself usually names the json file
        r = requests.get("https://www.eldorado.gg/swagger/seller/index.html", headers=ua, timeout=20)
        say(f"swagger index page -> {r.status_code}")
        import re
        for m in re.findall(r"""["'](/?[\w./-]*swagger[\w./-]*\.json)["']""", r.text):
            m = m if m.startswith("/") else "/swagger/seller/" + m
            if m not in paths:
                paths.insert(0, m)
    except requests.RequestException as e:
        say(f"swagger index page -> {type(e).__name__}")
    for path in paths:
        for hdr in ({**ua, **client._headers()}, ua):
            try:
                r = requests.get("https://www.eldorado.gg" + path, headers=hdr, timeout=20)
                if r.status_code == 200 and r.text.lstrip().startswith("{"):
                    spec = r.json()
                    say(f"Found spec: {path}")
                    break
                say(f"{path} -> {r.status_code}")
            except requests.RequestException as e:
                say(f"{path} -> {type(e).__name__}")
        if spec:
            break
    if spec:
        for p, methods in sorted((spec.get("paths") or {}).items()):
            if "ffer" not in p:
                continue
            for m, op in methods.items():
                if m.lower() not in ("post", "put", "patch"):
                    continue
                say(f"\n{m.upper()} {p}   {op.get('summary') or ''}")
                body = ((op.get("requestBody") or {}).get("content") or {})
                for ctype, c in body.items():
                    if "json" in ctype:
                        say(json.dumps(short(deref(spec, c.get("schema") or {})), indent=1, ensure_ascii=False)[:2500])
                        break
    say("\nDone. Nothing was changed on Eldorado.")
    try:
        open("diagnose_offer.txt", "w", encoding="utf-8").write("\n".join(OUT))
        say("(Also saved in diagnose_offer.txt)")
    except OSError:
        pass


if __name__ == "__main__":
    main()
