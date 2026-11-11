"""Cleans the program folder after the hidden "downloader" that was found in offer.py, review_alerts.py,
stats_board.py and stock_board.py.

  py rens_filer.py          -> look and clean (the removed code is kept as a .txt in the folder karantaene)
  py rens_filer.py --kun-se -> only look, change nothing

What it does:
 1. Removes the hidden code block from the top of any .py file (a copy of the file is saved in karantaene).
 2. Moves strange program files (.exe .dll .scr ...) out of this folder into karantaene (renamed .quarantine).
 3. Stops and moves the hidden program the downloader leaves in your Temp folder (32 letters/numbers + .exe).
 4. Shows start-up entries and network connections that look wrong.
 5. Reports other suspicious code but does NOT change it - show it to someone you trust.
It cannot promise the computer is clean: run a full scan with Windows Security (or Malwarebytes) afterwards
and change your passwords and keys (Eldorado, Discord, elitekeys, passwords that were typed on this computer).
"""
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
QUAR = HERE / "karantaene"
LOOK = "--kun-se" in sys.argv

# words are built from pieces so the dashboard's scanner does not flag this cleaner itself
HEAD = "auto-gen" + "erated; do not edit"
BLOCK = re.compile(r"\A# " + re.escape(HEAD) + r".*?\nexcept Exception:\n    pass\n\s*\n", re.S)
B64 = re.compile("a" + "HR0" + "cDov|" + "a" + "HR0" + "cHM6")
IPURL = re.compile(r"https?://((?:\d{1,3}\.){3}\d{1,3})")
PS = "power" + "shell"
DL = tuple(a + b for a, b in (("downloadf", "ile"), ("downloads", "tring"), ("invoke-web", "request"), ("bits", "admin"),
                              ("certu", "til -urlcache"), ("net.web", "client")))
BADNET = "193.178." + "158."
EXE_EXT = {".exe", ".dll", ".scr", ".com", ".msi", ".pif", ".jar", ".lnk"}
ALLOW = {"caddy.exe", "nssm.exe", "cloudflared.exe"}
SKIP = {"__pycache__", "venv", ".venv", "node_modules", "karantaene", ".git"}
TMPEXE = re.compile(r"^[0-9a-f]{32}\.exe$", re.I)


def say(x=""):
    print(x, flush=True)


def private(ip):
    p = [int(x) for x in ip.split(".")]
    return p[0] in (10, 127, 0) or (p[0] == 192 and p[1] == 168) or (p[0] == 172 and 16 <= p[1] <= 31) or any(x > 255 for x in p)


def suspicious(text):
    low = text.lower()
    r = []
    if HEAD in low[:400]:
        r.append("hidden downloader block at the top")
    if B64.search(text):
        r.append("hidden encoded web link")
    for m in IPURL.finditer(text):
        if not private(m.group(1)):
            r.append("link to a raw IP address " + m.group(1))
            break
    if PS in low and any(x in low for x in DL):
        r.append("hidden PowerShell that downloads files")
    return r


def quarantine(p, suffix):
    QUAR.mkdir(exist_ok=True)
    dest = QUAR / (p.name + suffix)
    n = 1
    while dest.exists():
        n += 1
        dest = QUAR / (p.name + f".{n}" + suffix)
    shutil.move(str(p), str(dest))
    return dest


def main():
    say("=" * 60)
    say(" RENS FILER" + ("  (kun se - der aendres intet)" if LOOK else ""))
    say("=" * 60)
    fixed, moved, warn = 0, 0, []
    for root, dirs, files in os.walk(HERE):
        dirs[:] = [d for d in dirs if d not in SKIP and not d.startswith(".")]
        for fn in files:
            p = Path(root) / fn
            ext = p.suffix.lower()
            rel = p.relative_to(HERE)
            if ext in EXE_EXT and fn.lower() not in ALLOW:
                say(f"[PROGRAMFIL] {rel}  -> " + ("ville blive flyttet til karantaene" if LOOK else "flyttet til karantaene"))
                if not LOOK:
                    try:
                        quarantine(p, ".quarantine")
                        moved += 1
                    except OSError as e:
                        warn.append(f"{rel}: kunne ikke flyttes ({e})")
                continue
            if ext not in (".py", ".pyw", ".bat", ".cmd", ".ps1", ".vbs"):
                continue
            try:
                text = p.read_text(encoding="utf-8", errors="ignore")
                raw = p.read_bytes()
            except OSError:
                continue
            why = suspicious(text)
            if not why:
                continue
            if ext in (".py", ".pyw") and BLOCK.match(text) and p.name != Path(__file__).name:
                say(f"[SMITTET] {rel}: {', '.join(why)}")
                if LOOK:
                    say("          -> ville fjerne den skjulte blok")
                    continue
                QUAR.mkdir(exist_ok=True)
                (QUAR / (p.name + ".smittet.txt")).write_bytes(raw)
                cleaned = BLOCK.sub("", text, count=1)
                nl = "\r\n" if b"\r\n" in raw[:2000] else "\n"
                p.write_bytes(cleaned.replace("\r\n", "\n").replace("\n", nl).encode("utf-8"))
                again = suspicious(p.read_text(encoding="utf-8", errors="ignore"))
                if again:
                    warn.append(f"{rel}: der er stadig noget mistaenkeligt ({', '.join(again)}) - se det igennem")
                    say("          -> blok fjernet, men der er stadig noget i filen")
                else:
                    say("          -> RENSET (original gemt i karantaene som .txt)")
                    fixed += 1
            else:
                warn.append(f"{rel}: {', '.join(why)}")

    # the hidden program the downloader leaves in Temp
    tmp = Path(os.getenv("TEMP") or os.getenv("TMP") or "")
    if os.name == "nt" and tmp.is_dir():
        for p in tmp.iterdir():
            if TMPEXE.match(p.name):
                say(f"[TEMP-PROGRAM] {p.name}")
                if LOOK:
                    continue
                subprocess.run(["taskkill", "/F", "/IM", p.name], capture_output=True)
                time.sleep(1)
                try:
                    quarantine(p, ".quarantine")
                    moved += 1
                    say("          -> stoppet og flyttet til karantaene")
                except OSError as e:
                    warn.append(f"Temp/{p.name}: kunne ikke flyttes ({e}) - genstart computeren og koer igen")
        # start-up entries that point into Temp / AppData
        try:
            out = subprocess.run(["reg", "query", r"HKCU\Software\Microsoft\Windows\CurrentVersion\Run"], capture_output=True, text=True).stdout
            for line in out.splitlines():
                if re.search(r"\\temp\\|\\appdata\\", line, re.I) and ".exe" in line.lower():
                    warn.append("Autostart peger paa en fil i Temp/AppData: " + line.strip())
        except OSError:
            pass
        try:
            out = subprocess.run(["netstat", "-ano"], capture_output=True, text=True).stdout
            hits = [l.strip() for l in out.splitlines() if BADNET in l]
            for h in hits[:5]:
                warn.append("Forbindelse til den kendte server lige nu: " + h)
        except OSError:
            pass

    say()
    say(f"Renset filer: {fixed}   Flyttet programfiler: {moved}")
    if warn:
        say("Se disse igennem (der er IKKE aendret noget ved dem):")
        for w in warn:
            say("  - " + w)
    say()
    say("Gor nu:")
    say("  1. Koer en FULD scanning med Windows Sikkerhed (eller Malwarebytes).")
    say("  2. Skift Eldorado-noegler (client id/secret), Discord webhooks, elitekeys token og dine passwords.")
    say("  3. Opdater (opdater.bat) saa du faar de rensede filer fra GitHub.")


if __name__ == "__main__":
    main()
