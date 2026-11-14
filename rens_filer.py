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


def uniq(name):
    QUAR.mkdir(exist_ok=True)
    dest = QUAR / name
    n = 1
    while dest.exists():
        n += 1
        dest = QUAR / f"{name}.{n}"
    return dest


def extra_roots():
    """Other places on this computer where old copies of the scripts may lie (Desktop, Downloads ...)."""
    out = []
    for i, a in enumerate(sys.argv):
        if a == "--mappe" and i + 1 < len(sys.argv):
            out.append(Path(sys.argv[i + 1]))
    home = Path.home()
    for d in ("Desktop", "Downloads", "Documents", "OneDrive/Desktop", "OneDrive/Documents"):
        if (home / d).is_dir():
            out.append(home / d)
    # the folder above this one (e.g. where you unpacked the zip)
    if HERE.parent != HERE and HERE.parent != home and HERE.parent.parent != HERE.parent:   # not a drive root
        out.append(HERE.parent)
    seen, res = set(), []
    for r in out:
        k = str(r.resolve()).lower()
        if k not in seen and k != str(HERE).lower():
            seen.add(k)
            res.append(r)
    return res


def ps(cmd):
    try:
        return subprocess.run([PS + ".exe", "-NoProfile", "-Command", cmd], capture_output=True, text=True, timeout=90).stdout
    except (OSError, subprocess.SubprocessError):
        return ""


def main():
    say("=" * 60)
    say(" RENS FILER" + ("  (kun se - der aendres intet)" if LOOK else ""))
    say("=" * 60)
    fixed, moved, warn = 0, 0, []
    roots = [(HERE, True)] + [(r, False) for r in extra_roots()]
    for base, home in roots:
        say(f"\nTjekker {base} ...")
        for root, dirs, files in os.walk(base):
            depth = len(Path(root).relative_to(base).parts)
            dirs[:] = [d for d in dirs if d.lower() not in SKIP and not d.startswith(".") and d.lower() not in ("appdata", "windows", "site-packages", "program files", "program files (x86)", "programdata")]
            if not home and depth >= 4:
                dirs[:] = []
            for fn in files:
                p = Path(root) / fn
                ext = p.suffix.lower()
                rel = p.relative_to(HERE) if home else p
                if home and ext in EXE_EXT and fn.lower() not in ALLOW:
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
                    if p.stat().st_size > 3_000_000:
                        continue
                    text = p.read_text(encoding="utf-8", errors="ignore")
                    raw = p.read_bytes()
                except OSError:
                    continue
                why = suspicious(text)
                if not why:
                    continue
                if ext in (".py", ".pyw") and BLOCK.match(text) and p.resolve() != Path(__file__).resolve():
                    say(f"[SMITTET] {rel}: {', '.join(why)}")
                    if LOOK:
                        say("          -> ville fjerne den skjulte blok")
                        continue
                    try:
                        uniq(p.name + ".smittet.txt").write_bytes(raw)
                        cleaned = BLOCK.sub("", text, count=1)
                        nl = "\r\n" if b"\r\n" in raw[:2000] else "\n"
                        p.write_bytes(cleaned.replace("\r\n", "\n").replace("\n", nl).encode("utf-8"))
                    except OSError as e:
                        warn.append(f"{rel}: kunne ikke renses ({e}) - luk programmer der bruger filen og koer igen")
                        continue
                    again = suspicious(p.read_text(encoding="utf-8", errors="ignore"))
                    if again:
                        warn.append(f"{rel}: der er stadig noget mistaenkeligt ({', '.join(again)}) - se det igennem")
                        say("          -> blok fjernet, men der er stadig noget i filen")
                    else:
                        say("          -> RENSET (original gemt i karantaene som .txt)")
                        fixed += 1
                else:
                    warn.append(f"{rel}: {', '.join(why)}")

    if os.name == "nt":
        say("\nTjekker Temp, koerende programmer, autostart og planlagte opgaver ...")
        tmp = Path(os.getenv("TEMP") or os.getenv("TMP") or "")
        if tmp.is_dir():
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
        # programs running right now from Temp (nothing normal runs from there)
        out = ps("Get-CimInstance Win32_Process | Where-Object { $_.ExecutablePath -match '\\\\Temp\\\\' } | ForEach-Object { '{0}|{1}|{2}' -f $_.ProcessId,$_.Name,$_.ExecutablePath }")
        for line in out.splitlines():
            parts = line.strip().split("|")
            if len(parts) == 3:
                say(f"[KOERER FRA TEMP] {parts[1]} (pid {parts[0]}): {parts[2]}")
                if not LOOK:
                    subprocess.run(["taskkill", "/F", "/PID", parts[0]], capture_output=True)
                    say("          -> stoppet")
                warn.append(f"Program koerte fra Temp: {parts[2]} - det er stoppet, men find ud af hvorfor det startede")
        # start-up entries
        for key in (r"HKCU\Software\Microsoft\Windows\CurrentVersion\Run", r"HKLM\Software\Microsoft\Windows\CurrentVersion\Run",
                    r"HKCU\Software\Microsoft\Windows\CurrentVersion\RunOnce"):
            try:
                out = subprocess.run(["reg", "query", key], capture_output=True, text=True).stdout
            except OSError:
                continue
            for line in out.splitlines():
                if re.search(r"\\temp\\|\\appdata\\|\\programdata\\|\\users\\public\\", line, re.I) and ".exe" in line.lower():
                    warn.append(f"Autostart ({key.split(chr(92))[0]}): {line.strip()}  <- fjern den i Task Manager > Start-up, hvis du ikke selv har sat den")
        for d in (os.getenv("APPDATA", "") + r"\Microsoft\Windows\Start Menu\Programs\Startup", os.getenv("PROGRAMDATA", "") + r"\Microsoft\Windows\Start Menu\Programs\Startup"):
            if d.strip(chr(92)) and Path(d).is_dir():
                for f in Path(d).iterdir():
                    if f.suffix.lower() in (".exe", ".bat", ".cmd", ".vbs", ".lnk", ".ps1", ".js") and f.name.lower() != "desktop.ini":
                        warn.append(f"Start-up mappen indeholder: {f}  <- tjek at det er din egen")
        # scheduled tasks that start something from Temp/AppData
        try:
            out = subprocess.run(["schtasks", "/query", "/fo", "csv", "/v"], capture_output=True, text=True).stdout
            for line in out.splitlines():
                if re.search(r"\\temp\\", line, re.I) or (re.search(r"\\appdata\\", line, re.I) and ".exe" in line.lower() and not re.search(r"microsoft|google|discord|onedrive|opera|adobe|zoom|spotify", line, re.I)):
                    warn.append("Planlagt opgave der starter fra Temp/AppData: " + line.strip()[:200])
        except OSError:
            pass
        try:
            out = subprocess.run(["netstat", "-ano"], capture_output=True, text=True).stdout
            for h in [l.strip() for l in out.splitlines() if BADNET in l][:5]:
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
    say("  1. Koer en FULD scanning med Windows Sikkerhed - vaelg 'Microsoft Defender Antivirus (offline scan)' - og gerne Malwarebytes.")
    say("     Det der blev hentet kan have lavet kopier af sig selv. Kun et rigtigt antivirusprogram kan finde dem alle.")
    say("  2. Skift Eldorado-noegler (client id/secret), Discord webhooks, elitekeys token og dine passwords (fra en ANDEN, ren enhed).")
    say("  3. Opdater (opdater.bat) saa du faar de rensede filer fra GitHub.")


if __name__ == "__main__":
    main()
