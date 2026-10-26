"""Starts everything in ONE window:   py start_all.py

Runs order_alerts, review_alerts, stock_board, stats_board, offer (auto) and the dashboard side by side.
Every line of output gets a [name] in front, a program that crashes is started again after a few seconds,
and Ctrl+C stops them all. Put this file in the same folder as the other scripts.

    py start_all.py                 everything below
    py start_all.py dashboard orders   only the ones you name (names are the first word of each line below)
"""
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
# name, script, arguments. Delete a line (or put # in front) for something you do not use.
PROGRAMS = [
    ("orders",    "order_alerts.py",  []),
    ("reviews",   "review_alerts.py", []),
    ("stock",     "stock_board.py",   []),
    ("stats",     "stats_board.py",   []),
    ("offer",     "offer.py",         ["auto"]),
    ("dashboard", "dashboard.py",     []),
]
RESTART_AFTER = 5       # seconds before a crashed program is started again
STAGGER = 2             # seconds between starts, so they do not all hit Eldorado at once

stop = threading.Event()
procs = {}
print_lock = threading.Lock()


def say(name, line):
    with print_lock:
        print(f"[{name:<9}] {line}", flush=True)


def run(name, script, args):
    path = HERE / script
    if not path.exists():
        say(name, f"{script} not found here, skipping.")
        return
    env = dict(os.environ, PYTHONIOENCODING="utf-8", PYTHONUNBUFFERED="1")
    fast_crashes = 0
    while not stop.is_set():
        started = time.time()
        p = subprocess.Popen([sys.executable, "-u", str(path), *args], cwd=str(HERE), env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace")
        procs[name] = p
        say(name, "started")
        for line in p.stdout:
            say(name, line.rstrip())
        code = p.wait()
        if stop.is_set():
            break
        # crashing right away again and again: wait longer each time (max 2 minutes)
        fast_crashes = fast_crashes + 1 if time.time() - started < 30 else 0
        wait = min(RESTART_AFTER * (2 ** min(fast_crashes, 5)), 120)
        say(name, f"stopped (code {code}), starting again in {wait}s")
        stop.wait(wait)


def main():
    wanted = {a.lower() for a in sys.argv[1:]}
    chosen = [p for p in PROGRAMS if not wanted or p[0] in wanted]
    if not chosen:
        print("Unknown name. Choose from:", ", ".join(p[0] for p in PROGRAMS))
        return
    threads = []
    for name, script, args in chosen:
        t = threading.Thread(target=run, args=(name, script, args), daemon=True)
        t.start()
        threads.append(t)
        time.sleep(STAGGER)
    print("Everything is running. Press Ctrl+C to stop all.", flush=True)
    try:
        while any(t.is_alive() for t in threads):
            time.sleep(0.5)
    except KeyboardInterrupt:
        pass
    stop.set()
    print("Stopping...", flush=True)
    for p in procs.values():
        if p.poll() is None:
            p.terminate()
    deadline = time.time() + 8
    for p in procs.values():
        try:
            p.wait(max(0.1, deadline - time.time()))
        except subprocess.TimeoutExpired:
            p.kill()


if __name__ == "__main__":
    main()
