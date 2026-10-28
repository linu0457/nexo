"""Starts everything:   py start_all.py   (the same as  py dashboard.py, plus it can start itself again)

The dashboard starts order_alerts, review_alerts, stock_board, stats_board, offer (auto) and Caddy (https) by itself,
watches them, and starts them again if they stop. You can see them on the Programs page.
The Restart button on the Server page makes the dashboard stop with code 3, and this file then starts it again.

    py start_all.py --no-programs     only the website, without the other programs
Set PROGRAMS=orders,reviews in .env to start only some of them (orders, reviews, stock, stats, offer).
"""
import os
import subprocess
import sys
import time
from pathlib import Path

here = Path(__file__).resolve().parent
env = dict(os.environ, NEXO_SUPERVISED="1")
code = 0
try:
    while True:
        code = subprocess.call([sys.executable, "-u", str(here / "dashboard.py"), *sys.argv[1:]], cwd=str(here), env=env)
        if code != 3:
            break
        print("\n--- Restarting the dashboard ---\n", flush=True)
        time.sleep(2)
except KeyboardInterrupt:
    pass
sys.exit(code)
