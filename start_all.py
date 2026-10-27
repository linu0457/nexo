"""Starts everything:   py start_all.py   (the same as  py dashboard.py)

The dashboard now starts order_alerts, review_alerts, stock_board, stats_board and offer (auto) by itself,
watches them, and starts them again if they stop. You can see them on the Programs page.

    py dashboard.py --no-programs     only the website, without the other programs
Set PROGRAMS=orders,reviews in .env to start only some of them (orders, reviews, stock, stats, offer).
"""
import subprocess
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
try:
    sys.exit(subprocess.call([sys.executable, "-u", str(here / "dashboard.py"), *sys.argv[1:]], cwd=str(here)))
except KeyboardInterrupt:
    pass
