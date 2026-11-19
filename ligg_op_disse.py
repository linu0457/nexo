"""ONE-TIME file: adds 25 keys to exactly these two offers and then deletes itself:
   "Netflix 12-Months Subscription"   and   "Premium plan 4K | 12 months"
Keys come from keys.txt. Text: additional_info.txt.   py ligg_op_disse.py --kun-se  only looks (changes nothing).
"""
import os
import sys
from pathlib import Path

import ligg_op_flere as F
from eldorado_client import EldoradoClient
from ligg_op_nye import all_offers, title_of

HERE = Path(__file__).resolve().parent
DONE = HERE / "ligg_op_disse.done"
TARGETS = ("netflix 12 months subscription", "premium plan 4k | 12 months")


def main():
    look = "--kun-se" in sys.argv
    if DONE.exists():
        print("Denne fil er allerede koert een gang og goer ikke mere. (Slet ligg_op_disse.done for at koere den igen.)")
        return
    client = EldoradoClient()
    allo = all_offers(client)
    offers, problems = [], []
    for t in TARGETS:
        hits = [(o, st) for o, st in allo if F.norm(title_of(o)) == t or F.norm(title_of(o)).startswith(t)]
        if len(hits) != 1:
            problems.append(f"'{t}': fandt {len(hits)} tilbud")
        else:
            offers.append(hits[0])
    if problems:
        print("Jeg kan ikke finde praecis eet tilbud for hver titel:", "; ".join(problems))
        print("Dine tilbud:")
        for o, st in allo:
            print(f"   [{st}] {title_of(o)}")
        print("Der er ikke aendret noget.")
        return
    ok = F.run(client, offers, 25, look)
    if ok and not look:
        DONE.write_text("koert\n")
        for f in (Path(__file__), HERE / "ligg_op_disse.bat"):
            if f.name.endswith(".bat"):
                continue                      # the .bat deletes itself (see the file)
            try:
                os.remove(f)
            except OSError:
                pass
        print("\nDenne fil er nu koert og er slettet.")


if __name__ == "__main__":
    main()
