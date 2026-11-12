#!/usr/bin/env python3
"""Usage: chk.py <problem>  (reads candidates separated by lines '----' from stdin, prints results)"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools")); sys.path.insert(0, str(ROOT))
from golfcheck import Checker
_c = {}
def check(problem, text):
    if problem not in _c:
        _c[problem] = Checker(problem)
    return _c[problem].check(text)
if __name__ == "__main__":
    cands = sys.stdin.read().split("----\n")
    for t in cands:
        if t.strip():
            print(check(sys.argv[1], t), "|", " / ".join(l.strip() for l in t.strip().splitlines()))
