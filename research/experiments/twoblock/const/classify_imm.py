#!/usr/bin/env python3
"""Classify the 24 `imm` expressions of the 93-word answer.

For each imm expression: delete just that expression (keeping the rest of the
line; if the line becomes empty, drop the line) and measure
  words  (fbcheck: assembler word count)
  mismatches (native simulator vs the official testcase expectation)
An imm whose removal drops the word count by 1 occupies its own word.

Run: python3 const/classify_imm.py | tee const/classify_imm.log
"""
import re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
import importlib.util as _iu
_spec = _iu.spec_from_file_location("fbcheck", ROOT / "tools/fbcheck.py")
fb = _iu.module_from_spec(_spec)
sys.modules["fbcheck"] = fb
_spec.loader.exec_module(fb)

BASE = (ROOT / "problems/challenge/20.fizzbuzz/answer.vsm").read_text().rstrip("\n").split("\n")


def strip_imm(line):
    """Remove the imm expression from a line; return the rest (or '')."""
    parts = [p.strip() for p in line.split(";")]
    keep = [p for p in parts if not p.split()[0].split("/")[0] == "imm"]
    return "; ".join(keep)


def check(lines):
    text = "\n".join(lines) + "\n"
    r = fb.check(text)
    return r.words, r.mismatches, r.error


w0, m0, e0 = check(BASE)
print(f"baseline: words={w0} mismatches={m0} err={e0}")
print()
print(f"{'line':>4} {'imm expression':52s} {'words':>5} {'mismatch':>8}  own-word?")
rows = []
for i, line in enumerate(BASE, 1):
    if not any(p.strip().split()[0].split("/")[0] == "imm" for p in line.split(";")):
        continue
    rest = strip_imm(line)
    cand = list(BASE)
    if rest:
        cand[i - 1] = rest
    else:
        del cand[i - 1]
    words, mism, err = check(cand)
    imm = [p.strip() for p in line.split(";") if p.strip().split()[0].split("/")[0] == "imm"][0]
    own = words == w0 - 1
    rows.append((i, imm, words, mism, own, err))
    print(f"{i:4d} {imm:52s} {words:5d} {str(mism):>8}  {'OWN-WORD' if own else 'attached'} {err or ''}")
print()
print("own-word imms:", [r[0] for r in rows if r[4]])
print("attached imms:", [r[0] for r in rows if not r[4]])
# which deletions are *correct* (mismatches == 0)?
print("deletions with mismatches==0:", [(r[0], r[1]) for r in rows if r[3] == 0])
print("smallest mismatch counts:", sorted((r[3], r[0], r[1]) for r in rows if r[3] is not None)[:8])
