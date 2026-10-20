#!/usr/bin/env python3
"""Replace the T-chain (source lines 42-48) in the 93-word answer with a candidate.

Usage:
  python3 patch_chain.py OUT.vsm --body body.txt
  python3 patch_chain.py OUT.vsm --expr r18          # shorthand: T = r18
  python3 patch_chain.py OUT.vsm --expr zero         # T = 0

body.txt: VSM lines that replace lines 42-47.  Line 48's leading
`fvadd ... ; ` is always removed (its `imm f"0.01" $lr74` is kept).
"""
from __future__ import annotations

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "problems/challenge/20.fizzbuzz/answer.vsm"

EXPRS = {
    "r18": ["ipassa $lr18 $t"],
    "zero": ["zero $t"],
    "keep": None,
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--body")
    ap.add_argument("--expr")
    args = ap.parse_args()
    lines = SRC.read_text().splitlines()
    if args.expr:
        body = EXPRS[args.expr]
    else:
        body = Path(args.body).read_text().splitlines()
    assert lines[41].startswith("lsub $lr18 $ls132 $omr1"), lines[41]
    assert lines[47].startswith("fvadd $mauf $lr104 $t/$imr1; imm f\"0.01\""), lines[47]
    line48 = lines[47].split(";", 1)[1].strip()
    out = lines[:41] + body + [line48] + lines[48:]
    Path(args.out).write_text("\n".join(out) + "\n")
    print(f"wrote {args.out}: {len(out)} source lines")


if __name__ == "__main__":
    main()
