#!/usr/bin/env python3
"""Exhaustive single-line deletion sweep over base.vsm (93 words).

For each line k: delete it, run fbasm (legality). If legal, run fbcheck.
Reports the winner(s) and, for failures, the assembler reason.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = HERE / "base.vsm"
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"

lines = [l for l in BASE.read_text().splitlines() if l.split("#")[0].strip()]


def asm(cand):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"],
                       input=("\n".join(cand) + "\n").encode(), capture_output=True)
    if p.returncode == 0:
        return True, ""
    err = [l for l in p.stderr.decode().strip().splitlines() if l.strip()]
    return False, err[-1] if err else "?"


def check(cand, tag):
    path = HERE / f"del_{tag}.vsm"
    path.write_text("\n".join(cand) + "\n")
    p = subprocess.run([sys.executable, str(ROOT / "tools" / "fbcheck.py"), str(path)],
                       capture_output=True, text=True)
    return (p.stdout + p.stderr).strip().splitlines()[-1]


results = []
for k in range(1, len(lines) + 1):
    cand = [l for i, l in enumerate(lines, 1) if i != k]
    ok, err = asm(cand)
    if ok:
        line = check(cand, k)
        print(f"L{k:3d} DELETE: ASM-OK  {line}   | {lines[k-1][:70]}")
    else:
        print(f"L{k:3d} DELETE: FAIL    {err[:110]}   | {lines[k-1][:60]}")
