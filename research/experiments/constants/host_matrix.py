#!/usr/bin/env python3
"""For each ALU-only line of the 93-word answer, test whether a co-issued MAU
expression assembles (official assemble3, flat mode)."""
import subprocess
from pathlib import Path

ROOT = Path("/home/wogikaze/wgkz/mncore")
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
BASE = Path(__file__).resolve().parent / "base.vsm"

ALU_ONLY = [1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 20, 25, 26,
            30, 31, 42, 49, 56, 57, 58, 77, 78, 79, 80, 81, 82, 83, 84]

VARIANTS = {
    "GRF0->GRF0": "fvadd $r0 $r0 $r16",
    "GRF1->GRF0": "fvadd $s0 $s0 $r16",
    "GRF0->GRF1": "fvadd $r0 $r0 $s16",
    "GRF0->T":    "fvadd $r0 $r0 $t",
    "passa GRF0->GRF0": "fvpassa $r0 $r16",
}


def run(src):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=src.encode(),
                       capture_output=True)
    if p.returncode != 0:
        msg = next((l.strip() for l in p.stderr.decode().splitlines() if l.strip()), "")
        return None, msg
    return True, ""


lines = [l for l in BASE.read_text().splitlines() if l.split("#")[0].strip()]
assert len(lines) == 93

print("variant first (standalone legality):")
for name, expr in VARIANTS.items():
    ok, err = run(expr + "\n")
    print(f"  {name:20s} {'OK' if ok else 'FAIL ' + err}")

print("\nhost insertion matrix (rows=line, cols=variant):")
hdr = "line  " + " ".join(f"{n:18s}" for n in VARIANTS)
print(hdr)
for ln in ALU_ONLY:
    row = []
    for name, expr in VARIANTS.items():
        cand = list(lines)
        cand[ln - 1] = cand[ln - 1] + "; " + expr
        ok, err = run("\n".join(cand) + "\n")
        row.append("OK" if ok else "FAIL")
    print(f"{ln:4d}  " + " ".join(f"{r:18s}" for r in row))

print("\nreasons (last assembler message per failing cell, only for GRF0->GRF0):")
for ln in ALU_ONLY:
    cand = list(lines)
    cand[ln - 1] = cand[ln - 1] + "; " + VARIANTS["GRF0->GRF0"]
    ok, err = run("\n".join(cand) + "\n")
    if not ok:
        print(f"  L{ln:3d}: {err}")
