#!/usr/bin/env python3
"""Probe assembler for MV transfer-size limits and L2BM->DRAM direct forms."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"

def try_asm(label, body):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=body.encode(), capture_output=True)
    out = p.stdout.decode(errors="replace"); err = p.stderr.decode(errors="replace")
    ok = p.returncode == 0
    first = next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(("OK   " if ok else "FAIL ") + f"{label:55s} words={out.count(chr(10)):3d} {first[:110]}")

if __name__ == "__main__":
    for n in [64, 512, 1024, 2048, 4096, 8192, 16384, 32768]:
        try_asm(f"mvp L2group->DRAM n{n}", f"j nop\nm mvp/n{n} $lc0@0.1 $d0@0\n")
    for n in [64, 512, 1024, 2048, 4096]:
        try_asm(f"mvd L2->PDM n{n}", f"j nop\nm mvd/n{n} $lc0 $p0@0\n")
    for n in [64, 512, 1024, 2048, 4096]:
        try_asm(f"mvp PDM->DRAM n{n}", f"j nop\nm mvp/n{n} $p0@0 $d0@0\n")
    # L1BM/L2BM with GRF1 source (is l2bmd source L1BM only?)
    try_asm("l2bmd $ls0 $lc0", "j l2bmd $ls0 $lc0\nj nop\nj nop\n")
    try_asm("l2bmd $lb0 $lc0", "j l2bmd $lb0 $lc0\nj nop\nj nop\n")
    try_asm("l1bmd $ls0 $lb0", "j l1bmd $ls0 $lb0\nj nop\nj nop\n")
    try_asm("l1bmd $aluf $lb0 + ALU", "j l1bmd $aluf $lb0; imm i\"1\" $r100\nj nop\n")
    try_asm("ALU write $s0 + L1B read $s0", "j l1bmd $s0 $lb0; imm i\"1\" $s0\nj nop\nj nop\nj nop\n")
