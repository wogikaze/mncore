#!/usr/bin/env python3
"""Probe how many PE expressions fit on one line and what the line costs in words."""
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"

CASES = [
    # (label, source)
    ("1 expr, plain", "lpassa $lm0v $ln0v"),
    ("1 expr, flat 4-cycle", "lpassa $lm[0,2,4,6] $ln[0,2,4,6]"),
    ("1 expr, adri v", "lpassa $lm0v $ln0v"),
    ("2 expr ALU+MAU", "lpassa $lm0v $ln0v;dvpassa $lm0v $ln8v"),
    ("2 expr ALU+L1BM gather", "lpassa $lm0v $ln0v;l1bmd $lr0v $lb0"),
    ("3 expr ALU+L1BM+L2BM", "lpassa $lm0v $ln0v;l1bmd $lr0v $lb0;l2bmd $lb0 $lc0"),
    ("4 expr + L1BM dist", "lpassa $lm0v $ln0v;l1bmd $lr0v $lb0;l2bmd $lb0 $lc0;l1bmd $lb192 $ls8v"),
    ("3 expr ALU+MAUcalc+MAUmwrite", "lpassa $lm0v $ln0v;dvpassa $lm8v $ln8v;gmwrite $ls0v $ly0"),
    ("4 expr ALU+MAUcalc+MAUmwrite+MAUmread", "lpassa $lm0v $ln0v;dvpassa $lm8v $ln8v;gmwrite $ls0v $ly0;dmread $lx $ls16v"),
    ("same group twice (ALU+ALU)", "lpassa $lm0v $ln0v;iadd $lm0 $ln0 $ln8"),
    ("same group twice (MAU calc)", "dvpassa $lm0v $ln0v;fvpassa $lm8v $ln8v"),
    ("imm alone", 'imm i"5" $r0'),
    ("imm + ALU on LM1", 'imm i"5" $r0;lpassa $ln0v $ln8v'),
    ("imm + ALU reading LM0 (forbidden)", 'imm i"5" $r0;lpassa $lm0v $ln0v'),
    ("imm + MAU only", 'imm i"5" $r0;dvpassa $lm0v $ln0v'),
    ("two imms one line", 'imm i"5" $r0;imm i"6" $s0'),
    ("nop + expr (forbidden)", "nop;lpassa $lm0v $ln0v"),
    ("nop + wait", "nop;wait"),
    ("MV sharing a PE line", "mvp/n64 $p0@0 $d0@0;lpassa $lm0v $ln0v"),
    ("two MV lines", "mvp/n64 $p0@0 $d0@0\nmvp/n64 $p64@0 $d64@0"),
    ("MV small vs large size", "mvp/n64 $p0@0 $d0@0\nmvp/n16384 $p0@0 $d0@0"),
    ("multi-output ALU expr", "lpassa $llm0v $ln0v $lls0v $omr1"),
]


def run(src: str) -> tuple[int, str, str]:
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(src + "\n").encode(), capture_output=True)
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")


for label, src in CASES:
    rc, out, err = run(src)
    if rc == 0:
        j = sum(1 for l in out.splitlines() if l[:1] == "j")
        m = sum(1 for l in out.splitlines() if l[:1] == "m")
        print(f"OK   {label:44s} j={j} m={m} words={j+m}")
    else:
        msg = next((l.strip() for l in err.splitlines() if l.strip()), "")
        print(f"FAIL {label:44s} {msg}")
