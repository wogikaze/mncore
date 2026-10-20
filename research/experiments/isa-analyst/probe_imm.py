#!/usr/bin/env python3
"""imm economics: is a constant free when co-issued?"""
import subprocess
from pathlib import Path

ASM = Path(__file__).resolve().parents[3] / "judge/judge-py/mncore2_emuenv/assemble3"

CASES = [
 ("imm alone (ALU slot)", 'imm i"7" $r16'),
 ("imm alone, long literal", 'imm ui"0x4b000000" $t'),
 ("imm + MAU calc on GRF1 (no LM0)", 'imm i"7" $r16;fvpassa $ls0v $ls8v'),
 ("imm + L1BM gather from GRF0", 'imm i"7" $r16;l1bmd $lr0v $lb0'),
 ("imm + L2BM (no LM0)", 'imm i"7" $r16;l2bmd $lb0 $lc0'),
 ("imm + ALU (same group -> illegal)", 'imm i"7" $r16;lpassa $ln0v $ln8v'),
 ("imm + ALU reading LM0 -> illegal (bit sharing)", 'imm i"7" $r16;lpassa $lm0v $ln0v'),
 ("two imm on one line -> illegal", 'imm i"7" $r16;imm i"8" $s16'),
 ("imm on a line whose ALU slot is free: 2 words -> 1 word",
  'lpassa $lm0v $ln0v\nimm i"7" $r16'),
 ("same two lines merged", 'lpassa $lm0v $ln0v;imm i"7" $r16'),
 ("3 constants: 3 lines", 'imm i"7" $r16\nimm i"8" $r17\nimm i"9" $r18'),
 ("3 constants piggybacked on 3 MAU lines",
  'fvpassa $ls0v $ls24v;imm i"7" $r16\nfvpassa $ls32v $ls56v;imm i"8" $r17\nfvpassa $ls64v $ls88v;imm i"9" $r18'),
 ("mread + imm (d precision)", 'dmread $lx $lr16v;imm i"7" $s16'),
 ("dvpassa + dmread (both d)", 'dvpassa $ls16v $ls24v;dmread $lx $lr16v'),
 ("dmwrite + dmread (both d)", 'dmwrite $ls16v $ly0;dmread $lx $lr16v'),
 ("dvpassa + dmwrite (both d)", 'dvpassa $ls16v $ls24v;dmwrite $ls32v $ly0'),
 ("dmread + lpassa (ALU) + L1BM", 'dmread $lx $lr16v;lpassa $lm0v $ln0v;l1bmd $lr0v $lb0'),
]


def run(src: str):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(src + "\n").encode(), capture_output=True)
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")


for label, src in CASES:
    rc, out, err = run(src)
    if rc == 0:
        j = sum(1 for l in out.splitlines() if l[:1] == "j")
        m = sum(1 for l in out.splitlines() if l[:1] == "m")
        print(f"OK   {label:52s} j={j} m={m} words={j+m}")
    else:
        msg = next((l.strip() for l in err.splitlines() if l.strip()), "")
        print(f"FAIL {label:52s} {msg}")
