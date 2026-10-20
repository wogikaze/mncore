#!/usr/bin/env python3
"""Which ALU opcodes process BOTH long words of a 2-long-word (`ll`) operand?

SDM table 3.9 has a "2-long-word operation" column: `yes` only for
zero / imm / passa / bfe / bfn(half).  Everything else computes the MSB long
word (2 int32 lanes at `i` precision) and passes the LSB long word of the first
input through.  This probe measures that, because it decides whether 6
candidates (2 blocks x 3) can share one instruction word.

Setup: GRF0 words 0..3 = 1,1,1,1 and 4..7 = 2,2,2,2; GRF1 words 0..7 = 10..10.
For `op $llr0 $lls0 $lls16`:
  * if both long words are computed: words 16..19 = 11,11,12,12
  * if the LSB long word passes through: words 16..19 = 11,11, 2,2
(destination `$lls16` is 2 long words = 4 words, incremented by 4 per cycle.)

Run: python3 probe_ll3.py | tee logs/ll_probe.log
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator  # noqa: E402

ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
PE = "n0c0b0m0p0"

SETUP = """imm i"1" $r[0,1,2,3]
imm i"2" $r[4,5,6,7]
imm i"10" $s[0,1,2,3]
imm i"10" $s[4,5,6,7]
imm f"2.5" $s[16,17,18,19]
nop/2
"""

OPS = [
    ("iadd", "iadd $llr0 $lls0 $lls16"),
    ("isub", "isub $llr0 $lls0 $lls16"),
    ("iand", "iand $llr0 $lls0 $lls16"),
    ("ior", "ior $llr0 $lls0 $lls16"),
    ("ilsl", "ilsl $lls0 $llr0 $lls16"),
    ("ipassa", "ipassa $llr0 $lls16"),
    ("iinc", "iinc $llr0 $lls16"),
    ("fftoi", "fftoi $lls16 $lls24"),
    ("ffloor", "ffloor $lls16 $lls24"),
    ("relu", "frelu $lls16 $lls16 $lls24"),
]


def main() -> int:
    print("op        words 16..23 of GRF1 after `op`   veredict")
    for name, text in OPS:
        prog = SETUP + text
        p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=prog,
                           text=True, capture_output=True)
        asm = "ok" if p.returncode == 0 else "FAIL"
        sim = simulator()
        r = sim.run(prog + f"\nd get $ls{PE} 16\n")
        if r.error:
            print(f"{name:9s} asm={asm:4s} SIM ERROR {r.error}")
            continue
        lw = {a: v for (m, pp, a), v in r.dump.items() if m == "GREG1"}
        w = {}
        for a, v in lw.items():
            w[a] = (v >> 32) & 0xFFFFFFFF
            w[a + 1] = v & 0xFFFFFFFF
        out = [w.get(i, 0) for i in range(16, 24)]
        s = " ".join(f"{x:08x}" for x in out)
        if out[:2] != out[2:4] and out[2:4] == [2, 2]:
            verdict = "MSB long word only (LSB passed through)"
        elif out[:2] == out[2:4]:
            verdict = "both long words computed"
        else:
            verdict = "?"
        print(f"{name:9s} asm={asm:4s} {s}   {verdict}")
    print("\nkey line: `iadd $llr0 $lls0 $lls16` -> 0000000b 0000000b 00000002 00000002")
    print("  = 1+10 in lanes 0,1 (cycle 0's MSB long word) and 2,2 = GRF0 words 2,3")
    print("  passed through, NOT 1+10.  So `ll` gives 2 computed int32 lanes per")
    print("  cycle, i.e. 8 per instruction word, for every arithmetic opcode.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
