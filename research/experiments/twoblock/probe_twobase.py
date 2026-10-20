#!/usr/bin/env python3
"""Probe: per-cycle T gives TWO block bases in one instruction word.

The 2-block canvas plan needs one ALU write instruction to serve both blocks,
i.e. the 4 cycles must carry two different T bases (block A in cycles 0/1,
block B in cycles 2/3).  T is per-cycle (T[C] = word 4C+1), so this should work.

Program:
  * LM0 word 16 = 10, word 18 = 200              (the two bases)
  * T <- fftoi($lmt[18,18,16,16])                (same lookup idiom as the 93-word answer, line 51)
  * ipassa $s[8,9,8,9] $mt[0,1,0,1]              (chars at T[C]+{0,1})
  * ipassa $lls[16..] $llm[...]                  (4 words per cycle with a 2-long-word write)
Then dump LM0.

Run: python3 probe_twobase.py
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


def run_and_dump(prog: str, words=256):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=prog,
                       text=True, capture_output=True)
    asm_ok = p.returncode == 0
    sim = simulator()
    r = sim.run(prog.rstrip("\n") + f"\nd get $lm{PE} {words}\nd get $lt{PE} 8\n")
    if r.error:
        print(f"SIM ERROR {r.part}:{r.line}: {r.error} (asm_ok={asm_ok})")
        if not asm_ok:
            print(p.stderr.strip()[-400:])
        return None
    lw = {a: v for (m, pp, a), v in r.dump.items() if m == "LM0" and pp == PE}
    tw = {a: v for (m, pp, a), v in r.dump.items() if m == "TREG" and pp == PE}
    canvas = {}
    for a, v in lw.items():
        canvas[a] = (v >> 32) & 0xFFFFFFFF
        canvas[a + 1] = v & 0xFFFFFFFF
    tvals = {}
    for a, v in tw.items():
        tvals[2 * a] = (v >> 32) & 0xFFFFFFFF
        tvals[2 * a + 1] = v & 0xFFFFFFFF
    print(f"  asm_ok={asm_ok}")
    print(f"  T words = {[hex(tvals.get(i, 0)) for i in range(16)]}")
    nz = [(i, canvas.get(i, 0)) for i in range(words) if canvas.get(i, 0)]
    print(f"  non-zero LM0 words: {[(i, hex(v), chr(v) if 32 <= v < 127 else '') for i, v in nz]}")
    return canvas


SETUP = """
imm f"10.0" $r[0,1,2,3]
imm f"200.0" $r[4,5,6,7]
ipassa $r[0,0,0,0] $m[16,16,16,16]
ipassa $r[4,4,4,4] $m[18,18,18,18]
nop/2
imm i"65" $s[8,8,8,8]
imm i"66" $s[9,9,9,9]
imm i"67" $s[10,10,10,10]
imm i"68" $s[11,11,11,11]
"""


def main() -> int:
    print("=== A: two T bases, word writes, 4 cycles = 4 (char,position) pairs")
    run_and_dump(SETUP + """
fftoi $lmt[18,18,16,16] $t
ipassa $s[8,9,10,11] $mt[0,1,0,1]
""")
    print("  expect 'A' at 10, 'B' at 11, 'C' at 200, 'D' at 201")

    print("\n=== B: same, 2-long-word write (4 words per cycle)")
    run_and_dump(SETUP + """
imm i"65" $r[0,1,2,3]
fftoi $lmt[18,18,16,16] $t
ipassa $llr0 $llm[0,4,0,4]
""")
    print("  expect 4 chars at 10..13 and 4 at 200..203 (ll writes 4 words/cycle)")

    print("\n=== C: one line serves BOTH blocks (2 cycles each) with ll writes")
    run_and_dump(SETUP + """
imm i"65" $r[0,1,2,3]
imm i"66" $r[4,5,6,7]
fftoi $lmt[18,18,16,16] $t
ipassa $llr0 $llm[0,0,0,0]
ipassa $llr4 $llm[0,0,0,0]
""")
    print("  expect 'A'x4 at 10..13 and 'B'x4 at 200..203 from ONE word")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
