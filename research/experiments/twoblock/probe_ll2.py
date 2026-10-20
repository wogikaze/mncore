#!/usr/bin/env python3
"""Probe 2-long-word (`ll`) ALU operand support and lane semantics.

The question: does an `ll` operand give 4 int32 lanes per cycle (16 per
instruction word) instead of 2 (8)?

Method: fill GRF0 and GRF1 with known word patterns, run one op, dump 16 long
words (32 words) and print all 32 words per cycle.

Run: python3 probe_ll2.py
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator  # noqa: E402

ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
DUMPNAME = {"GREG1": "ls", "GREG0": "lr", "LM0": "lm"}


def official_asm(prog: str):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=prog,
                       text=True, capture_output=True)
    return p.returncode == 0, (p.stderr.strip().splitlines() or [""])[-1]


def run(prog: str, mem="GREG1", count=16, pe="n0c0b0m0p0"):
    sim = simulator()
    return sim.run(prog.rstrip("\n") + f"\nd get ${DUMPNAME[mem]}{pe} {count}\n")


def show(tag, prog, mem="GREG1", count=16):
    ok, err = official_asm(prog)
    r = run(prog, mem, count)
    if r.error:
        print(f"{tag}: SIM ERROR {r.part}:{r.line}: {r.error}   [{('ASM-OK' if ok else 'ASM-FAIL: ' + err)}]")
        return None
    lw = {a: v for (m, p, a), v in r.dump.items() if m == mem}
    words = {}
    for a, v in lw.items():
        words[a] = (v >> 32) & 0xFFFFFFFF
        words[a + 1] = v & 0xFFFFFFFF
    out = [words.get(i, 0) for i in range(0, 32)]
    asms = "ASM-OK" if ok else f"ASM-FAIL({err})"
    print(f"{tag}: {asms}")
    for c in range(0, 32, 8):
        print("    w%2d..%2d: %s" % (c, c + 7, " ".join(f"{w:08x}" for w in out[c:c+8])))
    return out


SETUP = """
imm i"1" $r[0,1,2,3]
imm i"2" $r[4,5,6,7]
imm i"100" $s[0,1,2,3]
imm i"200" $s[4,5,6,7]
"""


def main() -> int:
    print("=== setup: GRF0 w0-3=1, w4-7=2 ; GRF1 w0-3=100, w4-7=200")
    show("ipassa  $r0v $s0v  (word)", SETUP + "ipassa $r0v $s0v", count=4)
    show("ipassa  $llr0 $lls0 (2lw)", SETUP + "ipassa $llr0 $lls0", count=8)
    print()
    show("iadd $llr0 $lls0 $lls16", SETUP + "iadd $llr0 $lls0 $lls16", count=24)
    show("ilsl $lls0 $llr0 $lls16", SETUP + "ilsl $lls0 $llr0 $lls16", count=24)
    show("fftoi $lls0 $lls16", SETUP + "fftoi $lls0 $lls16", count=24)
    show("fvfma $llr0 $ls8 $lr0 $lls16", """
imm ui"0x4b000000" $r[0,1,2,3]
imm ui"0x4b000010" $r[4,5,6,7]
imm f"2.5" $s[8,8,8,8]
fvfma $llr0 $ls8 $lr0 $lls16
""", count=24)
    print("\n=== masking / write granularity with ll")
    show("ipassa $llr0 $lls16/1100", SETUP + "ipassa $llr0 $lls16/1100", count=16)
    print("\n=== ll destination of a word-source op")
    show("ipassa $r0v $lls16", SETUP + "ipassa $r0v $lls16", count=16)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
