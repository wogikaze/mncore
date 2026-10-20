#!/usr/bin/env python3
"""Assembler probes for the delivery bound: transfer-size limit and hazard gaps.

Run from the repository root:
    python3 research/preliminary/fizzbuzz-delivery/probe_isa.py
Every probe is a small VSM fragment assembled with the official
judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat.
The exit status of assemble3 is the authority on legality; the hazard checker
is enabled by default.
"""
from __future__ import annotations
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"


def probe(label: str, body: str) -> bool:
    p = subprocess.run(
        [str(ASM), "--instruction-mode", "flat"],
        input=body.encode(), capture_output=True,
    )
    err = p.stderr.decode(errors="replace")
    ok = p.returncode == 0
    first = next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(f"{'OK  ' if ok else 'FAIL'} {label:62s} {first[:96]}")
    return ok


def main() -> int:
    print("== transfer-size field limit (n is in long words; 8 bytes each) ==")
    for n in (4096, 16384, 32768):
        probe(f"mvp L2BM->DRAM single group n{n}", f"nop\nmvp/n{n} $lc0@0.1 $d0@0\n")
    for n in (4096, 16384, 32768):
        probe(f"mvp PDM->DRAM n{n}", f"nop\nmvp/n{n} $p0@0 $d0@0\n")
    for n in (4096, 16384, 32768):
        probe(f"mvr2dfadd L2BM->DRAM per group n{n}", f"nop\nmvr2dfadd/n{n} $lc0 $d0\n")
    for n in (4096, 16384, 32768):
        probe(f"mvr4dfadd L2BM->DRAM per group n{n}", f"nop\nmvr4dfadd/n{n} $lc0 $d0\n")
    for n in (4096, 16384, 32768):
        probe(f"mvrdfadd L2BM->DRAM per group n{n}", f"nop\nmvrdfadd/n{n} $lc0 $d0\n")

    print("\n== PDM->DRAM forms: single-individual copy vs distribution ==")
    probe("mvp (copy) PDM->DRAM n16384", "nop\nmvp/n16384 $p0@0 $d0@0\n")
    probe("mvd (distribution) PDM->DRAM n16384", "nop\nmvd/n16384 $p0@0 $d0\n")
    probe("mvd (distribution) with dst group suffix [must FAIL]",
          "nop\nmvd/n64 $p0@0 $d0@0\n")

    print("\n== capacity of one L1BM->L2BM word (l2bmd) ==")
    # The FizzBuzz output is 4096 long words; one l2bmd writes 2048.
    print("   SDM 3.6.7.8: 64 words/cycle * 4 cycles * 8 L2BM = 2048 long words/word")
    print("   measured: deleting one of the two l2bmd from the Accepted 93-word")
    print("   solution gives exactly 2048 mismatched DRAM words (see verify.sh)")

    print("\n== hazard gaps (same address) ==")
    # L2BM write -> MV read: needs one intervening word.
    probe("l2bmd, mvd/n512 (0 nop)  [must FAIL]",
          "l2bmd $lb0 $lc0\nl2bmd $lb32 $lc256\nmvd/n512 $lc0 $p0@0\n")
    probe("l2bmd, nop, mvd/n512 (1 nop)  [must OK]",
          "l2bmd $lb0 $lc0\nl2bmd $lb32 $lc256\nnop\nmvd/n512 $lc0 $p0@0\n")
    # PE->L1BM write -> L1BM->L2BM read: needs two intervening words.
    probe("l1bmd, l2bmd (0 nop)  [must FAIL]",
          "l1bmd $ls0 $lb0\nl2bmd $lb0 $lc0\n")
    probe("l1bmd, nop, l2bmd (1 nop)  [must FAIL]",
          "l1bmd $ls0 $lb0\nnop\nl2bmd $lb0 $lc0\n")
    probe("l1bmd, nop, nop, l2bmd (2 nop)  [must OK]",
          "l1bmd $ls0 $lb0\nnop\nnop\nl2bmd $lb0 $lc0\n")
    # normal ALU producer -> l1bmd reading the same GRF1 address: one nop.
    probe("ipassa->s0, l1bmd s0 (0 nop)  [must FAIL]",
          "ipassa $t $ls0/1100\nl1bmd $ls0 $lb0\n")
    probe("ipassa->s0, nop, l1bmd s0 (1 nop)  [must OK]",
          "ipassa $t $ls0/1100\nnop\nl1bmd $ls0 $lb0\n")
    # PDM write -> PDM read (mvd then mvp) needs no gap.
    probe("mvd, mvp (0 nop)  [must OK]",
          "mvd/n512 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
