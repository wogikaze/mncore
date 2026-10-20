#!/usr/bin/env python3
"""Trace PE register/memory values at chosen source lines of a VSM program.

Local experimental tool: inserts `d get` lines (allowed in experiments, not in
submitted candidates) and runs the native simulator once per checkpoint.

Usage:
  python3 trace_regs.py --after 42,47 --blocks 0,4 --regs r,s,t base.vsm
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

REG_INFO = {
    "r": ("lr", "GREG0"),
    "s": ("ls", "GREG1"),
    "m": ("lm", "LM0"),
    "n": ("ln", "LM1"),
    "t": ("lt", "TREG"),
    "o": ("omr1", "OMR"),
}


def block_to_loc(b: int) -> str:
    g = (b >> 5) & 3
    c = (b >> 4) & 1
    h = (((b >> 7) & 3) << 1) | ((b >> 3) & 1)
    m = ((b >> 9) << 1) | ((b >> 2) & 1)
    p = b & 3
    return f"n{g}c{c}b{h}m{m}p{p}"


def trace_one(sol_lines, after, regs, blocks, reg_words, sim):
    out = []
    for i, line in enumerate(sol_lines, 1):
        out.append(line)
        if i == after:
            for b in blocks:
                loc = block_to_loc(b)
                for reg in regs:
                    tok, _ = REG_INFO[reg]
                    n = reg_words.get(reg, 8 if reg != "o" else 1)
                    out.append(f"d get ${tok}{loc} {n}")
    r = sim.run("\n".join(out) + "\n")
    if r.error:
        raise SystemExit(f"sim error {r.part}:{r.line}: {r.error}")
    return r.dump


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--after", required=True)
    ap.add_argument("--blocks", default="0")
    ap.add_argument("--regs", default="r,s,t")
    ap.add_argument("--words", default="", help="e.g. r:32,s:32")
    ap.add_argument("--nonzero", action="store_true")
    ap.add_argument("solution")
    args = ap.parse_args()
    afters = [int(x) for x in args.after.split(",")]
    blocks = [int(x) for x in args.blocks.split(",")]
    regs = args.regs.split(",")
    words = {}
    for part in args.words.split(","):
        if ":" in part:
            k, v = part.split(":")
            words[k] = int(v)

    from mncompile.sim import simulator

    sim = simulator()
    sol = Path(args.solution).read_text().splitlines()
    for after in afters:
        dump = trace_one(sol, after, regs, blocks, words, sim)
        for b in blocks:
            loc = block_to_loc(b)
            print(f"\n===== after L{after}  block {b} ({loc}) =====")
            for reg in regs:
                _, name = REG_INFO[reg]
                entries = sorted(
                    (addr, val) for (mem, pe, addr), val in dump.items()
                    if mem == name and pe == loc
                )
                if args.nonzero:
                    entries = [(a, v) for a, v in entries if v != 0]
                if not entries:
                    print(f"  {name}: (empty)")
                else:
                    s = " ".join(f"{a}:{v:016x}" for a, v in entries)
                    print(f"  {name}: {s}")


if __name__ == "__main__":
    main()
