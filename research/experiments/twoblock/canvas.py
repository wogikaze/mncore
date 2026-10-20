#!/usr/bin/env python3
"""Dump LM0 canvas at a checkpoint (correct word mapping) for several PEs.

`d get $lm0 <pe> N` returns long words at addresses 0,2,4,...,2(N-1) (the key is
the long-word address).  The long word at address a is word a (MSB half) and
word a+1 (LSB half).

Usage:
  python3 canvas.py prog.vsm --after 84 --pes n0c0b0m0p0,n0c0b0m0p1 --lm 0:64
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator  # noqa: E402

TESTCASE = ROOT / "problems/challenge/20.fizzbuzz/testcase.vsm"
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="


def collect(r, pe, mem):
    lw = {addr: v for (m, p, addr), v in r.dump.items() if p == pe and m == mem}
    words = {}
    for a, v in lw.items():
        words[a] = (v >> 32) & 0xFFFFFFFF
        words[a + 1] = v & 0xFFFFFFFF
    return words


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("prog")
    ap.add_argument("--after", type=int, required=True)
    ap.add_argument("--pes", required=True)
    ap.add_argument("--lm", default="0:64")
    ap.add_argument("--mem", default="LM0")
    ap.add_argument("--int", action="store_true", help="print as char when low byte looks printable")
    args = ap.parse_args()

    pes = args.pes.split(",")
    lines = Path(args.prog).read_text(encoding="utf-8").rstrip("\n").split("\n")
    lo, hi = (int(x) for x in args.lm.split(":"))

    tc = TESTCASE.read_text(encoding="utf-8")
    pre, suf = tc.split(MARKER, 1)
    suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip()) + "\n"
    sim = simulator()
    sim.register("cvpre", pre)
    sim.register("cvsuf", suf)

    out = []
    for i, line in enumerate(lines, 1):
        out.append(line)
        if i == args.after:
            for pe in pes:
                out.append(f"d get ${args.mem.lower()}{pe} {hi}")
                out.append(f"d get $lt{pe} 4")
    r = sim.run("\n".join(out) + "\n", prefix_key="cvpre", suffix_key="cvsuf")
    if r.error:
        print(f"ERROR {r.part}:{r.line}: {r.error}")
        return 1
    for pe in pes:
        words = collect(r, pe, args.mem)
        tw = collect(r, pe, "TREG")
        print(f"--- PE {pe}: T[C] = {[tw.get(4*c+1,0) for c in range(4)]}")
        row = []
        for a in range(lo, hi):
            v = words.get(a, 0)
            if args.int:
                ch = v & 0xFF
                row.append(f"{a}:{chr(ch)}" if 32 <= ch < 127 and (v >> 8) == 0 else f"{a}:{v:08x}")
            else:
                row.append(f"{a}:{v:08x}")
        for i in range(0, len(row), 8):
            print("   ", " ".join(row[i:i+8]))
    sim.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
