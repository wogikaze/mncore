#!/usr/bin/env python3
"""Dump machine state after a prefix of the answer (native sim).

Usage: python3 state.py N [--pe n0c0b0m0p0] [--all]
Prints nonzero GRF0/GRF1 words with float interpretation, plus T and masks.
"""
import argparse
import struct
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

BASE = "base.vsm"


def f32(u):
    return struct.unpack("<f", struct.pack("<I", u & 0xFFFFFFFF))[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--pe", default="n0c0b0m0p0")
    ap.add_argument("--words", type=int, default=260)
    args = ap.parse_args()
    lines = [l for l in open(BASE).read().splitlines() if l.split("#")[0].strip()]
    pre = lines[: args.n]
    sim = simulator()
    prog = "\n".join(pre) + f"\nd get $lr0 {args.words}\nd get $ls0 {args.words}\nd get $llt 4\n"
    r = sim.run(prog + "\n")
    if r.error:
        print("ERROR", r.error)
        return
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) != args.pe:
            continue
        if val == 0:
            continue
        msb, lsb = val >> 32, val & 0xFFFFFFFF
        print(f"{mem} word{addr:4d} = 0x{val:016x}  msb={msb:#010x} ({f32(msb):.7g}) "
              f"lsb={lsb:#010x} ({f32(lsb):.7g})")


if __name__ == "__main__":
    main()
