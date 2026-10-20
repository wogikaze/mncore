#!/usr/bin/env python3
"""Native-simulator probe: run a snippet and dump GRF0/GRF1/LM0 etc.

Usage: python3 probe.py $'instr1\ninstr2\nd get $lr0 24' [peid]
Prints non-zero (mem, pe, addr, value) tuples.
"""
import os
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)

_sim = None


def get_sim():
    global _sim
    if _sim is None:
        from mncompile.sim import simulator
        _sim = simulator()
    return _sim


def run(snippet, pe=None):
    sim = get_sim()
    r = sim.run(snippet.rstrip("\n") + "\n")
    if r.error:
        print("ERROR", r.part, r.line, r.error)
    return r


def show(r, pe=None, nonzero=True):
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if nonzero and val == 0:
            continue
        if pe and peid != pe:
            continue
        print(f"{mem:8s} {str(peid):20s} {addr:5d}  0x{val:016x}")


if __name__ == "__main__":
    snippet = sys.argv[1]
    pe = sys.argv[2] if len(sys.argv) > 2 else None
    r = run(snippet)
    show(r, pe)
