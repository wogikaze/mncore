#!/usr/bin/env python3
"""Run an arbitrary snippet through the native simulator and print dumps.

Usage: python3 probe.py $'instr1\ninstr2\nd get $lr0 24' [g,c,h,m,p]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, ROOT)

_sim = None


def get_sim():
    global _sim
    if _sim is None:
        from mncompile.sim import simulator
        _sim = simulator()
    return _sim


def run(snippet, pe=None, error_out=True):
    sim = get_sim()
    r = sim.run(snippet.rstrip("\n") + "\n")
    if r.error and error_out:
        print("ERROR", r.part, r.line, r.error)
    return r


def show(r, pe=None):
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if val == 0:
            continue
        if pe and peid != pe:
            continue
        print(f"{mem:8s} {peid:16s} {addr:5d}  0x{val:016x}")


if __name__ == "__main__":
    snippet = sys.argv[1]
    pe = sys.argv[2] if len(sys.argv) > 2 else None
    r = run(snippet)
    show(r, pe)
