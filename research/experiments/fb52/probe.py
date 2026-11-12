#!/usr/bin/env python3
"""Probe helper for fb52: run a snippet on the native simulator and dump values.

Usage: python3 probe.py 'snippet' [filter]
Prints non-zero dumps sorted by (mem, pe, addr). Use d get ... lines in the snippet.
"""
import sys, os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, ROOT)
from mncompile.sim import simulator

def run(snippet, show=True, only_nonzero=True, filt=None):
    sim = simulator()
    r = sim.run(snippet.rstrip("\n") + "\n")
    if r.error:
        print("ERROR", r.part, r.line, r.error)
    rows = []
    for (mem, pe, addr), val in sorted(r.dump.items()):
        if filt and filt not in pe and filt != mem:
            continue
        if only_nonzero and val == 0:
            continue
        rows.append((mem, pe, addr, val))
    if show:
        for mem, pe, addr, val in rows:
            print(f"{mem:8s} {pe:14s} {addr:6d}  0x{val:016x}")
    return r, rows

if __name__ == "__main__":
    snip = sys.argv[1]
    filt = sys.argv[2] if len(sys.argv) > 2 else None
    run(snip, filt=filt)
