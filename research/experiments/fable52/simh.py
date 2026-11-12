#!/usr/bin/env python3
"""Native-simulator helper: run VSM text (with d get lines) and return dumps."""
import sys, os, struct
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, ROOT)
from mncompile.sim import simulator
SIM = simulator()

def run(text):
    r = SIM.run(text.rstrip("\n") + "\n")
    if r.error:
        raise RuntimeError(f"{r.part}:{r.line}: {r.error}")
    return r

def f32(bits):
    return struct.unpack(">f", struct.pack(">I", bits & 0xffffffff))[0]

def pes(sel=None):
    """yield (path, g, c, b, m, p) for all 4096 PEs (or a sample)."""
    for g in range(4):
        for c in range(2):
            for b in range(8):
                for m in range(16):
                    for p in range(4):
                        yield f"n{g}c{c}b{b}m{m}p{p}", g, c, b, m, p

if __name__ == "__main__":
    r = run('imm f"1.5" $lr0\nd get $lr0n0c0b0m0p0 1\nd get $lr0n1c1b3m5p2 1\n')
    for k, v in r.dump.items(): print(k, hex(v))
    print(r.words)
