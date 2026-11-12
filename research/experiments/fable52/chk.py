#!/usr/bin/env python3
"""Lane checker: run VSM on native sim, dump lane variables (v-stride long words) for all PEs."""
import struct
from simh import run
MEMS = {"r": "GREG0", "s": "GREG1", "n": "LM1", "m": "LM0"}
def lanes():
    for g in range(4):
        for c in range(2):
            for b in range(8):
                for m in range(16):
                    for p in range(4):
                        path = f"n{g}c{c}b{b}m{m}p{p}"
                        l2b = 2 * g + c
                        B0 = 512 * (m >> 3) + 128 * (b >> 1) + 16 * l2b + 8 * (b & 1) + 4 * ((m >> 2) & 1) + p
                        for cyc in range(4):
                            yield path, cyc, 1024 * cyc + B0, m & 3
def bits_to_f(b):
    return struct.unpack(">f", struct.pack(">I", b & 0xffffffff))[0]
def dump(prog, regs):
    """regs: list of (file_letter, word_base). Returns dict[(file, base)][(path, cyc)] = 64-bit value."""
    gets = "".join(f"d get $l{f}{w} 4\n" for f, w in regs)
    r = run(prog + gets)
    out = {}
    for f, w in regs:
        d = {}
        for path, cyc, B, k in lanes():
            d[(path, cyc)] = r.dump[(MEMS[f], path, w + 2 * cyc)]
        out[(f, w)] = d
    return out, r.words
def check(prog, specs, maxshow=5):
    """specs: list of (file, base, fn(B, k) -> 64-bit int or None (don't care), mask64)."""
    regs = [(f, w) for f, w, *_ in specs]
    out, words = dump(prog, regs)
    allok = True
    for f, w, fn, mask in specs:
        bad = 0; shown = 0
        for path, cyc, B, k in lanes():
            exp = fn(B, k)
            if exp is None: continue
            got = out[(f, w)][(path, cyc)]
            if (got ^ exp) & mask:
                bad += 1
                if shown < maxshow:
                    print(f"  MISMATCH {f}{w} B={B} k={k} got={got:016x} exp={exp:016x}")
                    shown += 1
        print(f"check {f}{w}: bad={bad}")
        allok &= bad == 0
    return allok, words
