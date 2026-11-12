#!/usr/bin/env python3
"""Compare lane variables of a gen5 program against model3 (usage: dbg5.py cfg.json prog.vsm)."""
import sys, json, struct
import numpy as np
import gen5, model3
from simh import run
from chk import lanes, MEMS
cfg = json.load(open(sys.argv[1])) if len(sys.argv) > 1 and sys.argv[1] != "-" else None
g = gen5.G(cfg)
prog = "\n".join(open(sys.argv[2]).read().splitlines()[:-7]) + "\n"
o = model3.run(g.P)
def f32(b): return struct.unpack(">f", struct.pack(">I", b & 0xffffffff))[0]
names = sys.argv[3:] or ["Bv", "mS", "us", "Sv"]
gets = "".join(f"d get $l{g.VAL[n][0]}{g.VAL[n][1]} 4\n" for n in names)
r = run(prog + gets)
exp = {"Bv": lambda i: (None, None), "mS": lambda i: (o["m"][i], o["m"][i]), "us": lambda i: (16 * o["u"][i], 16 * o["u"][i]),
       "Sv": lambda i: (None, o["s"][i]), "nR": lambda i: (o["n"][i], o["n"][i]), "q": lambda i: (o["q"][i], o["q"][i])}
for n in names:
    f, a = g.VAL[n]
    bad = 0; shown = 0
    for idx, (path, cyc, B, k) in enumerate(lanes()):
        v = r.dump[(MEMS[f], path, a + 2 * cyc)]
        e0, e1 = f32(v >> 32), f32(v)
        li = 4 * B + k
        x0, x1 = (float(B), float(B)) if n == "Bv" else exp[n](li)
        if (x0 is not None and e0 != x0) or (x1 is not None and e1 != x1):
            bad += 1
            if shown < 4: print(f"  {n} B={B} k={k} got=({e0},{e1}) exp=({x0},{x1})"); shown += 1
    print(n, "bad", bad)
