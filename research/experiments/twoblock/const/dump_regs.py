#!/usr/bin/env python3
"""Dump GRF0/GRF1/T words just before a given line of a VSM, for a few PEs."""
import argparse, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator
from pathlib import Path as P
import re
TC = ROOT/"problems/challenge/20.fizzbuzz/testcase.vsm"
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("prog"); ap.add_argument("--after", type=int, required=True)
    ap.add_argument("--pes", default="n0c0b0m0p0,n0c0b1m1p3,n0c1b3m2p2")
    ap.add_argument("--n", type=int, default=32)
    a = ap.parse_args()
    lines = P(a.prog).read_text().rstrip("\n").split("\n")
    tc = TC.read_text(); pre, suf = tc.split(MARK,1)
    suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip())+"\n"
    sim = simulator(); sim.register("cp",pre); sim.register("cs",suf)
    out=[]
    for i,l in enumerate(lines,1):
        out.append(l)
        if i==a.after:
            for pe in a.pes.split(","):
                out.append(f"d get $lr{pe} {a.n}")
                out.append(f"d get $ls{pe} {a.n}")
    r=sim.run("\n".join(out)+"\n", prefix_key="cp", suffix_key="cs")
    if r.error: print("ERR", r.part, r.line, r.error); return 1
    for pe in a.pes.split(","):
        for mem in ("GREG0","GREG1"):
            lw={x:v for (m,p,x),v in r.dump.items() if p==pe and m==mem}
            W={}
            for x,v in lw.items():
                W[x]=(v>>32)&0xffffffff; W[x+1]=v&0xffffffff
            nz=[(i,W[i]) for i in range(a.n*2) if W.get(i,0)]
            print(f"{pe} {mem}: {[(i,hex(v)) for i,v in nz]}")
    return 0
raise SystemExit(main())
