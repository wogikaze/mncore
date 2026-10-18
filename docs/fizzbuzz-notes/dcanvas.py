#!/usr/bin/env python3
"""Print the LM0 canvas words and T before/after each line in a range."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, ROOT)
from mncompile.sim import simulator
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
TC = os.path.join(ROOT, "problems/challenge/20.fizzbuzz", "testcase.vsm")
lo, hi, PE = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
g,c,b,m,p = PE.split(","); loc=f"n{g}c{c}b{b}m{m}p{p}"
lines = open(os.path.join(ROOT,"problems/challenge/20.fizzbuzz/main.vsm")).read().rstrip("\n").split("\n")
pre,suf = open(TC).read().split(MARKER,1)
sim=simulator(); sim.register("pre",pre); sim.register("suf",suf)
prev=None
for k in range(lo,hi+1):
    out=[]
    for i,l in enumerate(lines,1):
        out.append(l)
        if i==k:
            out.append(f"d get $lm0{loc} 128")
            out.append(f"d get $t{loc} 4")
    r=sim.run("\n".join(out)+"\n",prefix_key="pre",suffix_key="suf")
    if r.error: print(k,"ERR",r.error); break
    d={}; T=None
    for (mm,pe,addr),v in r.dump.items():
        if mm=="LM0": d[addr]=v
        if mm=="TREG" and addr==0: T=v
    mx=max(d) if d else 0
    w=[]
    for a in range(0,mx+1,2):
        v=d.get(a,0)
        w.append((v>>32)&0xffffffff); w.append(v&0xffffffff)
    if prev is not None:
        diffs=[(i,w[i]) for i in range(128) if w[i]!=prev[i]]
        print(f"after {k}: T={T} changed={[(i,hex(v)) for i,v in diffs]}")
        print("   canvas:", " ".join(f"{w[i]&0xff:02x}" for i in range(48)))
    prev=w
sim.close()
