#!/usr/bin/env python3
import sys, json, random
from collections import Counter
import gen13, search13, relax2
base = json.load(open(sys.argv[1]))
variants = [("base", {}), ("xd", dict(o_xd=1)), ("dyd", dict(o_dyd=1)), ("xd,dyd", dict(o_xd=1, o_dyd=1)), ("xd,dyd,hd", dict(o_xd=1, o_dyd=1, o_hd=1)),
            ("h8d", dict(o_h8d=1)), ("ubf", dict(o_ubf=1)), ("tabalu", dict(o_tabalu=1)), ("mtab", dict(o_mtab=1)), ("mtab,lhd,xd,dyd", dict(o_mtab=1, o_lhd=1, o_xd=1, o_dyd=1))]
for name, opts in variants:
    c = dict(base); c.update(opts)
    r = search13.repair(c, random.Random(3), gen=gen13)
    if r is None: print(name, "no valid config"); continue
    g = gen13.G(r); cnt = Counter(o["unit"] for o in g.OPS)
    ra = relax2.relaxed(g.OPS, timeout=30)
    rA = relax2.relaxed(g.OPS, units=(("alu", "imm"), ("l1",)), timeout=20)
    rM = relax2.relaxed(g.OPS, units=(("mau",), ("l1",)), timeout=20)
    print(f"{name:18s} imm {cnt['imm']} alu {cnt['alu']} mau {cnt['mau']} | all {ra[0]}{'' if ra[1] else '?'} alu-only {rA[0]} mau-only {rM[0]}", flush=True)
