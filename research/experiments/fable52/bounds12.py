#!/usr/bin/env python3
import sys, json, random
from collections import Counter
import gen12, search12, relax2
base = dict(gen12.DEFAULT)
for k, v in json.load(open("cfg9_55.json")).items():
    if k in base: base[k] = v
variants = [("A mtab", dict(o_mtab=1)), ("B +xd,dyd", dict(o_mtab=1, o_xd=1, o_dyd=1)), ("C +lhd", dict(o_mtab=1, o_xd=1, o_dyd=1, o_lhd=1)),
            ("D +hd", dict(o_mtab=1, o_xd=1, o_dyd=1, o_lhd=1, o_hd=1)), ("E +h8d", dict(o_mtab=1, o_xd=1, o_dyd=1, o_lhd=1, o_hd=1, o_h8d=1)),
            ("A' mtab ubf", dict(o_mtab=1, o_ubf=1)), ("C' ubf", dict(o_mtab=1, o_xd=1, o_dyd=1, o_lhd=1, o_ubf=1))]
for name, opts in variants:
    c = dict(base); c.update(o_ubf=0, o_tabalu=0); c.update(opts)
    r = search12.repair(c, random.Random(3), gen=gen12)
    g = gen12.G(r); cnt = Counter(o["unit"] for o in g.OPS)
    ra = relax2.relaxed(g.OPS, timeout=30)
    rA = relax2.relaxed(g.OPS, units=(("alu", "imm"), ("l1",)), timeout=20)
    rM = relax2.relaxed(g.OPS, units=(("mau",), ("l1",)), timeout=20)
    print(f"{name:14s} imm {cnt['imm']} alu {cnt['alu']} mau {cnt['mau']} | all {ra[0]}{'' if ra[1] else '?'} alu-only {rA[0]} mau-only {rM[0]}", flush=True)
