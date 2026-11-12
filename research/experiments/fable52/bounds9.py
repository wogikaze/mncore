#!/usr/bin/env python3
import sys, json, itertools, importlib
import relax2
gen = importlib.import_module(sys.argv[1])
cfg = json.load(open(sys.argv[2]))
names = sys.argv[3].split(",")
for combo in itertools.product([0, 1], repeat=len(names)):
    c = dict(cfg); c.update(dict(zip(names, combo)))
    import random
    try:
        g = gen.G(c)
    except AssertionError as e:
        print(combo, "assert", e); continue
    from collections import Counter
    cnt = Counter(o["unit"] for o in g.OPS)
    try:
        r = relax2.relaxed(g.OPS, timeout=20)
        ra = relax2.relaxed(g.OPS, units=(("alu", "imm"), ("l1",)), timeout=20)
        rm = relax2.relaxed(g.OPS, units=(("mau",), ("l1",)), timeout=20)
        rl = relax2.relaxed(g.OPS, units=(), timeout=20)
    except AssertionError as e:
        print(dict(zip(names, combo)), "prepare assert", e); continue
    print(dict(zip(names, combo)), "viol", g.viol, "imm", cnt["imm"], "alu", cnt["alu"], "mau", cnt["mau"], "| all", r[0], "alu-only", ra[0], "mau-only", rm[0], "lat", rl[0])
