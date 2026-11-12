#!/usr/bin/env python3
"""Port-free lower bound (units + latencies only) for an op list, via CP-SAT."""
import sys, json, itertools
from collections import Counter
from ortools.sat.python import cp_model
import sched3

def relaxed(ops, horizon=70, timeout=30):
    producer, grp, off, groups, deps = sched3.prepare(ops)
    n = len(ops)
    m = cp_model.CpModel()
    t = [m.NewIntVar(0, horizon, "") for i in range(n)]
    for c, o in enumerate(ops):
        for v in o["fwd"]: m.Add(t[c] == t[producer[v]] + 1)
    for p, c, L in deps: m.Add(t[c] >= t[p] + L)
    for unit in (("alu", "imm"), ("mau",), ("l1",)):
        ids = [i for i, o in enumerate(ops) if o["unit"] in unit]
        m.AddAllDifferent([t[i] for i in ids])
    last = [i for i, o in enumerate(ops) if o["dst"] == ["OUT"]][0]
    for i in range(n):
        if i != last: m.Add(t[i] < t[last])
    m.Minimize(t[last])
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = timeout; s.parameters.num_workers = 8
    st = s.Solve(m)
    return s.Value(t[last]) + 1, st == cp_model.OPTIMAL, [s.Value(x) for x in t]

if __name__ == "__main__":
    import gen5
    base = json.load(open(sys.argv[1]))
    opts = ["o_f1alu", "o_f2alu", "o_nsalu", "o_tabalu", "o_c100"]
    for combo in itertools.product([0, 1], repeat=len(opts)):
        c = dict(base); c.update(dict(zip(opts, combo)))
        try:
            g = gen5.G(c)
        except AssertionError as e:
            c["CX"] = "n"
            try: g = gen5.G(c)
            except AssertionError as e2:
                print(combo, "assert", e2); continue
        L, opt, tv = relaxed(g.OPS)
        cnt = Counter(o["unit"] for o in g.OPS)
        print(combo, "bound", L, "opt" if opt else "?", "imm", cnt["imm"], "alu", cnt["alu"], "mau", cnt["mau"])
