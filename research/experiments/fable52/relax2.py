#!/usr/bin/env python3
"""Port-free bounds with selected unit constraints (diagnostics)."""
import sys, json
from ortools.sat.python import cp_model
import sched3

def relaxed(ops, units=(("alu", "imm"), ("mau",), ("l1",)), horizon=70, timeout=30, free_imm=False):
    producer, grp, off, groups, deps = sched3.prepare(ops)
    n = len(ops)
    m = cp_model.CpModel()
    t = [m.NewIntVar(-40 if free_imm else 0, horizon, "") for i in range(n)]
    for c, o in enumerate(ops):
        for v in o["fwd"]: m.Add(t[c] == t[producer[v]] + 1)
        for v, d in o.get("at", ()): m.Add(t[c] == t[producer[v]] + d)
    for p, c, L in deps: m.Add(t[c] >= t[p] + L)
    for unit in units:
        ids = [i for i, o in enumerate(ops) if o["unit"] in unit]
        m.AddAllDifferent([t[i] for i in ids])
    if free_imm:
        for i, o in enumerate(ops):
            if o["unit"] != "imm": m.Add(t[i] >= 0)
    last = [i for i, o in enumerate(ops) if o["dst"] == ["OUT"]][0]
    for i in range(n):
        if i != last: m.Add(t[i] < t[last])
    m.Minimize(t[last])
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = timeout; s.parameters.num_workers = 8
    st = s.Solve(m)
    return s.Value(t[last]) + 1, st == cp_model.OPTIMAL, [s.Value(x) for x in t]

if __name__ == "__main__":
    import importlib
    gen = importlib.import_module(sys.argv[1])
    cfg = json.load(open(sys.argv[2]))
    g = gen.G(cfg)
    print("all units      :", relaxed(g.OPS)[:2])
    print("no ALU limit   :", relaxed(g.OPS, units=(("mau",), ("l1",)))[:2])
    print("no MAU limit   :", relaxed(g.OPS, units=(("alu", "imm"), ("l1",)))[:2])
    print("latency only   :", relaxed(g.OPS, units=())[:2])
    print("imm free (ALU ops only in ALU slot):", relaxed(g.OPS, units=(("alu",), ("mau",), ("l1",)), free_imm=True)[:2])
