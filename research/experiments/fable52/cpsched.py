#!/usr/bin/env python3
"""Exact scheduler (CP-SAT) for a fixed op list from gen4: minimise the number of compute lines.

Same rules as sched3: unit slots, forwarding = next line, register latency, one read pattern and one
write per file per line, LM0/LM1 never read+written on one line, an LM write blocks reads of that LM
on the next two lines, imm excludes LM0 access, one mask entry / one zero-flush op per line.
"""
import sys, json, time
from ortools.sat.python import cp_model
import sched3

def conflicts(ops):
    """pairs (i, j) that cannot share a line (i < j)."""
    n = len(ops)
    out = []
    for i in range(n):
        tmp = {}
        sched3.take(tmp, 0, ops[i])
        for j in range(i + 1, n):
            if not sched3.fits(tmp, 0, ops[j]): out.append((i, j))
    return out

def solve(ops, ub, lb=1, timeout=60.0, workers=8, hint=None, log=False):
    producer, grp, off, groups, deps = sched3.prepare(ops)
    n = len(ops)
    m = cp_model.CpModel()
    H = ub
    t = [m.NewIntVar(0, H - 1, f"t{i}") for i in range(n)]
    # forwarding
    for c, o in enumerate(ops):
        for v in o["fwd"]:
            m.Add(t[c] == t[producer[v]] + 1)
        for v, d in o.get("at", ()):
            m.Add(t[c] == t[producer[v]] + d)
    for p, c, L in deps:
        m.Add(t[c] >= t[p] + L)
    cf = conflicts(ops)
    for i, j in cf:
        m.Add(t[i] != t[j])
    # LM write -> read blocking
    info = [sched3.info(o) for o in ops]
    for f in ("m", "n"):
        W = [i for i in range(n) if any(x[0] == f for x in info[i][1])]
        R = [i for i in range(n) if any(x[0] == f for x in info[i][0])]
        for w in W:
            for r in R:
                if w == r: continue
                # forbid t[r] - t[w] in {1, 2}
                b = m.NewBoolVar("")
                m.Add(t[r] <= t[w]).OnlyEnforceIf(b)
                m.Add(t[r] >= t[w] + 3).OnlyEnforceIf(b.Not())
    last = [i for i, o in enumerate(ops) if o["dst"] == ["OUT"]][0]
    for i in range(n):
        if i != last: m.Add(t[i] < t[last])
    m.Add(t[last] >= lb - 1)
    m.Minimize(t[last])
    if hint:
        for i in range(n): m.AddHint(t[i], hint[i])
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = timeout
    s.parameters.num_workers = workers
    s.parameters.log_search_progress = log
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None
    tv = [s.Value(x) for x in t]
    L = tv[last] + 1
    lines = [[] for _ in range(L)]
    for i in sorted(range(n), key=lambda i: sched3.UNIT_ORDER[ops[i]["unit"]]):
        lines[tv[i]].append(ops[i])
    return lines, st == cp_model.OPTIMAL, s.BestObjectiveBound() + 1

if __name__ == "__main__":
    import importlib
    gen4 = importlib.import_module(sys.argv[3] if len(sys.argv) > 3 else "gen5")
    cfg = json.load(open(sys.argv[1])) if len(sys.argv) > 1 else None
    timeout = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    g = gen4.G(cfg)
    hb = sched3.best_schedule(g.OPS, tries=200)
    ub = len(hb[0])
    hint = [hb[1][i] for i in range(len(g.OPS))]
    print("heuristic:", ub)
    t0 = time.time()
    r = solve(g.OPS, ub, timeout=timeout, hint=hint)
    lines, opt, bound = r
    print("cp-sat lines", len(lines), "optimal" if opt else "feasible", "bound", bound, "time %.0fs" % (time.time() - t0))
    text = sched3.render(lines) + "\n".join(gen4.TAIL) + "\n"
    open("/tmp/v4c.vsm", "w").write(text)
