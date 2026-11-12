#!/usr/bin/env python3
"""Simulated annealing over register-file assignments where each candidate is scored by the exact CP-SAT scheduler
(time-limited, hinted by the heuristic schedule).  usage: exsa.py <gen> <search> <cfg.json> <iters> [nproc] [tlim]"""
import sys, json, random, importlib, time
import multiprocessing as mp
import sched3, cpsched

def exact_score(gen, cfg, ub, tlim):
    """best line count <= ub found by CP-SAT within tlim (None if nothing found)"""
    try:
        g = gen.G(cfg)
    except (AssertionError, IndexError, KeyError):
        return None
    if g.viol: return None
    try:
        hb = sched3.best_schedule(g.OPS, tries=12)
    except AssertionError:
        return None
    hint = None
    if hb is not None and len(hb[0]) <= ub:
        hint = [hb[1][i] for i in range(len(g.OPS))]
    try:
        r = cpsched.solve(g.OPS, ub, timeout=tlim, workers=1, hint=hint)
    except Exception:
        return None
    if r is None:
        return (len(hb[0]), sched3.render(hb[0])) if hb is not None and len(hb[0]) <= ub else None
    return len(r[0]), sched3.render(r[0])

def chain(args):
    genname, searchname, start, seed, iters, tlim, slack = args
    gen = importlib.import_module(genname); search = importlib.import_module(searchname)
    rnd = random.Random(seed)
    cur = dict(start)
    r = exact_score(gen, cur, 60, tlim)
    cs = r[0] if r else 99
    best = (cs, dict(cur), r[1] if r else None)
    for it in range(iters):
        cand = search.mutate(cur, rnd)
        if rnd.random() < 0.3: cand = search.mutate(cand, rnd)
        hs, _ = search.evaluate(cand, 8, seed0=rnd.randrange(1000), gen=gen)
        if hs > cs + slack: continue                      # heuristic prefilter
        r = exact_score(gen, cand, cs + 1, tlim)
        if r is None: continue
        s = r[0]
        if s <= cs or rnd.random() < 0.15:
            cur, cs = cand, s
            if s < best[0]:
                best = (s, dict(cand), r[1])
    return best

if __name__ == "__main__":
    genname, searchname, cfgf, iters = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 12
    tlim = float(sys.argv[6]) if len(sys.argv) > 6 else 6.0
    start = json.load(open(cfgf))
    t0 = time.time()
    with mp.Pool(nproc) as pool:
        res = pool.map(chain, [(genname, searchname, start, s, iters, tlim, 3) for s in range(nproc)])
    res.sort(key=lambda x: x[0])
    print("results:", [r[0] for r in res], "time %.0fs" % (time.time() - t0))
    b = res[0]
    gen = importlib.import_module(genname)
    json.dump(b[1], open("/tmp/exsa_best.json", "w"), indent=0, sort_keys=True)
    open("/tmp/exsa.vsm", "w").write(b[2] + "\n".join(gen.TAIL) + "\n")
    print("best lines", b[0], "total", b[0] + 7, {k: v for k, v in b[1].items() if k.startswith("o_")})
