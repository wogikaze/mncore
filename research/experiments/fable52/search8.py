#!/usr/bin/env python3
"""Local search over the register-file assignment of gen8 (objective: scheduled line count)."""
import sys, random, json, time, os
import multiprocessing as mp
import gen8 as gen7, sched3

CONST1 = ["H8", "K1", "KBc1", "KBc2", "B23", "A4", "H1516", "CP", "XC", "X", "P_A", "P_B", "cUB", "NLc",
          "DX", "IX", "DY", "D", "N23", "N4", "AT"]
LANE = ["SL", "RW", "RA", "RB", "Bv", "L23", "Wv", "nR", "N0", "us", "R1v", "S1s", "S2r", "UAv",
        "Rv", "DA", "Spv", "XA", "Vreg"]
PAIRS = [("Z", "Y1"), ("mS", "mR"), ("DMn", "DMs"), ("Za", "Zb")]
MGS = ["rs", "sr", "rn", "nr", "sn", "ns", "rsn", "srn", "nrs"]
OPTS = ["o_tabalu", "o_vreg", "o_ubf"]

def mutate(cfg, rnd):
    c = dict(cfg)
    k = rnd.random()
    if k < 0.40:
        n = rnd.choice(CONST1); c[n] = rnd.choice("rsn")
    elif k < 0.74:
        n = rnd.choice(LANE); c[n] = "r" if c[n] == "s" else "s"
    elif k < 0.80:
        a, b = rnd.choice(PAIRS); c[a], c[b] = c[b], c[a]
    elif k < 0.84:
        c["MG"] = rnd.choice(MGS)
    elif k < 0.88:
        c["ML"] = rnd.choice("rsn")
    elif k < 0.92:
        c["MP"] = rnd.choice("rsn")
    elif k < 0.96:
        f = rnd.choice("rsn"); g = rnd.choice([x for x in "rsn" if x != f]); c["TF"] = f; c["TBH"] = g
    else:
        o = rnd.choice(OPTS); c[o] = 1 - c.get(o, 0)
    return c

def evaluate(cfg, tries=24, seed0=0, gen=gen7):
    try:
        g = gen.G(cfg)
    except (AssertionError, IndexError, KeyError):
        return 999, None
    if g.viol: return 999, None
    try:
        best = sched3.best_schedule(g.OPS, tries=tries, seed0=seed0)
    except AssertionError:
        return 999, None
    if best is None: return 999, None
    return len(best[0]), best

def repair(start, rnd, limit=200000, gen=gen7):
    cur = dict(start); cv = gen.violations(cur)
    for it in range(limit):
        if cv == 0: return cur
        cand = mutate(cur, rnd)
        v = gen.violations(cand)
        if v <= cv or rnd.random() < 0.02: cur, cv = cand, v
    return None

def chain(args):
    seed, iters, start, tries = args
    rnd = random.Random(seed)
    cur = repair(start, rnd)
    cs, sch = evaluate(cur, tries)
    best = (cs, dict(cur), sched3.render(sch[0]) if sch else None)
    T = 1.2
    for it in range(iters):
        cand = mutate(cur, rnd)
        if rnd.random() < 0.3: cand = mutate(cand, rnd)
        s, sch = evaluate(cand, tries, seed0=rnd.randrange(1000))
        if s <= cs or rnd.random() < pow(2.718, -(s - cs) / T):
            cur, cs = cand, s
            if cs < best[0]: best = (cs, dict(cur), sched3.render(sch[0]))
        T = max(0.25, T * 0.999)
    return best

if __name__ == "__main__":
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    startf = sys.argv[3] if len(sys.argv) > 3 else None
    start = dict(gen7.DEFAULT)
    if startf and os.path.exists(startf): start.update(json.load(open(startf)))
    t = time.time()
    with mp.Pool(nproc) as pool:
        res = pool.map(chain, [(s, iters, start, 24) for s in range(nproc)])
    res.sort(key=lambda x: x[0])
    print("results:", [r[0] for r in res], "time %.0fs" % (time.time() - t))
    best = res[0]
    json.dump(best[1], open("/tmp/cfg8_best.json", "w"), indent=0, sort_keys=True)
    print("best lines", best[0], "total", best[0] + 7, {k: v for k, v in best[1].items() if k.startswith("o_")})
    open("/tmp/v8s.vsm", "w").write(best[2] + "\n".join(gen7.TAIL) + "\n")
