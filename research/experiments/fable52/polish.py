#!/usr/bin/env python3
"""Second-stage search: walk around a good configuration with the fast heuristic, then ask the exact CP-SAT
scheduler whether any visited configuration can be scheduled in fewer lines than the heuristic found.
usage: polish.py <gen> <search> <cfg.json> <target_lines> [n_walk] [nproc]"""
import sys, json, random, importlib, time
import multiprocessing as mp
import sched3, cpsched

def walk(args):
    genname, searchname, cfg, seed, steps, slack = args
    gen = importlib.import_module(genname); search = importlib.import_module(searchname)
    rnd = random.Random(seed)
    cur = dict(cfg); cs, _ = search.evaluate(cur, 24, gen=gen)
    base = cs; seen = {}
    for it in range(steps):
        cand = search.mutate(cur, rnd)
        s, _ = search.evaluate(cand, 12, seed0=rnd.randrange(1000), gen=gen)
        if s <= base + slack:
            cur, cs = cand, s
            seen[json.dumps(cand, sort_keys=True)] = s
    return seen

def exact(args):
    genname, key, target, timeout = args
    gen = importlib.import_module(genname)
    cfg = json.loads(key)
    try:
        g = gen.G(cfg)
        r = cpsched.solve(g.OPS, target, timeout=timeout, workers=1)
    except Exception as e:
        return key, None, None
    if r is None: return key, None, None
    lines, opt, bound = r
    return key, len(lines), sched3.render(lines)

if __name__ == "__main__":
    genname, searchname, cfgf, target = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    steps = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    nproc = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    cfg = json.load(open(cfgf))
    t0 = time.time()
    with mp.Pool(nproc) as pool:
        res = pool.map(walk, [(genname, searchname, cfg, s, steps, 1) for s in range(nproc)])
        seen = {}
        for r in res: seen.update(r)
        keys = sorted(seen, key=lambda k: seen[k])
        print("visited", len(keys), "heuristic histogram", {v: sum(1 for k in keys if seen[k] == v) for v in sorted(set(seen.values()))}, "%.0fs" % (time.time() - t0), flush=True)
        best = None
        for key, n, text in pool.imap_unordered(exact, [(genname, k, target, 20.0) for k in keys]):
            if n is not None and (best is None or n < best[0]):
                best = (n, key, text)
                print("exact found", n, "lines  (%.0fs)" % (time.time() - t0), flush=True)
                gen = importlib.import_module(genname)
                open("/tmp/polish.vsm", "w").write(text + "\n".join(gen.TAIL) + "\n")
                json.dump(json.loads(key), open("/tmp/polish.json", "w"), indent=0, sort_keys=True)
    print("done; best", best[0] if best else None, "%.0fs" % (time.time() - t0))
