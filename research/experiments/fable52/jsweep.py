#!/usr/bin/env python3
"""sweep build variants at a fixed horizon: jsweep.py <H> <timeout> <par> <workers> [fixed build opts k=v ...]"""
import sys, itertools, subprocess, json, time
from concurrent.futures import ThreadPoolExecutor
H, T, par, W = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
fixed = dict(a.split("=") for a in sys.argv[5:])
names = [n for n in ("dyd", "hd", "h8d", "xcw", "ta1", "ta2") if n not in fixed]
def run(combo):
    kv = dict(fixed); kv.update({n: str(v) for n, v in zip(names, combo)})
    tag = "_".join(f"{k}{v}" for k, v in sorted(kv.items()))
    args = ["python3", "jopt.py", H, T, f"workers={W}", f"out=/tmp/sw_{H}_{tag}.vsm"] + [f"{k}={v}" for k, v in kv.items()]
    r = subprocess.run(args, capture_output=True, text=True)
    out = r.stdout.strip().splitlines()
    st = out[0][:60] if out else r.stderr[-200:]
    ln = out[1].split()[1] if len(out) > 1 and out[1].startswith("lines") else "-"
    return tag, ln, st
combos = list(itertools.product((0, 1), repeat=len(names)))
with ThreadPoolExecutor(par) as ex:
    for tag, ln, st in ex.map(run, combos):
        print(tag, "->", ln, "|", st, flush=True)
