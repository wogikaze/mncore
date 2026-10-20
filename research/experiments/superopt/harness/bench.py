#!/usr/bin/env python3
"""Benchmark the scorer: candidates/second for serial and parallel pools.

Usage: python3 harness/bench.py [--n 80] [--workers 0,4,8,10,12]
Each run uses a fresh temporary cache so every candidate is really evaluated.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

from harness import scorer, transforms, vsmx  # noqa: E402


def candidate_texts(n: int):
    src = (ROOT / "problems/challenge/20.fizzbuzz/answer.vsm").read_text()
    p = vsmx.parse(src)
    fams = ["commute", "addr", "const", "swap", "merge", "move", "delete"]
    out = [(src, "seed", "baseline")]
    for fam in fams:
        for m in transforms.ALL_FAMILIES[fam](p):
            out.append((m.program.text(), m.family, m.detail))
            if len(out) >= n:
                return out
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=80)
    ap.add_argument("--workers", default="0,4,8,10,12")
    ap.add_argument("--asm", default="1")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    items = candidate_texts(args.n)
    rows = []
    for w in [int(x) for x in args.workers.split(",")]:
        with tempfile.TemporaryDirectory() as td:
            sc = scorer.Scorer(Path(td) / "c.sqlite", workers=w,
                               asm_filter=bool(int(args.asm)))
            t0 = time.perf_counter()
            rs = sc.evaluate(items)
            dt = time.perf_counter() - t0
            st = sc.throughput()
            rows.append((w, len(items), dt, st["simulated"], st["asm_error"],
                         st["sim_ok"], st["sim_fail"], st["sim_error"]))
            print(f"workers={w:2d} n={len(items)} {dt:6.2f}s  "
                  f"all={len(items) / dt:6.2f}/s sim={st['simulated']} "
                  f"({st['simulated'] / dt:5.2f} sim/s) asm_err={st['asm_error']} "
                  f"ok={st['sim_ok']} fail={st['sim_fail']} err={st['sim_error']}")
            sc.close()
    if args.json:
        Path(args.json).write_text(json.dumps(
            [{"workers": w, "n": n, "seconds": round(dt, 2),
              "all_per_s": round(n / dt, 2),
              "simulated": sim, "sim_per_s": round(sim / dt, 2),
              "asm_error": asm_err, "sim_ok": okv, "sim_fail": fail,
              "sim_error": err}
             for (w, n, dt, sim, asm_err, okv, fail, err) in rows], indent=2))
        print("wrote", args.json)
    return rows


if __name__ == "__main__":
    main()
