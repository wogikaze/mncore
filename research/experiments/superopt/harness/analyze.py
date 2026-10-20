#!/usr/bin/env python3
"""Final accounting over the candidate cache and the wave summaries.

Writes logs/final_report.json and prints the tables used in RESULTS.md.
"""

from __future__ import annotations

import json
import re
import sqlite3
import sys
import zlib
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
DB = HERE / "cache" / "candidates.sqlite"
LOGS = HERE / "logs"


def error_kind(e: str) -> str:
    if not e:
        return "none"
    el = e.lower()
    m = re.search(r"racy memory (read|write) at (\w+)", e)
    if m:
        return f"data race ({m.group(2)})"
    if "field conflict" in el:
        m = re.search(r"between `([^`]*)` and `([^`]*)`", e)
        if m:
            return f"field conflict ({m.group(1)}/{m.group(2)})"
        return "field conflict (other)"
    if "uninitialized" in el or "accessing ialu forwarding" in el:
        return "uninitialized forwarding register"
    if "mask" in el and "conflict" in el:
        return "mask entry conflict"
    if "non pe operation" in el:
        return "MV in PE row"
    if "too many operand" in el:
        return "MV operand error"
    if "terminate called" in el:
        return "assembler abort (other)"
    return e[:70]


def main():
    db = sqlite3.connect(str(DB))
    q = lambda s, a=(): db.execute(s, a).fetchall()
    distinct = q("SELECT count(*) FROM evals")[0][0]
    stages = dict(q("SELECT stage,count(*) FROM evals GROUP BY stage"))
    simulated = sum(v for k, v in stages.items() if k.startswith("sim"))
    ok = q("SELECT count(*) FROM evals WHERE ok=1")[0][0]
    ok_words = dict(q("SELECT words,count(*) FROM evals WHERE ok=1 GROUP BY words"))
    buckets = Counter()
    for m, n in q("SELECT mismatches,count(*) FROM evals WHERE mismatches IS NOT NULL "
                  "GROUP BY mismatches"):
        if m == 0:
            buckets["0"] += n
        elif m < 10:
            buckets["1-9"] += n
        elif m < 100:
            buckets["10-99"] += n
        elif m < 1000:
            buckets["100-999"] += n
        else:
            buckets["1000+"] += n
    kinds = Counter()
    for e, n in q("SELECT error,count(*) FROM evals WHERE error IS NOT NULL "
                  "GROUP BY error"):
        kinds[error_kind(e)] += n

    # how many word-reducing (92-row) programs were tested end to end?
    rows = q("SELECT text,stage,ok,words,mismatches FROM evals")
    by_rows = defaultdict(Counter)
    for blob, stage, okv, words, mis in rows:
        if blob is None:
            continue
        nrows = zlib.decompress(blob).decode().count("\n")
        by_rows[nrows][stage] += 1
    reductions = {n: dict(c) for n, c in sorted(by_rows.items())}

    # aggregate family stats over every summary file
    fam = defaultdict(Counter)
    waves = defaultdict(dict)
    tags = []
    for p in sorted(LOGS.glob("summary-*.json")):
        try:
            s = json.loads(p.read_text())
        except Exception:
            continue
        tags.append({"tag": s.get("tag"), "best_words": s.get("best_words"),
                     "throughput": s.get("throughput"),
                     "elapsed_s": s.get("elapsed_s")})
        for name, st in s.get("family_stats", {}).items():
            for k, v in st.items():
                fam[name][k] += v
        for name, ws in s.get("waves", {}).items():
            w = waves[name]
            for k in ("items", "new", "cached", "asm_error", "sim_ok",
                      "sim_fail", "sim_error", "simulated", "wall_s"):
                w[k] = w.get(k, 0) + (ws.get(k, 0) or 0)

    best = q("SELECT hash,words,stage FROM evals WHERE ok=1 ORDER BY words,hash LIMIT 10")
    report = {
        "distinct_candidates": distinct,
        "stages": stages,
        "simulated": simulated,
        "accepted": ok,
        "accepted_words": ok_words,
        "mismatch_buckets": dict(buckets),
        "failure_modes": dict(kinds.most_common(25)),
        "rows_per_program": reductions,
        "family_stats": {k: dict(v) for k, v in fam.items()},
        "waves": dict(waves),
        "campaigns": tags,
        "best": [{"hash": h, "words": w, "stage": s} for h, w, s in best],
    }
    (LOGS / "final_report.json").write_text(json.dumps(report, indent=2))

    print(f"distinct candidates: {distinct}")
    print(f"simulator evaluations: {simulated}")
    print(f"accepted (mismatches=0): {ok}  words={ok_words}")
    print(f"stages: {stages}")
    print(f"mismatch buckets: {dict(buckets)}")
    print("\nfailure modes:")
    for k, n in kinds.most_common(25):
        print(f"  {n:7d}  {k}")
    print("\nprograms by row count (word count):")
    for n in sorted(reductions):
        print(f"  {n} rows: {reductions[n]}")
    print("\nper-family (submissions):")
    for name in sorted(fam):
        c = fam[name]
        tot = sum(c.values())
        print(f"  {name:18s} n={tot:6d} " + " ".join(
            f"{k}={c[k]}" for k in
            ("sim_ok", "sim_fail", "sim_error", "asm_error")))
    print("\nwaves:")
    for name in sorted(waves):
        print(f"  {name:18s} {json.dumps(waves[name])}")
    print("\ncampaigns:")
    for t in tags:
        print(f"  {t['tag']}: best={t['best_words']} "
              f"new={t['throughput']['new']} simulated={t['throughput']['simulated']} "
              f"rate={t['throughput']['new_per_second']}/s")
    print("\nbest accepted:", report["best"])
    return report


if __name__ == "__main__":
    main()
