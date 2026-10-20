#!/usr/bin/env python3
"""Summarise the candidate cache: stages, word/mismatch distributions, bests."""

from __future__ import annotations

import json
import sqlite3
import sys
import zlib
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
DB = HERE / "cache" / "candidates.sqlite"
LOGS = HERE / "logs"


def main():
    db = sqlite3.connect(str(DB))
    total = db.execute("SELECT count(*) FROM evals").fetchone()[0]
    stages = dict(db.execute("SELECT stage, count(*) FROM evals GROUP BY stage"))
    words = db.execute(
        "SELECT words, count(*) FROM evals WHERE ok=1 GROUP BY words ORDER BY words"
    ).fetchall()
    mis = db.execute(
        "SELECT mismatches, count(*) FROM evals WHERE mismatches IS NOT NULL "
        "GROUP BY mismatches ORDER BY mismatches"
    ).fetchall()
    errs_raw = db.execute(
        "SELECT error, count(*) FROM evals WHERE error IS NOT NULL "
        "GROUP BY error").fetchall()
    kinds = Counter()
    examples = {}
    for e, n in errs_raw:
        el = (e or "").lower()
        if "racy memory" in el:
            import re as _re
            m = _re.search(r"racy memory (read|write) at (\w+)", e)
            k = f"DataRace-{m.group(2)}" if m else "DataRace"
        elif "field conflict" in el:
            k = "field conflict"
        elif "uninitialized" in el:
            k = "uninitialized forwarding register"
        elif "terminate called" in el:
            k = "other assembler abort"
        elif "not allowed" in el or "unsupported" in el:
            k = e[:60]
        else:
            k = (e or "")[:60]
        kinds[k] += n
        examples.setdefault(k, (e or "")[:160])
    best = db.execute(
        "SELECT hash, words, lines, stage, ts FROM evals WHERE ok=1 "
        "ORDER BY words, hash LIMIT 15").fetchall()
    # accepted by word count
    ok_words = Counter()
    for w, n in words:
        ok_words[w] += n

    print(f"cache: {DB}")
    print(f"distinct candidates: {total}")
    print(f"stages: {stages}")
    sims = sum(v for k, v in stages.items() if k.startswith("sim"))
    print(f"simulated: {sims}   assembler-rejected: {stages.get('asm_error', 0)}")
    print(f"assembled fraction: {1 - stages.get('asm_error', 0) / max(total, 1):.2%}")
    print("\nfrequency by result:")
    for k, v in stages.items():
        print(f"  {k:12s} {v:7d}  {v / total:6.1%}")
    print("\nsimulator mismatch distribution:")
    buckets = Counter()
    for m, n in mis:
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
    for k in ("0", "1-9", "10-99", "100-999", "1000+"):
        print(f"  {k:9s} {buckets.get(k, 0):7d}")
    print("\naccepted candidates by word count:")
    for w in sorted(ok_words):
        print(f"  {w} words: {ok_words[w]}")
    print("\nbest accepted:")
    for h, w, lines, stage, ts in best:
        print(f"  {w} words  {h[:10]}  {stage}")
    print("\nfailure modes:")
    for k, n in kinds.most_common(20):
        print(f"  {n:6d}  {k:32s} e.g. {examples[k][:110]}")

    # word-count histogram of all candidates (including failures)
    allw = dict(db.execute("SELECT words, count(*) FROM evals GROUP BY words"))
    print("\nall candidates by assembled word count:")
    for w in sorted(allw):
        print(f"  {w}: {allw[w]}")

    # per-family stats from wave summaries
    fam = defaultdict(Counter)
    waves = {}
    for p in sorted(LOGS.glob("summary-*.json")):
        try:
            s = json.loads(p.read_text())
        except Exception:
            continue
        for name, st in s.get("family_stats", {}).items():
            for k, v in st.items():
                fam[name][k] += v
        for name, ws in s.get("waves", {}).items():
            if name not in waves:
                waves[name] = ws
            else:
                waves[name]["items"] += ws.get("items", 0)
                waves[name]["simulated"] += ws.get("simulated", 0)
                waves[name]["asm_error"] += ws.get("asm_error", 0)
                waves[name]["sim_ok"] += ws.get("sim_ok", 0)
    if fam:
        print("\nper-family results (all summary files):")
        for name in sorted(fam):
            c = fam[name]
            print(f"  {name:10s} " + " ".join(f"{k}={c[k]}" for k in
                                               ("sim_ok", "sim_fail", "sim_error", "asm_error")))
    if waves:
        print("\nwaves:")
        for name, w in waves.items():
            print(f"  {name}: {json.dumps(w)}")

    return {"total": total, "stages": stages, "ok_words": dict(ok_words),
            "buckets": dict(buckets), "failure_modes": dict(kinds.most_common(20))}


if __name__ == "__main__":
    main()
