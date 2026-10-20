#!/usr/bin/env python3
"""Evidence that the fast scorer agrees with the official tools.

Checks
------
1. `tools/fbcheck.py` and the in-process scorer both report the baseline as
   93 words / 0 mismatches.
2. `tools/fbverify.py` (official assemble3 + gpfn3 + testcase `d getd`
   expectations) reports `ACCEPTED!! score=93` for the same baseline text.
3. The official assembler's word count equals the simulator's word count on a
   sample of cached candidates (including assembler rejects, where the count
   is undefined).
4. For a sample of candidates the fast scorer accepted, `fbverify` accepts them
   too (the search oracle is not more permissive than the gate).

Writes logs/agreement.json.
"""

from __future__ import annotations

import json
import random
import re
import subprocess
import sys
import time
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

import tools.fbcheck as fb  # noqa: E402
from harness import scorer  # noqa: E402

BASELINE = ROOT / "problems/challenge/20.fizzbuzz/answer.vsm"
DB = HERE / "cache" / "candidates.sqlite"


def official_verify(text: str) -> dict:
    """Run tools/fbverify.py on a temporary file and parse its verdict."""
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".vsm", delete=False) as f:
        f.write(text)
        path = f.name
    t0 = time.time()
    p = subprocess.run([sys.executable, str(ROOT / "tools/fbverify.py"), path],
                       text=True, capture_output=True)
    dt = time.time() - t0
    out = p.stdout + p.stderr
    m = re.search(r"ACCEPTED!! score=(\d+) j=(\d+) m=(\d+)", out)
    return {
        "ok": bool(m),
        "score": int(m.group(1)) if m else None,
        "j": int(m.group(2)) if m else None,
        "m": int(m.group(3)) if m else None,
        "seconds": round(dt, 2),
        "tail": out.strip().splitlines()[-1][:200] if out.strip() else "",
    }


def main():
    base_text = BASELINE.read_text()
    evidence = {"baseline": {}, "word_count_agreement": [], "gate_sample": []}

    # 1. fast scorer on the baseline
    r = fb.check(base_text)
    evidence["baseline"]["fbcheck"] = {"ok": r.ok, "words": r.words,
                                       "lines": r.lines,
                                       "mismatches": r.mismatches}
    print("fbcheck baseline:", r)

    # 2. official gate on the baseline
    ev = official_verify(base_text)
    evidence["baseline"]["fbverify"] = ev
    print("fbverify baseline:", ev)
    assert r.words == 93 and r.mismatches == 0 and r.ok
    assert ev["ok"] and ev["score"] == 93

    # 3. word count agreement on a sample of cached candidates
    import sqlite3

    db = sqlite3.connect(str(DB))
    rows = db.execute(
        "SELECT hash, stage, words, text FROM evals WHERE text IS NOT NULL "
        "AND stage IN ('sim_ok','sim_fail','sim_error')").fetchall()
    rng = random.Random(11)
    rng.shuffle(rows)
    import mncompile.sim as ms

    asm = ms.assembler()
    for h, stage, words, blob in rows[:40]:
        text = zlib.decompress(blob).decode()
        a = asm.assemble(text)
        if not a.ok:
            continue
        rr = fb.check(text)
        rec = {"hash": h[:10], "stage": stage, "asm_words": a.words,
               "sim_words": rr.words, "mismatches": rr.mismatches}
        rec["match"] = a.words == rr.words
        evidence["word_count_agreement"].append(rec)
        if not rec["match"]:
            print("MISMATCH", rec)
    print(f"word-count agreement: {len(evidence['word_count_agreement'])} sampled, "
          f"{sum(1 for x in evidence['word_count_agreement'] if x['match'])} match")
    assert all(x["match"] for x in evidence["word_count_agreement"])

    # 4. official gate on a sample of fast-scorer-accepted candidates
    accepted = db.execute(
        "SELECT hash, words, text FROM evals WHERE ok=1 AND stage='sim_ok' "
        "ORDER BY words ASC, hash LIMIT 200").fetchall()
    # include the lowest-word accepted candidates and a few random ones
    sample = accepted[:2]
    rest = accepted[2:]
    rng.shuffle(rest)
    sample += rest[:1]
    for h, words, blob in sample:
        text = zlib.decompress(blob).decode()
        ev = official_verify(text)
        rec = {"hash": h[:10], "words": words, "fbverify_ok": ev["ok"],
               "score": ev["score"]}
        evidence["gate_sample"].append(rec)
        print("gate sample:", rec)
    # every sampled candidate must be accepted with the same score
    assert all(x["fbverify_ok"] and x["score"] == x["words"]
               for x in evidence["gate_sample"]), evidence["gate_sample"]

    out = HERE / "logs" / "agreement.json"
    out.write_text(json.dumps(evidence, indent=2))
    print("wrote", out)
    return evidence


if __name__ == "__main__":
    main()
