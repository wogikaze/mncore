#!/usr/bin/env python3
"""List which output words the table candidate breaks, and why.

Runs a candidate with the native simulator against the official testcase's
`d getd` expectations, prints:
  * total mismatched DRAM long words,
  * the first broken block indices and their (r18, w, true k, predicted k),
  * the distribution of broken blocks by w and by the table index j=r18>>3.

Usage: python3 analyze_candidate.py cand_table_keep51.vsm
"""
from __future__ import annotations

import codecs
import csv
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
TESTCASE = ROOT / "problems/challenge/20.fizzbuzz/testcase.vsm"
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="


def k_of(x: int, w: int) -> int:
    return sum(x >= t for t in [w + 8, 2 * w + 8, 3 * w + 13, 4 * w + 23, 5 * w + 33, 6 * w + 33])


def main():
    cand = Path(sys.argv[1])
    tc = TESTCASE.read_text()
    pre, suf = tc.split(MARKER, 1)
    expected = {}
    for m in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="([^"]*)"', tc):
        expected[int(m.group(1))] = codecs.decode(m.group(2), "unicode_escape").encode("latin-1")
    suf = "\n".join(line.split("#")[0].rstrip() for line in suf.splitlines() if line.split("#")[0].strip()) + "\n"
    from mncompile.sim import simulator

    sim = simulator()
    sim.register("pre", pre)
    sim.register("suf", suf)
    r = sim.run(cand.read_text(), prefix_key="pre", suffix_key="suf")
    if r.error:
        raise SystemExit(f"sim error {r.part}:{r.line}: {r.error}")
    mism = []
    for (mem, _pe, addr), val in r.dump.items():
        if mem != "DRAM":
            continue
        exp = expected.get(addr)
        if exp is None:
            continue
        got = val.to_bytes(8, "big")
        if got[: len(exp)] != exp:
            mism.append(addr)
    mism.sort()
    print(f"{cand}: words={r.words} mismatched DRAM long words={len(mism)}")

    rows = {int(x["b"]): x for x in csv.DictReader((Path(__file__).parent / "chain_data.csv").open())}
    residues = [0, 0, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 6]
    by_w = Counter()
    by_j = Counter()
    detail = []
    for b in mism:
        row = rows.get(b)
        if row is None:
            continue
        x = int(row["r18"])
        w = int(row["s4"])
        j = x >> 3
        pred = residues[j] if j < len(residues) else -1
        true = k_of(x, w)
        by_w[w] += 1
        by_j[j] += 1
        if len(detail) < 15:
            detail.append((b, x, j, w, true, pred))
    print("broken blocks by w:", dict(by_w))
    print("broken blocks by j=r18>>3:", dict(sorted(by_j.items())))
    print("first 15: (block, r18, j, w, true_k, table_pred_k)")
    for d in detail:
        print("  ", d)


if __name__ == "__main__":
    main()
