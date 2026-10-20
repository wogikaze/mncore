#!/usr/bin/env python3
"""Collect per-block values around the T-chain for all 4096 blocks.

Runs the native simulator on the 93-word solution with `d get` probes inserted
(experiment only; probes are not part of any candidate), and writes a CSV with
block index, coordinates, chain inputs at L41, and the final T value at L48.

Output: chain_data.csv
Columns:
  b, g, c, h, mab, p,
  r18, s4, s128, s130, s132, s134,
  t0_hi, t0_lo, t1_hi, t1_lo, ... t3_*  (T words after L48; hi/lo are the two
  32-bit halves of the (t[4c],t[4c+1]) pair)
"""
from __future__ import annotations

import csv
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

SRC = ROOT / "problems/challenge/20.fizzbuzz/answer.vsm"
OUT = Path(__file__).resolve().parent / "chain_data.csv"


def main():
    lines = SRC.read_text().splitlines()
    # Insert probes after L41 (chain inputs) and after L48 (chain output T).
    probes41 = [
        "d get $lr18 1",
        "d get $ls4 1",
        "d get $ls128 1",
        "d get $ls130 1",
        "d get $ls132 1",
        "d get $ls134 1",
    ]
    prog = lines[:41] + probes41 + lines[41:48] + ["d get $lt 4"] + lines[48:]
    from mncompile.sim import simulator

    sim = simulator()
    r = sim.run("\n".join(prog) + "\n")
    if r.error:
        raise SystemExit(f"sim error {r.part}:{r.line}: {r.error}")
    dump = r.dump

    # group dumps by PE path
    pes = sorted({pe for (_mem, pe, _addr) in dump})
    rows = []
    for pe in pes:
        mm = re.fullmatch(r"n(\d+)c(\d+)b(\d+)m(\d+)p(\d+)", pe)
        if not mm:
            continue
        g, c, h, mab, p = map(int, mm.groups())
        b = (mab >> 1) << 9 | (h >> 1) << 7 | g << 5 | c << 4 | (h & 1) << 3 | (mab & 1) << 2 | p

        def get(mem, addr):
            return dump.get((mem, pe, addr), 0)

        row = [b, g, c, h, mab, p]
        row += [get("GREG0", 18), get("GREG1", 4), get("GREG1", 128),
                get("GREG1", 130), get("GREG1", 132), get("GREG1", 134)]
        for cyc in range(4):
            v = get("TREG", cyc)
            row += [v >> 32, v & 0xFFFFFFFF]
        rows.append(row)
    rows.sort()
    header = (["b", "g", "c", "h", "mab", "p", "r18", "s4", "s128", "s130", "s132", "s134"]
              + [f"t{cyc}_{half}" for cyc in range(4) for half in ("hi", "lo")])
    with OUT.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)
    print(f"wrote {len(rows)} rows to {OUT}")
    # sanity: block set
    print("blocks", rows[0][0], "..", rows[-1][0], "count", len(rows))


if __name__ == "__main__":
    main()
