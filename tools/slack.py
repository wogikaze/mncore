#!/usr/bin/env python3
"""Rank problems by the gap between the recorded answer and simple lower bounds of its own dataflow.

    python3 tools/slack.py [--top N] [problem ...]

For each `problems/**/answer.vsm` the expressions are parsed with `mncompile.machine` and a dependency
graph is built from their reads and writes (exact words for PE memories, coarse 8-long-word blocks for
L1BM/L2BM, the forwarding registers tied to the previous line's producer). Each edge gets the minimum line
distance of its storage (forwarding 1, T/GRF 2, LM0/LM1/BAR 3, L1BM 3, turnaround 1, L2BM 2, matrix 1).
Bounds reported:

  chain  longest path in lines through that graph (the answer's algorithm, perfectly scheduled)
  alu / mau / mwrite / mread / l2bm   expressions per issue group (one per line each); l1bm counts half
         (a line can hold one PE->L1BM and one L1BM->PE expression); w:lm0 / w:lm1 count expressions writing
         that memory (one write per memory per line)
  lb     max(chain, unit counts) + MV words

`gap = score - lb` is how many words the recorded answer spends beyond what its own dataflow needs under
this model. It is a pointer, not a proof: the latencies are approximations, port and same-line conflicts
are ignored, and a different algorithm can beat `lb`. A large gap means waiting or serialization that the
model does not explain; a small gap with `lb` set by a unit count means the algorithm itself must change.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from mncompile.machine import L1, L2, Bar, Dram, Fwd, Mat, Mem, Omr, Pdm, parse_program, unit_of  # noqa: E402

LAT = {"grf0": 2, "grf1": 2, "t": 2, "lm0": 3, "lm1": 3, "omr": 1, "bar": 3, "lb": 3, "lbi": 1, "lc": 2,
       "mat": 1, "dram": 0, "pdm": 0}
FWD_UNIT = {"aluf": "alu", "mauf": "mau", "lbf": "l1bm", "mreadf": "mread"}


def keys(op, writing: bool):
    """Storage keys an operand touches: (space, unit-address)."""
    if isinstance(op, Mem):
        out = set()
        for c in range(4):
            if writing and op.mask is not None and op.mask.flags() is not None and not op.mask.flags()[c]:
                continue
            for w in op.words(c):
                out.add((op.space, w))
            if op.tind:
                out.add(("t", c * 4))
        return out
    if isinstance(op, Omr):
        return {("omr", op.entry)}
    if isinstance(op, Bar):
        return {("bar", int(op.lm1))}
    if isinstance(op, L1):
        if op.addr is None:
            return {("lbi", 0)}
        return {("lb", (op.addr + k) // 8) for k in range(0, 8 * op.wl * 4, 8)}
    if isinstance(op, L2):
        return {("lc", (op.addr + k) // 64) for k in range(0, 256, 64)}
    if isinstance(op, Dram):
        return {("dram", 0)}
    if isinstance(op, Pdm):
        return {("pdm", 0)}
    if isinstance(op, Mat):
        return {("mat", op.side)}
    return set()


def analyse(text: str) -> dict:
    steps = parse_program(text)
    last_write: dict = {}  # key -> (line, latency)
    prev_units: dict = {}  # unit -> line of the most recent issue
    finish = {}
    counts: dict = {}
    pe_line = 0
    mv = 0
    chain = 0
    for st in steps:
        if st.nop:
            pe_line += st.nop
            continue
        instrs = st.instrs
        if all(unit_of(i.opcode) == "mv" for i in instrs):
            mv += len(instrs)
            for i in instrs:
                for o in i.dsts:
                    for k in keys(o, True):
                        last_write[k] = (None, 0)
            continue
        pe_line += 1
        line_ready = {}
        for i in instrs:
            u = unit_of(i.opcode)
            if u in ("nop", "noforward", "wait"):
                continue
            counts[u] = counts.get(u, 0) + 1
            for space in {o.space for o in i.dsts if isinstance(o, Mem)}:
                counts["w:" + space] = counts.get("w:" + space, 0) + 1
            ready = 1
            for o in i.srcs:
                if isinstance(o, Fwd):
                    pu = FWD_UNIT.get(o.kind)
                    if pu in prev_units and prev_units[pu] is not None:
                        ready = max(ready, finish.get((pu, prev_units[pu]), 1) + 1)
                    continue
                for k in keys(o, False):
                    if k in last_write and last_write[k][0] is not None:
                        ln, lat = last_write[k]
                        ready = max(ready, ln + lat)
            for o in i.dsts:  # read-modify of masks/flags is ignored; outputs only order writes
                pass
            line_ready[id(i)] = (u, ready)
        for i in instrs:
            if id(i) not in line_ready:
                continue
            u, ready = line_ready[id(i)]
            finish[(u, pe_line)] = ready
            chain = max(chain, ready)
            for o in i.dsts:
                for k in keys(o, True):
                    space = k[0]
                    last_write[k] = (ready, LAT.get(space, 2))
            prev_units[u] = pe_line
    l1 = counts.get("l1bm", 0) + counts.get("l1bm-turnaround", 0)
    unit_bound = max([counts.get(u, 0) for u in ("alu", "mau", "mwrite", "mread", "l2bm", "w:lm0", "w:lm1")]
                     + [(l1 + 1) // 2])
    return {"pe": pe_line, "mv": mv, "chain": chain, "counts": counts, "lb": max(chain, unit_bound) + mv}


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("problems", nargs="*")
    ap.add_argument("--top", type=int, default=100)
    a = ap.parse_args(argv[1:])
    dirs = [ROOT / "problems" / p for p in a.problems] or sorted(
        {p.parent for p in (ROOT / "problems").glob("**/answer.vsm")})
    rows = []
    for d in dirs:
        name = str(d.relative_to(ROOT / "problems"))
        try:
            r = analyse((d / "answer.vsm").read_text(encoding="utf-8"))
        except Exception as e:  # noqa: BLE001
            print(f"{name}: parse error: {e}", file=sys.stderr)
            continue
        score = r["pe"] + r["mv"]
        rows.append((score - r["lb"], name, score, r))
    rows.sort(key=lambda x: (-x[0], -x[2]))
    print(f"{'gap':>4} {'score':>5} {'lb':>4} {'chain':>5} {'alu':>4} {'mau':>4} {'mw':>3} {'mr':>3} {'l1bm':>4} {'l2bm':>4} {'wLM1':>4} {'mv':>3}  problem")
    for gap, name, score, r in rows[: a.top]:
        c = r["counts"]
        l1 = c.get("l1bm", 0) + c.get("l1bm-turnaround", 0)
        print(f"{gap:4d} {score:5d} {r['lb']:4d} {r['chain']:5d} {c.get('alu', 0):4d} {c.get('mau', 0):4d} {c.get('mwrite', 0):3d} {c.get('mread', 0):3d} "
              f"{l1:4d} {c.get('l2bm', 0):4d} {c.get('w:lm1', 0):4d} {r['mv']:3d}  {name}")


if __name__ == "__main__":
    main(sys.argv)
