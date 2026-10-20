#!/usr/bin/env python3
"""Dump LM0/T/GRF at checkpoints (word-level, exact) while running a VSM program.

Usage:
  python3 trace3.py prog.vsm --after 50,51,57,58 [--pe n0c0b0m0p0] [--lm 0:128]

`d get $lm0` dumps long words; this prints every 32-bit word separately with
its char (low byte, and MSB byte) so the canvas layout is visible.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator  # noqa: E402

TESTCASE = ROOT / "problems/challenge/20.fizzbuzz/testcase.vsm"
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("prog")
    ap.add_argument("--after", default="")
    ap.add_argument("--pe", default="n0c0b0m0p0")
    ap.add_argument("--lm", default="0:128")
    ap.add_argument("--quiet-same", action="store_true")
    args = ap.parse_args()

    pe = args.pe
    lines = Path(args.prog).read_text(encoding="utf-8").rstrip("\n").split("\n")
    checkpoints = sorted(int(x) for x in args.after.split(",") if x.strip())
    lo, hi = (int(x) for x in args.lm.split(":"))

    tc = TESTCASE.read_text(encoding="utf-8")
    pre, suf = tc.split(MARKER, 1)
    suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip()) + "\n"
    sim = simulator()
    sim.register("t3pre", pre)
    sim.register("t3suf", suf)

    prev = None
    for k in checkpoints:
        out = []
        for i, line in enumerate(lines, 1):
            out.append(line)
            if i == k:
                out.append(f"d get $lm0{pe} {max(hi, 8)}")
                out.append(f"d get $lt{pe} 4")
                out.append(f"d get $ls0{pe} 8")
                out.append(f"d get $lr0{pe} 8")
        r = sim.run("\n".join(out) + "\n", prefix_key="t3pre", suffix_key="t3suf")
        if r.error:
            print(f"after {k}: ERROR {r.part}:{r.line}: {r.error}")
            return 1
        lw: dict[int, int] = {}
        t: dict[int, int] = {}
        s: dict[int, int] = {}
        for (mem, p, addr), v in r.dump.items():
            if p != pe:
                continue
            if mem == "LM0":
                lw[addr] = v
            elif mem == "TREG":
                t[addr] = v
            elif mem == "GREG1":
                s[addr] = v
        words = {}
        for a, v in lw.items():
            words[2 * a] = (v >> 32) & 0xFFFFFFFF
            words[2 * a + 1] = v & 0xFFFFFFFF
        twords = {}
        for a, v in t.items():
            twords[2 * a] = (v >> 32) & 0xFFFFFFFF
            twords[2 * a + 1] = v & 0xFFFFFFFF
        print(f"=== after line {k}: {lines[k-1].strip()[:100]}")
        print("  T words:", [f"{twords.get(i,0):#010x}" for i in range(0, 8)])
        print("  GRF1 w0..7:", " ".join(f"{s.get(i,0):#018x}" for i in range(0, 8)))
        row = []
        for a in range(lo, hi):
            v = words.get(a, 0)
            ch = v & 0xFF
            row.append(f"{a}:{ch:02x}" if v else f"{a}:--")
        for i in range(0, len(row), 16):
            print("   ", " ".join(row[i:i+16]))
        prev = words
    sim.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
