#!/usr/bin/env python3
"""Classify every source line of a VSM solution into issue groups and stages.

Usage: python3 census.py file.vsm [--stage-spec stages.json]
Prints a per-line table (groups used, whether imm-only, stage tag) and totals.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

MAU_CALC = {
    "dmfma", "dmmul", "dvfma", "dvmul", "dvadd", "dvpassa",
    "fmfma", "fmmul", "fvfma", "fvmul", "fvadd", "fvpassa",
    "gmfma", "gmmul", "hmfma", "hmmul", "hvfma", "hvmul", "hvadd", "hvpassa",
}
MAU_WRITE = {"dmwrite", "fmwrite", "gmwrite", "hmwrite"}
MAU_READ = {"dmread", "fmread", "gmread", "hmread"}


def group_of(op: str) -> str:
    if op == "nop":
        return "nop"
    if op == "noforward":
        return "noforward"
    if op == "wait":
        return "wait"
    if op.startswith("l1b"):
        return "l1bm"
    if op.startswith("l2b"):
        return "l2bm"
    if op in MAU_WRITE:
        return "mau-mwrite"
    if op in MAU_READ:
        return "mau-mread"
    if op in MAU_CALC:
        return "mau-calc"
    return "alu"


def main() -> None:
    path = Path(sys.argv[1])
    lines = path.read_text().splitlines()
    counts: dict[str, int] = {}
    expr_total = 0
    words = 0
    n_imm = 0
    imm_alone: list[int] = []
    print(f"{'ln':>3} {'grp':<38} {'imm':<4} stage   source")
    for i, raw in enumerate(lines, 1):
        text = raw.split("#")[0].strip()
        if not text:
            continue
        words += 1
        if text.startswith("mv"):
            counts["mv"] = counts.get("mv", 0) + 1
            print(f"{i:3d} {'MV':<38} {'':<4} {'-':<7} {text}")
            continue
        exprs = [e.strip() for e in text.split(";") if e.strip()]
        groups = [group_of(e.split()[0].split("/")[0]) for e in exprs]
        expr_total += len(exprs)
        for g in groups:
            counts[g] = counts.get(g, 0) + 1
        has_imm = any(e.split()[0].split("/")[0] == "imm" for e in exprs)
        n_imm += sum(1 for e in exprs if e.split()[0].split("/")[0] == "imm")
        if has_imm and len(exprs) == 1:
            imm_alone.append(i)
        print(f"{i:3d} {','.join(groups):<38} {'IMM' if has_imm else '':<4} {'':<7} {text}")
    print()
    print(f"words={words} lines_expressions={expr_total} imm_total={n_imm}")
    print("expression counts by group:")
    for g, c in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"  {g:12s} {c}")
    print(f"imm-only lines ({len(imm_alone)}): {imm_alone}")
    # lower bound on words from group capacity: each group is at most 1 expression per line,
    # so the number of lines must be at least max over groups (excluding nop/wait).
    hard = {g: c for g, c in counts.items() if g not in ("nop", "noforward", "wait", "mv")}
    print(f"max single-group expression count = {max(hard.values())} ({max(hard, key=hard.get)})")


if __name__ == "__main__":
    main()
