#!/usr/bin/env python3
"""Per-stage word table for a VSM solution + cross-tabs of wasted words."""
from __future__ import annotations
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from census import group_of  # noqa: E402

STAGES = [
    (1, 4, "S0 prologue constant dance (GRF0 1..7 via dmwrite/dmread/iinc)"),
    (5, 13, "S1 block-coordinate build (bit gather l1bid/peid/l2bid)"),
    (14, 25, "S2 base/threshold/mask setup (2^23 float trick, n1=8b+8, compare masks)"),
    (26, 49, "S3 digit estimate + Fizz/Buzz selection (reciprocals, lsub T-chain)"),
    (50, 56, "S4 canvas value/position (scroll offset, fftoi to T)"),
    (57, 77, "S5 canvas drawing (T-register character writes + 4 nop)"),
    (78, 84, "S6 pack 8 bytes into one long word"),
    (85, 93, "S7 transfer (l1bmd, 2x l2bmd, mvd, mvp) + 4 nop"),
]


def main() -> None:
    path = Path(sys.argv[1])
    lines = path.read_text().splitlines()
    stats = {s[2]: dict(words=0, alu=0, mau=0, imm=0, immonly=0, nop=0, other=0) for s in STAGES}
    by_line = {}
    for i, raw in enumerate(lines, 1):
        t = raw.split("#")[0].strip()
        if not t:
            continue
        stage = next(s[2] for s in STAGES if s[0] <= i <= s[1])
        st = stats[stage]
        st["words"] += 1
        if t.startswith("mv"):
            st["other"] += 1
            by_line[i] = "MV"
            continue
        exprs = [e.strip() for e in t.split(";") if e.strip()]
        groups = [group_of(e.split()[0].split("/")[0]) for e in exprs]
        ops = [e.split()[0].split("/")[0] for e in exprs]
        has_alu = "alu" in groups
        has_mau = any(g.startswith("mau") for g in groups)
        n_imm = ops.count("imm")
        st["alu"] += n_imm and 1 or 0
        if has_alu:
            st["alu"] += 0  # alu already counted via n_imm; recompute below
        st["mau"] += sum(1 for g in groups if g.startswith("mau"))
        st["imm"] += n_imm
        if n_imm and len(exprs) == 1:
            st["immonly"] += 1
        if groups == ["nop"]:
            st["nop"] += 1
        if not has_alu and not has_mau and groups not in (["nop"], ["noforward"]):
            st["other"] += 1
        by_line[i] = (groups, ops)
    # recompute ALU expression counts cleanly
    for stage in stats.values():
        stage["alu"] = 0
    for i, v in by_line.items():
        if v == "MV":
            continue
        stage = next(s[2] for s in STAGES if s[0] <= i <= s[1])
        stats[stage]["alu"] += sum(1 for op in v[1] if group_of(op) == "alu")

    print("| stage | words | ALU expr | MAU expr | imm expr | imm-only words | nop words |")
    print("|---|---|---|---|---|---|---|")
    for s in STAGES:
        st = stats[s[2]]
        print(f"| {s[2]} | {st['words']} | {st['alu']} | {st['mau']} | {st['imm']} | {st['immonly']} | {st['nop']} |")
    tw = sum(s["words"] for s in stats.values())
    ta = sum(s["alu"] for s in stats.values())
    tm = sum(s["mau"] for s in stats.values())
    ti = sum(s["imm"] for s in stats.values())
    tio = sum(s["immonly"] for s in stats.values())
    tn = sum(s["nop"] for s in stats.values())
    print(f"| **total** | **{tw}** | **{ta}** | **{tm}** | **{ti}** | **{tio}** | **{tn}** |")

    # line classes
    n_alu_only = n_both = n_mau_only = n_block = n_nop = n_mv = 0
    for i, v in by_line.items():
        if v == "MV":
            n_mv += 1
            continue
        groups, ops = v
        has_alu = "alu" in groups
        has_mau = any(g.startswith("mau") for g in groups)
        if groups == ["nop"]:
            n_nop += 1
        elif has_alu and has_mau:
            n_both += 1
        elif has_alu:
            n_alu_only += 1
        elif has_mau:
            n_mau_only += 1
        else:
            n_block += 1
    print()
    print("line classes:")
    print(f"  ALU only              {n_alu_only}")
    print(f"  ALU + MAU co-issued   {n_both}")
    print(f"  MAU only (ALU slot free) {n_mau_only}")
    print(f"  nop                   {n_nop}")
    print(f"  block/L1BM/L2BM only  {n_block}")
    print(f"  MV                    {n_mv}")
    print(f"  check sum             {n_alu_only+n_both+n_mau_only+n_nop+n_block+n_mv}")


if __name__ == "__main__":
    main()
