#!/usr/bin/env python3
"""Coordinate stage (correctness-first layout, one ALU expression per line).

Per (PE, cycle) it produces X = 8*B (float, MSB word of $lr56+2c) and the
role k = mabid & 3 (float, MSB word of $lr52), where

    B = 1024*cycle + 512*m3 + 128*h1 + 16*l2bid + 8*h0 + 4*m2 + pe

is the DRAM long-word index reached through l1bmr4 -> l2bmd x2 -> mvd -> mvp.
"""
from stageC import hp, fbits
from simh import run, pes, f32

ZR = fbits(-(2.0 ** 36) - 2.0 ** 26)

CONSTS = [
    f"imm {hp(126, 14)} $n0/1000",
    f"imm {hp(-4, 0)} $n1/1000",
    f"imm {hp(16, 16)} $n2/1000",
    'imm f"8192" $ln6/1000',
    'imm f"64" $n17/1000',
    'imm f"32" $n18/1000',
    'imm f"8" $n16/1000',
    f'imm ui"0x{ZR:08x}" $ls4/1000',
]

PIPE = [
    'imm ui"0x4b000000" $t $lr0/1000 $ls0/1000',
    "ior $subpeid $aluf $lr8/1000 $ls8/1000",
    "dmwrite $aluf $lx0; ior $l2bid $t $lr6/1000",
    "dmread $lx0 $lr16v $ls16v",
    "nop",
    "uilsr $mabid $r[16,20,22,16] $r[28,26,24,30]",
    "uilsr $l1bid $r[16,18,16,16] $r[27,25,31,31]",
    "fvfma $lr16v $ln6 $ls4 $lr64v",
    "ior $lr[6,24,26,28] $t $lr32v",
    "nop",
    "fvadd $lr32v -$ls0 $lr40v $ls40v",
    "nop",
    "fvfma $lr[40,42,44,40] $n[2,0,1,3]e $ls[8,44,46,40] $lr48v $ls48v",
    "nop",
    "fvfma $ls48 $n16 $lr64v $nowrite",
    "fvfma $r51 $n17 $mauf $nowrite",
    "fvfma $r50 $n18 $mauf $lr56v $ls56v",
]


def text():
    return "\n".join(CONSTS + PIPE) + "\n"


def expected_b0(g, c, b, m, p):
    l2b = 2 * g + c
    return 512 * (m >> 3) + 128 * (b >> 1) + 16 * l2b + 8 * (b & 1) + 4 * ((m >> 2) & 1) + p


if __name__ == "__main__":
    r = run(text() + "d get $lr56 4\nd get $lr52 1\n")
    bad = 0
    for path, g, c, b, m, p in pes():
        b0 = expected_b0(g, c, b, m, p)
        for cyc in range(4):
            x = f32(r.dump[("GREG0", path, 56 + 2 * cyc)] >> 32)
            bad += x != 8 * (b0 + 1024 * cyc)
        bad += f32(r.dump[("GREG0", path, 52)] >> 32) != (m & 3)
    print("words", r.words, "bad", bad)
