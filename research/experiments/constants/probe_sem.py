#!/usr/bin/env python3
"""Batch native-sim probe. Each case: (label, snippet). Dumps whatever d get lines say."""
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

sim = simulator()

CASES = []


def case(label):
    def deco(fn):
        CASES.append((label, fn()))
        return fn
    return deco


@case("imm i\"7\" $r16 ; word addressing")
def _():
    return 'imm i"7" $r16\nd get $lr0 14'


@case("imm ui\"0x4b000000\" $t ; T layout")
def _():
    return 'imm ui"0x4b000000" $t\nd get $llt 4'


@case("imm i\"8\" to flat [16,17,28,0] mask 1110")
def _():
    return 'imm i"8" $r[16,17,28,0]/1110\nd get $lr0 20'


@case("imm i\"8\" to flat [16,17,28,0] mask 1111")
def _():
    return 'imm i"8" $r[16,17,28,0]/1111\nd get $lr0 20'


@case("default v stride: lpassa $lm[0,4,10,14] $ln0v")
def _():
    return ('d set $lm0n0c0b0m0p0 8 l1l2l3l4l5l6l7\n'
            'lpassa $lm[0,4,10,14] $ln0v\nd get $ln0 10')


@case("prologue dance only (4 lines)")
def _():
    return ('ipackbit $subpeid $t $nowrite\n'
            'dmwrite $aluf $lx0; imm i"56" $r16/1000\n'
            'dmread $lx0 $lr0v4; imm i"599" $s31\n'
            'iinc $mreadf $lr2v4\n'
            'd get $lr0 20\nd get $ls0 34')


@case("dmwrite $s0->x0, dmread x0 addr0 -> lr0v")
def _():
    return ('d set $ls0n0c0b0m0p0 8 l10l11l12l13l14l15l16l17\n'
            'dmwrite $s0v $lx0\ndmread $lx0 $lr0v\nd get $lr0 12')


@case("dmwrite addr 1, dmread addr 0 (rotation)")
def _():
    return ('d set $ls0n0c0b0m0p0 8 l10l11l12l13l14l15l16l17\n'
            'dmwrite $s0v $lx1\ndmread $lx0 $lr0v\nd get $lr0 12')


for label, snippet in CASES:
    print("=" * 70)
    print("CASE:", label)
    print("-- program --")
    print(snippet)
    r = sim.run(snippet + "\n")
    if r.error:
        print("ERROR", r.part, r.line, r.error)
        continue
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) == "n0c0b0m0p0":
            print(f"  {mem:8s} {peid:24s} {addr:5d}  0x{val:016x}")
