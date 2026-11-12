#!/usr/bin/env python3
"""Verify the 2-long-word l1bmr4lbor layout: B = 2048*c' + 512*(mab>>2) + 128*h1 + 16*l2b + 8*h0 + 4*w + pe."""
import re, sys
from emu import run
def dram_dump(body):
    tail = """l1bmr4lbor $llr100v $llb0
nop
nop
l2bmd $lb0 $lc0
l2bmd $lb32 $lc256
nop
mvd/n512 $lc0 $p0@0
mvp/n4096 $p0@0 $d0@0
"""
    gets = "".join(f"d getd $d{i}n0 1\n" for i in range(4096))
    out, err, words = run(body + tail + gets)
    if err: print(err); sys.exit(1)
    return [int(re.search(r"\(0x([0-9A-Fa-f]+)\)", l).group(1), 16) for l in out.splitlines() if "DEBUG" in l]
res = {}
for name, src in [("l2bid", "$l2bid"), ("l1bid", "$l1bid"), ("mabid", "$mabid"), ("subpeid", "$subpeid")]:
    res[name] = dram_dump(f"lpassa {src} $lr100v\nnop\n")
res["cycle"] = dram_dump('imm i"1" $lr100v/0100\nimm i"2" $lr100v/0010\nimm i"3" $lr100v/0001\nnop\n')
bad = 0
for B in range(4096):
    cp = B >> 11; A2 = (B >> 9) & 3; h1 = (B >> 7) & 3; l2 = (B >> 4) & 7; h0 = (B >> 3) & 1; w = (B >> 2) & 1; pe = B & 3
    exp = dict(l2bid=l2, l1bid=h1*2+h0, mabid=(A2*4) | 3, subpeid=pe)
    for k, v in exp.items():
        if res[k][B] != v: bad += 1
    if (res["cycle"][B] & 0xffffffff) != 2*cp + w: bad += 1
print("mismatches", bad, [hex(res["cycle"][i]) for i in (0, 4, 2048, 2052)])
