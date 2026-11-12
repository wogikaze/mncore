#!/usr/bin/env python3
"""Verify the l1bmr4lbor -> l2bmd x2 -> mvd -> mvp layout formula on the official emulator."""
import re, sys
from emu import run

def dram_dump(body):
    tail = """l1bmr4lbor $aluf $lb0
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
    vals = []
    for line in out.splitlines():
        m = re.search(r"\(0x([0-9A-Fa-f]+)\)", line)
        if m: vals.append(int(m.group(1), 16))
    return vals

res = {}
for name, body in [
    ("l2bid", "lpassa $l2bid $nowrite\n"),
    ("l1bid", "lpassa $l1bid $nowrite\n"),
    ("mabid", "lpassa $mabid $nowrite\n"),
    ("subpeid", "lpassa $subpeid $nowrite\n"),
    ("cycle", 'imm i"1" $lr100v/0100\nimm i"2" $lr100v/0010\nimm i"3" $lr100v/0001\nnop\nlpassa $lr100v $nowrite\n'),
]:
    res[name] = dram_dump(body)
    print(name, len(res[name]), res[name][:8], res[name][1020:1028])
bad = 0
for B in range(4096):
    c = B >> 10; m3 = (B >> 9) & 1; h1 = (B >> 7) & 3; l2 = (B >> 4) & 7; h0 = (B >> 3) & 1; m2 = (B >> 2) & 1; pe = B & 3
    exp = dict(l2bid=l2, l1bid=h1*2+h0, mabid=(m3*8+m2*4) | 3, subpeid=pe)
    for k, v in exp.items():
        if res[k][B] != v: bad += 1
    cyc = res["cycle"][B]
    if (cyc >> 32) != c and cyc != c: bad += 1
print("mismatches", bad, "cycle sample", [hex(res["cycle"][i]) for i in (0, 1024, 2048, 3072)])
