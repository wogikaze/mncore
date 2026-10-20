#!/usr/bin/env python3
"""Parse official DEBUG-DRAM lines and check the PE->DRAM block mapping.

Usage: analyze_layout.py <log> 1block|2block
  1block: probes/p08_tag_1block.vsm  (every PE's tag must be at DRAM[b])
  2block: probes/p07_tag_2block.vsm  (long word 0 at b, long word 1 at b+2048)

Tags are written by the probes as a 32-bit word, so they sit in the MSB half of the
long word: the value expected at a DRAM address is tag << 32.
"""
import re, sys

def parse(path):
    v = {}
    for line in open(path, errors="replace"):
        m = re.search(r"DEBUG-DRAM\(n(\d+),(\d+)\):.*\(0x([0-9a-f]+)\)", line)
        if m:
            v[int(m.group(2))] = int(m.group(3), 16)
    return v

def tag_of(b):
    """Inverse of b = 512*(m>>1)+128*(h>>1)+32*g+16*c+8*(h&1)+4*(m&1)+p."""
    p = b & 3
    ma = (b >> 2) & 1
    ha = (b >> 3) & 1
    c = (b >> 4) & 1
    g = (b >> 5) & 3
    hh = (b >> 7) & 3
    mh = (b >> 9) & 7
    l2bid = g * 2 + c
    h = hh * 2 + ha
    m = mh * 2 + ma
    peid = m * 4 + p
    return (l2bid << 9) | (h << 6) | peid

def main(path, mode):
    v = parse(path)
    if mode == "1block":
        bad = [(b, hex(v.get(b, 0)), hex(tag_of(b) << 32)) for b in range(4096)
               if v.get(b) != tag_of(b) << 32]
        print(f"1-block: {4096-len(bad)}/4096 match; first bad: {bad[:4]}")
        return 0 if not bad else 1
    badA = [(b) for b in range(2048) if v.get(b) != tag_of(b) << 32]
    badB = [(b) for b in range(2048)
            if v.get(b + 2048) != (tag_of(b) | 0x10000) << 32]
    print(f"2-block: blockA {2048-len(badA)}/2048, blockB(+2048) {2048-len(badB)}/2048")
    return 0 if not badA and not badB else 1

if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1], sys.argv[2]))
