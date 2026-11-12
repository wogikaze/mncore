#!/usr/bin/env python3
"""Compact probe: run a VSM snippet, then print selected dumps for selected PEs.

Each `probe(snippet, [(mem_prefix, addr, count, pe_tag), ...])` runs a fresh program.
mem_prefix: 'lr' GRF0 long, 'ls' GRF1 long, 'lm' LM0 long, 'llt' T, 'lr0' word access via lr?
"""
import sys, os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, ROOT)
from mncompile.sim import simulator

SIM = simulator()

def run(snippet):
    r = SIM.run(snippet.rstrip("\n") + "\n")
    if r.error:
        raise RuntimeError(f"{r.part}:{r.line}: {r.error}")
    return r

def dumps(snippet, gets):
    """gets: list of (label, loc) where loc is e.g. '$lr0n1c1b0m0p0' and count 4."""
    lines = [snippet.rstrip("\n")]
    for label, loc, count in gets:
        lines.append(f"d get {loc} {count}")
    r = run("\n".join(lines) + "\n")
    out = {}
    i = 0
    # dumps are keyed by (mem, pe, addr); collect long-word values in addr order
    order = []
    for label, loc, count in gets:
        base = int(''.join(ch for ch in loc.split('$')[1] if ch.isdigit())[:1] or 0)
        memname = {'l': 'GREG0', 'm': 'LM0', 'b':'L1BM', 'c':'L2BM', 'p':'PIU', 'd':'DRAM'}
        # find mem char: after optional l/ll prefix
        s = loc.split('$')[1]
        if s.startswith('ll'): s = s[2:]
        elif s.startswith('l'): s = s[1:]
        ch = s[0]
        mem = {'r':'GREG0','s':'GREG1','m':'LM0','n':'LM1','t':'TREG','b':'L1BM','c':'L2BM'}[ch]
        rest = s[1:]
        a = ''
        for c in rest:
            if c.isdigit(): a += c
            else: break
        pe = rest[len(a):]
        petag = 'n1c1b0m0p0' if not pe else pe
        vals = []
        for j in range(count):
            key = (mem, petag, int(a or 0) + 2*j)
            vals.append(r.dump.get(key))
        out[label] = vals
    return out

def show(title, snippet, gets):
    print('##', title)
    out = dumps(snippet, gets)
    for label, vals in out.items():
        print(f'  {label}: ' + ' '.join('None' if v is None else f'{v:016x}' for v in vals))
    return out

if __name__ == '__main__':
    pass
