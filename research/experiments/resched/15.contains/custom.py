#!/usr/bin/env python3
"""Run a solution on custom A (16 values, same for all L1Bs or 1024) and B (1024) with the official emulator.
Prints C for L1B group 0 and checks all groups. usage: custom.py sol.vsm [seed|pattern]"""
import sys, subprocess, random
from pathlib import Path
ROOT = Path('/home/wogikaze/wgkz/mncore')
E = ROOT/'judge/judge-py/mncore2_emuenv'

def run(sol_text, A, B):
    L = []
    for g in range(64):
        n, c, b = g // 16, (g // 8) % 2, g % 8
        for i in range(16):
            L.append(f"d set $lm{2*i}n{n}c{c}b{b} 1 {A[g*16+i]:016X}")
    for q in range(64):
        m, p = q // 4, q % 4
        for i in range(16):
            L.append(f"d set $ln{2*i}m{m}p{p} 1 {B[q*16+i]:016X}")
    gets = []
    for g in range(64):
        n, c, b = g // 16, (g // 8) % 2, g % 8
        for i in range(16):
            gets.append(f"d getd $ln{32+2*i}n{n}c{c}b{b}m0p0 1")
    full = "\n".join(L) + "\n" + sol_text + "\n" + "\n".join(gets) + "\n"
    asm = subprocess.run([str(E/'assemble3'), '--instruction-mode', 'flat'], input=full.encode(), capture_output=True)
    if asm.returncode:
        return None, asm.stderr.decode()[-2000:]
    lines = [l for l in asm.stdout.decode().split('\n') if l.split() and (l.split()[0] in 'jm' or l.split()[0] == 'd')]
    r = subprocess.run([str(E/'gpfn3_package_main'), '--offchip-memory-init', 'zero'], input="\n".join(lines).encode(), capture_output=True)
    out = []
    for l in r.stderr.decode().splitlines():
        if l.startswith('DEBUG-LM1'):
            out.append(int(l.split('(0x')[1].split(')')[0], 16))
    if len(out) != 1024:
        return None, r.stderr.decode()[-2000:]
    return out, ""

def expect(A, B):
    s = set(B)
    return [1 if a in s else 0 for a in A]

def cases(seed):
    rnd = random.Random(seed)
    yield "rand", [rnd.randint(0, 1000) for _ in range(1024)], [rnd.randint(0, 1000) for _ in range(1024)]
    allv = list(range(1001))
    yield "allA_neighbours", [rnd.randint(0, 1000) for _ in range(1024)], [rnd.choice(range(0, 1001, 2)) for _ in range(1024)]
    yield "odd B", [rnd.randint(0, 1000) for _ in range(1024)], [rnd.choice(range(1, 1001, 2)) for _ in range(1024)]
    yield "B0", [rnd.randint(0, 3) for _ in range(1024)], [0] * 1024
    yield "B1000", [rnd.choice([999, 1000, 998, 0]) for _ in range(1024)], [1000] * 1024
    yield "Bfull", [rnd.randint(0, 1000) for _ in range(1024)], [i % 1001 for i in range(1024)]
    yield "sparse", [rnd.randint(0, 1000) for _ in range(1024)], [rnd.choice([5, 500, 501, 77]) for _ in range(1024)]
    yield "dupA", [rnd.choice([5, 6, 500, 501, 77, 0]) for _ in range(1024)], [rnd.randint(0, 1000) for _ in range(1024)]

if __name__ == "__main__":
    sol = Path(sys.argv[1]).read_text()
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    bad = 0
    for name, A, B in cases(seed):
        out, err = run(sol, A, B)
        if out is None:
            print(name, "ERROR", err); bad += 1; continue
        exp = expect(A, B)
        nb = sum(1 for x, y in zip(out, exp) if x != y)
        print(f"{name}: mismatches={nb}")
        bad += nb > 0
    print("ALL OK" if bad == 0 else "FAIL")
