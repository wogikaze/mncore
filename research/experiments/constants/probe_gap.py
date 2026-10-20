#!/usr/bin/env python3
"""Measure minimum write->read gaps for GRF0/GRF1 between ALU and MAU."""
import subprocess
from pathlib import Path

ASM = "/home/wogikaze/wgkz/mncore/judge/judge-py/mncore2_emuenv/assemble3"


def ok(src):
    p = subprocess.run([ASM, "--instruction-mode", "flat"], input=src.encode(),
                       capture_output=True)
    if p.returncode == 0:
        return True, ""
    err = p.stderr.decode().strip().splitlines()
    return False, (err[-1] if err else "")


WRITERS = {
    "alu imm -> $s108": 'imm f"4" $s108',
    "alu imm -> $r108": 'imm f"4" $r108',
    "mau fvadd -> $s108": 'zero $nowrite; fvadd $r0 $s0 $s108',
    "mau fvadd -> $r108": 'zero $nowrite; fvadd $r0 $s0 $r108',
}
READERS = {
    "mau fvmul reads $s108": 'fvmul $s108 $r0 $nowrite',
    "mau fvmul reads $r108": 'fvmul $r108 $s0 $nowrite',
    "alu ior reads $s108": 'ior $s108 $nowrite',
    "alu ior reads $r108": 'ior $r108 $nowrite',
}
# separate writes and reads by address bank
CASES = []
for wname, wsrc in [("imm->s108", 'imm f"4" $s108'), ("imm->r108", 'imm f"4" $r108')]:
    for rname, rsrc in [("mau reads s108", 'fvmul $s108 $s0 $nowrite'),
                        ("mau reads r108", 'fvmul $r108 $s0 $nowrite')]:
        for gap in range(0, 5):
            prog = '\n'.join([wsrc] + ["nop"] * gap + [rsrc]) + "\n"
            good, err = ok(prog)
            if good:
                print(f"{wname:12s} -> {rname:18s} gap={gap}: OK")
                break
            else:
                print(f"{wname:12s} -> {rname:18s} gap={gap}: {err[-80:]}")
print()
# MAU writer needs a legal 2-step-later source; use two steps then test read gap after the write
for wname, wsrc in [("mau->s108", 'fvpassa $r0 $s108'), ("mau->r108", 'fvpassa $r0 $r108')]:
    for rname, rsrc in [("mau reads s108", 'fvmul $s108 $s0 $nowrite'),
                        ("mau reads r108", 'fvmul $r108 $s0 $nowrite'),
                        ("alu reads s108", 'ior $s108 $nowrite'),
                        ("alu reads r108", 'ior $r108 $nowrite')]:
        for gap in range(0, 5):
            prog = '\n'.join([wsrc] + ["nop"] * gap + [rsrc]) + "\n"
            good, err = ok(prog)
            if good:
                print(f"{wname:12s} -> {rname:18s} gap={gap}: OK")
                break
            else:
                print(f"{wname:12s} -> {rname:18s} gap={gap}: {err[-70:]}")
