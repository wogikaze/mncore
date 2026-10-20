#!/usr/bin/env python3
"""Classify answer.vsm lines; try MAU host insertion on every ALU-only line."""
import re
import subprocess
from pathlib import Path

ROOT = Path("/home/wogikaze/wgkz/mncore")
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
BASE = Path(__file__).resolve().parent / "base.vsm"

MAU_PREFIX = ("fvadd", "fvsub", "fvfma", "fvmul", "fvpassa", "hvadd", "hvfma",
              "hvmul", "hvpassa", "dvadd", "dvfma", "dvmul", "dvpassa",
              "fftoi", "ffloor", "fmin", "fmax", "fabs", "fsqrt", "frsqrt",
              "fmfma", "fmmul", "gmfma", "gmmul", "dmfma", "dmmul",
              "bfe", "bfn", "ftoi")
ALU_PREFIX = ("iand", "ior", "ixor", "ilsl", "ilsr", "isub", "iadd", "iinc",
              "idec", "imm", "ipassa", "ladd", "lsub", "lsl", "lsr", "land",
              "lor", "lxor", "lnot", "not", "lpassa", "ipackbit", "iabs",
              "imax", "imin", "msl", "msr", "passa", "zero", "hpassa")
OTHER = ("l1bmd", "l2bmd", "l2bm", "mvd", "mvp", "nop", "noforward", "wait",
         "dmwrite", "dmread", "l1bmm", "l2bmb")


def classify(tok):
    op = tok.split()[0]
    op = op.split("/")[0]
    for p in OTHER:
        if op.startswith(p):
            return p
    for p in MAU_PREFIX:
        if op.startswith(p):
            return "MAU"
    for p in ALU_PREFIX:
        if op.startswith(p):
            return "ALU"
    return "?"


def parse(path):
    lines = []
    for raw in Path(path).read_text().splitlines():
        s = raw.split("#")[0].strip()
        if not s:
            continue
        lines.append(s)
    return lines


def run(src):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=src.encode(),
                       capture_output=True)
    if p.returncode != 0:
        msg = next((l.strip() for l in p.stderr.decode().splitlines() if l.strip()), "")
        return None, msg
    out = p.stdout.decode()
    j = sum(1 for l in out.splitlines() if l[:1] == "j")
    m = sum(1 for l in out.splitlines() if l[:1] == "m")
    return (j, m), ""


lines = parse(BASE)
print(f"{len(lines)} lines")
classes = []
for i, s in enumerate(lines, 1):
    groups = [classify(t.strip()) for t in s.split(";")]
    classes.append(groups)
    print(f"L{i:3d} {','.join(groups):28s} {s}")

alu_only = [i for i, g in enumerate(classes, 1) if g == ["ALU"]]
maumonly = [i for i, g in enumerate(classes, 1) if g == ["MAU"]]
print("\nALU-only lines:", alu_only)
print("MAU-only lines:", maumonly)
