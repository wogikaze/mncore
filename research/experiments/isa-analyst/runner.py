#!/usr/bin/env python3
"""Minimal assemble + emulate harness for MN-Core 2 ISA experiments.

Usage:
    python3 runner.py prog.vsm [--dump 0:4096] [--init zero|unique] [--asm]

  --dump K[:N]   append N `d getd $d<K+i>n0 1` lines (default 1)
  --init MODE    --offchip-memory-init MODE (default zero)
  --asm          skip assemble3, feed the file straight to the emulator

Prints:
    words j=<n> m=<n>
    D<i> = 0x...   for each dumped long word

If assemble3 fails, the assembler stderr is printed and the exit code is 1.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]  # <repo>/research/experiments/isa-analyst -> <repo>
EMUENV = ROOT / "judge/judge-py/mncore2_emuenv"
ASM = EMUENV / "assemble3"
EMU = EMUENV / "gpfn3_package_main"


def assemble(text: str) -> tuple[str, str, int]:
    p = subprocess.run(
        [str(ASM), "--instruction-mode", "flat"],
        input=text.encode(),
        capture_output=True,
    )
    return p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace"), p.returncode


def count_words(asm: str) -> dict[str, int]:
    cnt = {"j": 0, "m": 0}
    for line in asm.splitlines():
        if line[:1] in cnt:
            cnt[line[0]] += 1
    return cnt


def emulate(asm_text: str, init: str) -> tuple[str, str, int, str]:
    with tempfile.TemporaryDirectory() as td:
        inp = Path(td) / "in.asm"
        dmp = Path(td) / "out.dmp"
        inp.write_text(asm_text)
        p = subprocess.run(
            [str(EMU), "-i", str(inp), "-d", str(dmp), "--offchip-memory-init", init],
            capture_output=True,
        )
        dump = dmp.read_text() if dmp.exists() else ""
        return p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace"), p.returncode, dump


DUMP_RE = re.compile(r"DEBUG-DRAM\(n(\d+),(\d+)\):\([^)]*\) \((0x[0-9a-fA-F]+)\)")


def parse_dump(dump: str) -> dict[int, int]:
    out = {}
    for line in dump.splitlines():
        m = DUMP_RE.search(line)
        if m:
            out[int(m.group(2))] = int(m.group(3), 16)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("prog")
    ap.add_argument("--dump", action="append", default=[])
    ap.add_argument("--init", default="zero")
    ap.add_argument("--asm", action="store_true")
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    src = Path(args.prog).read_text()
    if args.asm:
        asm, err, rc = src, "", 0
    else:
        asm, err, rc = assemble(src)
        if rc != 0:
            print(f"ASSEMBLE FAILED rc={rc}")
            print(err.strip())
            return 1
        if err.strip():
            print(f"[assembler stderr] {err.strip()}")
    cnt = count_words(asm)
    print(f"words j={cnt['j']} m={cnt['m']} total={cnt['j']+cnt['m']}")

    dumps: list[tuple[int, int]] = []
    for spec in args.dump:
        if ":" in spec:
            k, n = spec.split(":")
            dumps.append((int(k), int(n)))
        else:
            dumps.append((int(spec), 1))
    suffix = ""
    for k, n in dumps:
        for i in range(k, k + n):
            suffix += f"d getd $d{i}n0 1\n"

    out, err2, rc2, dump = emulate(asm + suffix, args.init)
    if rc2 != 0:
        print(f"EMULATE FAILED rc={rc2}")
        print(err2.strip()[:4000])
        return 1
    vals = parse_dump(dump)
    for k, n in dumps:
        for i in range(k, k + n):
            v = vals.get(i)
            print(f"D{i} = {v:#018x}" if v is not None else f"D{i} = <missing>")
    if err2.strip():
        print(f"[emulator stderr] {err2.strip()[:2000]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
