#!/usr/bin/env python3
"""Probe the assembler for legal MV forms / operand combinations / size limits."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"


def try_asm(text: str) -> tuple[int, str, str]:
    p = subprocess.run(
        [str(ASM), "--instruction-mode", "flat"], input=text.encode(), capture_output=True
    )
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")


def first_err(stderr: str) -> str:
    for line in stderr.splitlines():
        line = line.strip()
        if line:
            return line
    return ""


def probe(label: str, body: str) -> None:
    rc, out, err = try_asm(body)
    words = out.count("\n")
    if rc == 0:
        print(f"OK   {label:58s} words={words:3d} asm={out.strip()[:40]}")
    else:
        print(f"FAIL {label:58s} {first_err(err)}")


if __name__ == "__main__":
    probes = [l for l in sys.argv[1:]]
    for p in probes:
        probe(p, p + "\n")
