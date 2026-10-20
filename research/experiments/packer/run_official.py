#!/usr/bin/env python3
"""Assemble + run one VSM through the official tools, print debug dumps.

Usage: python3 run_official.py <file.vsm> [--dram-dump]
"""
import re, subprocess, sys
from pathlib import Path

def run(path, hazard=False):
    src = Path(path).read_text()
    asm_cmd = ["assemble3", "--instruction-mode", "flat"]
    if not hazard:
        asm_cmd.append("--disable-hazard-checker")
    asm = subprocess.run(asm_cmd, input=src.encode(), capture_output=True)
    if asm.returncode != 0:
        return None, asm.stderr.decode(errors="replace")
    env = {"OMP_THREAD_LIMIT": "1"}
    import os
    e = os.environ.copy(); e.update(env)
    emu = subprocess.run(["gpfn3_package_main", "--offchip-memory-init", "zero"],
                         input=asm.stdout, capture_output=True, env=e)
    return asm.stdout.decode(), emu.stderr.decode(errors="replace") + emu.stdout.decode(errors="replace")

if __name__ == "__main__":
    asm, log = run(sys.argv[1])
    if asm is None:
        print("ASSEMBLE FAILED"); print(log); raise SystemExit(1)
    print(log)
