#!/usr/bin/env python3
"""Dump DRAM contents after running a FizzBuzz solution on the real testcase.

Usage: python3 dump_dram.py <solution.vsm> [--all]
Prints one line per DRAM long word read by the testcase: index value_hex
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
EMUENV = os.path.join(ROOT, "judge", "judge-py", "mncore2_emuenv")
TESTCASE = os.path.join(ROOT, "problems", "challenge", "20.fizzbuzz", "testcase.vsm")
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="


def combine(solution_path):
    tc = open(TESTCASE).read()
    sol = open(solution_path).read()
    assert MARKER in tc
    return tc.replace(MARKER, sol, 1)


def run(vsm):
    p = subprocess.run(
        [EMUENV + "/assemble3", "--instruction-mode", "flat"],
        input=vsm.encode(), capture_output=True,
    )
    if p.returncode != 0:
        sys.stderr.write(p.stderr.decode(errors="replace"))
        raise SystemExit(f"assemble3 failed rc={p.returncode}")
    asm = p.stdout.decode()
    env = os.environ.copy()
    env["OMP_THREAD_LIMIT"] = "1"
    p2 = subprocess.run(
        [EMUENV + "/gpfn3_package_main", "--offchip-memory-init", "zero"],
        input=asm.encode(), capture_output=True, env=env,
    )
    if p2.returncode != 0:
        sys.stderr.write(p2.stderr.decode(errors="replace"))
        raise SystemExit(f"emulator failed rc={p2.returncode}")
    return p2.stderr.decode(errors="replace")


def parse_dram(text):
    out = []
    for line in text.split("\n"):
        m = re.match(r"DEBUG-DRAM\(n0,(\d+)\):\(([^)]*)\)", line)
        if m:
            out.append((int(m.group(1)), m.group(2).strip()))
    return out


def main():
    solution = sys.argv[1]
    show_all = "--all" in sys.argv
    text = run(combine(solution))
    vals = parse_dram(text)
    print(f"# {len(vals)} DRAM words", file=sys.stderr)
    for idx, val in vals:
        if show_all or True:
            print(idx, val)
    if not vals:
        print(text[:2000])


if __name__ == "__main__":
    main()
