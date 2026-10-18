#!/usr/bin/env python3
"""Trace register state at checkpoints inside main.vsm.

Usage:
  python3 trace.py --after 16,25,41 --pe 1,1,7,10,0 [--regs lr0,lt] [solution.vsm]

Inserts d get commands after the given 1-indexed source lines, runs the
combined testcase+solution in the emulator, and prints non-zero dump entries
grouped by checkpoint (in emission order).
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
EMUENV = os.path.join(ROOT, "judge", "judge-py", "mncore2_emuenv")
TESTCASE = os.path.join(ROOT, "problems", "challenge", "20.fizzbuzz", "testcase.vsm")
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="

COUNTS = {"lr0": 64, "ls0": 64, "lm0": 128, "ln0": 128, "lt": 4}
KINDS = {"lr0": "GREG0", "ls0": "GREG1", "lm0": "LM0", "ln0": "LM1", "lt": "TREG"}


def location_suffix(pe_spec):
    if not pe_spec:
        return ""
    g, c, h, m, p = pe_spec.split(",")
    return f"n{g}c{c}b{h}m{m}p{p}"


def run(vsm):
    tc = open(TESTCASE).read()
    combined = tc.replace(MARKER, vsm, 1)
    p = subprocess.run([EMUENV + "/assemble3", "--instruction-mode", "flat"],
                       input=combined.encode(), capture_output=True)
    if p.returncode != 0:
        sys.stderr.write(p.stderr.decode(errors="replace"))
        raise SystemExit("assemble3 failed")
    env = os.environ.copy()
    env["OMP_THREAD_LIMIT"] = "1"
    p2 = subprocess.run([EMUENV + "/gpfn3_package_main", "--offchip-memory-init", "zero"],
                        input=p.stdout, capture_output=True, env=env)
    if p2.returncode != 0:
        sys.stderr.write(p2.stderr.decode(errors="replace"))
        raise SystemExit("emulator failed")
    return p2.stderr.decode(errors="replace")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--after", required=True)
    ap.add_argument("--pe", default="")
    ap.add_argument("--regs", default="lr0,lt")
    ap.add_argument("--showzero", action="store_true")
    ap.add_argument("solution",
                    default=os.path.join(ROOT, "problems", "challenge", "20.fizzbuzz", "main.vsm"),
                    nargs="?")
    args = ap.parse_args()
    after = sorted(int(x) for x in args.after.split(","))
    loc = location_suffix(args.pe)
    regs = [r[1:] if r.startswith("$") else r for r in args.regs.split(",")]
    sol = open(args.solution).read().rstrip("\n").split("\n")
    out = []
    for i, line in enumerate(sol, 1):
        out.append(line)
        if i in after:
            for reg in regs:
                out.append(f"d get ${reg}{loc} {COUNTS[reg]}")
    text = run("\n".join(out) + "\n")
    rx = re.compile(r"DEBUG-(\S+?)\((\S+?),(\d+)\):\s*\([^)]*v:(0x[0-9A-Fa-f]+)\)")
    seq = []  # (kind, addr, value)
    for line in text.split("\n"):
        m = rx.search(line)
        if not m or m.group(1) == "DRAM":
            continue
        seq.append((m.group(1), int(m.group(3)), m.group(4)[2:]))
    idx = 0
    for cp in after:
        print(f"\n===== checkpoint after L{cp} =====")
        for reg in regs:
            kind = KINDS[reg]
            n = COUNTS[reg]
            chunk = seq[idx:idx + n]
            idx += n
            assert len(chunk) == n, f"short dump for {kind} at L{cp}"
            shown = []
            for k, addr, val in chunk:
                if val == "0" and not args.showzero:
                    continue
                words = [val[i:i + 4] for i in range(0, len(val), 4)]
                shown.append(f"    {addr}: {val} [{' '.join(words)}]")
            print(f"  -- {kind} --")
            print("\n".join(shown) if shown else "    (all zero)")


if __name__ == "__main__":
    main()
