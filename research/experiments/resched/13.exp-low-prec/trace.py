#!/usr/bin/env python3
"""Trace a 14.exp candidate on the official emulator: dump state after every instruction word.

usage: trace.py cand.vsm "dumpspec1;dumpspec2..." [pe-suffix]
  dumpspec e.g. 'getf $s0 16' ; pe suffix default n0c0b0m0p0
"""
import subprocess, sys, os
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
tc = (ROOT / "problems/13.exp-low-prec/testcase.vsm").read_text()
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
pre, suf = tc.split(MARK, 1)
src = Path(sys.argv[1]).read_text()
specs = sys.argv[2].split(";") if len(sys.argv) > 2 else ["getf $s0 16"]
pes = sys.argv[3].split(",") if len(sys.argv) > 3 else ["n0c0b0m0p0"]
p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
if p.returncode:
    print(p.stderr); sys.exit(1)
body = [l for l in p.stdout.splitlines() if l.startswith(("j ", "m "))]
out = []
for i, l in enumerate(body):
    out.append(l)
    out.append(f"d getf $n9999 1")  # marker (will error?)
text = pre
for i, l in enumerate(body):
    text += l + "\n"
    for s in specs:
        op, mem, n = s.split()
        # insert pe path after address
        for pe in pes:
            text += f"d {op} {mem}{pe} {n}\n"
q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True,
                   capture_output=True, env={**os.environ, "OMP_THREAD_LIMIT": "1"})
lines = (q.stderr + q.stdout).splitlines()
dbg = [l for l in lines if l.startswith("DEBUG")]
per = sum(int(x.split()[2]) for x in specs) * len(pes)
srcl = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("#")]
k = 0
for i in range(len(body)):
    print(f"=== after word {i+1}: {srcl[i] if i < len(srcl) else ''}")
    for j in range(per):
        if k < len(dbg):
            print("  ", dbg[k][:400]); k += 1
if q.returncode:
    print("EMU ERR", q.stderr[-2000:])
