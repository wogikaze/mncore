#!/usr/bin/env python3
"""Compact trace on official emulator. usage: tr.py cand.vsm "ln0:16,lr0:16" pes(m0p0,m1p0) [words(comma) or all]"""
import subprocess, sys, os, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
tc = (ROOT / "problems/challenge/11.square-sum/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======", 1)
src = Path(sys.argv[1]).read_text()
specs = [s.split(":") for s in sys.argv[2].split(",")]
pes = sys.argv[3].split(",")
p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
if p.returncode: print(p.stderr); sys.exit(1)
body = [l for l in p.stdout.splitlines() if l.startswith(("j ", "m "))]
sel = None if len(sys.argv) < 5 or sys.argv[4] == "all" else set(int(x) for x in sys.argv[4].split(","))
text = pre; tags = []
for i, l in enumerate(body):
    text += l + "\n"
    if sel is None or i+1 in sel:
        for reg, n in specs:
            for pe in pes:
                text += f"d getd ${reg}n0c0b0{pe} {n}\n"; tags.append((i+1, reg, pe, int(n)))
q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True, capture_output=True)
dbg = [l for l in (q.stderr + q.stdout).splitlines() if l.startswith("DEBUG")]
k = 0; last = None
srcl = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("#")]
for (w, reg, pe, n) in tags:
    if w != last: print(f"== {w}: {srcl[w-1] if w-1 < len(srcl) else ''}"); last = w
    vals = []
    for _ in range(n):
        m = re.search(r":\(([^)]*)\)", dbg[k]); k += 1
        vals += [f"{float(x):.4g}" for x in m.group(1).split(",")]
    print(f"  {reg:5s} {pe}: {' '.join(vals)}")
if q.returncode: print("EMU ERR", q.stderr[-1500:])
