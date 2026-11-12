#!/usr/bin/env python3
"""Compact trace: tr.py cand.vsm "reg n;reg n" "m0,m2" -> after each word print values (first n words) per MAB, PE0."""
import subprocess, sys, os, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
tc = (ROOT / "problems/challenge/25.hsv2rgb/testcase.vsm").read_text()
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
pre, suf = tc.split(MARK, 1)
src = Path(sys.argv[1]).read_text()
specs = [s.split() for s in sys.argv[2].split(";")]
mabs = sys.argv[3].split(",") if len(sys.argv) > 3 else ["m0"]
pe = sys.argv[4] if len(sys.argv) > 4 else "p0"
p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
if p.returncode:
    print(p.stderr); sys.exit(1)
body = [l for l in p.stdout.splitlines() if l.startswith(("j ", "m "))]
text = pre
for l in body:
    text += l + "\n"
    for reg, n in specs:
        for m in mabs:
            text += f"d getf {reg}n0c0b0{m}{pe} {n}\n"
q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True,
                   capture_output=True, env={**os.environ, "OMP_THREAD_LIMIT": "1"})
lines = [l for l in (q.stderr + q.stdout).splitlines() if l.startswith("DEBUG")]
srcl = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("#")]
k = 0
for i in range(len(body)):
    print(f"=== {i+1}: {srcl[i] if i < len(srcl) else ''}")
    for reg, n in specs:
        for m in mabs:
            vals = []
            for _ in range(int(n)):
                l = lines[k]; k += 1
                mm = re.search(r":\((.*?)\) \((.*?)\)", l)
                vals.append((mm.group(2) if os.environ.get("HEX") else mm.group(1)).replace(" ", ""))
            print(f"   {reg:6s}{m:4s}", " ".join(vals))
if q.returncode: print("EMU ERR", q.stderr[-2000:])
