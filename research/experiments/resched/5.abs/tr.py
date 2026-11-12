#!/usr/bin/env python3
"""Trace on official emulator (int32). usage: tr.py cand.vsm "ln0:44,lr0:44" m0p0[,m1p0] [steps|all]
   n = number of long words; prints int32 values."""
import subprocess, sys, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
tc = (ROOT / "problems/challenge/5.abs/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======", 1)
src = Path(sys.argv[1]).read_text()
specs = [s.split(":") for s in sys.argv[2].split(",")]
pes = sys.argv[3].split(",")
p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
if p.returncode: print(p.stderr); sys.exit(1)
body = [l for l in p.stdout.splitlines() if l.startswith(("j ", "m "))]
sel = None if len(sys.argv) < 5 or sys.argv[4] == "all" else set(int(x) for x in sys.argv[4].split(","))
text = pre; tags = []
def dump(i):
    global text
    for reg, n in specs:
        for pe in pes:
            text += f"d getd ${reg}n0c0b0{pe} {n}\n"; tags.append((i, reg, pe, int(n)))
dump(0)
for i, l in enumerate(body):
    text += l + "\n"
    if sel is None or i+1 in sel: dump(i+1)
q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True, capture_output=True)
dbg = [l for l in (q.stderr + q.stdout).splitlines() if l.startswith("DEBUG")]
if k0 := 0: pass
k = 0; last = None
srcl = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("#")]
for (w, reg, pe, n) in tags:
    if w != last: print(f"== {w}: {srcl[w-1] if 0 < w <= len(srcl) else ''}"); last = w
    vals = []
    for _ in range(n):
        if k >= len(dbg): print("no dbg"); sys.exit(1)
        line = dbg[k]; k += 1
        m = re.findall(r"[0-9A-Fa-f]{16}", line)
        if m:
            h = m[-1]; a, b = int(h[:8], 16), int(h[8:], 16)
            vals += [str(a - (1<<32) if a >> 31 else a), str(b - (1<<32) if b >> 31 else b)]
        else: vals.append("?" + line[-40:])
    print(f"  {reg:5s} {pe}: {' '.join(vals)}")
if q.returncode: print("EMU ERR", q.stderr[-1500:])
