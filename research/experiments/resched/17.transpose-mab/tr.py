#!/usr/bin/env python3
"""Trace on official emulator with labelled input.  X[16k+i] = double with high word 0x3FF0kkii (normal, so FP passes keep it) so we can read (k,i).
usage: tr.py cand.vsm [reg:n,...] [mabs] [steps|all]
default: ln0:16 (n = long words) at PE0 of all MABs after each step.  Shows label 'k.i' per long word ('.' = zero)."""
import subprocess, sys, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
src = Path(sys.argv[1]).read_text()
specs = [s.split(":") for s in (sys.argv[2] if len(sys.argv) > 2 else "ln0:16").split(",")]
mabs = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else ",".join(map(str, range(16)))).split(",")]
pre = ""
for k in range(16):
    for i in range(16):
        pre += f"d set $lm{2*i}m{k} 1 {0x3FF00000+k*0x100+i:08X}00000000\n"
p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
if p.returncode: print(p.stderr); sys.exit(1)
body = [l for l in p.stdout.splitlines() if l.startswith(("j ", "m "))]
sel = None if len(sys.argv) < 5 or sys.argv[4] == "all" else set(int(x) for x in sys.argv[4].split(","))
text = pre; tags = []
def dump(i):
    global text
    for reg, n in specs:
        for m in mabs:
            text += f"d getd ${reg}n0c0b0m{m}p0 {n}\n"; tags.append((i, reg, m, int(n)))
for i, l in enumerate(body):
    text += l + "\n"
    if sel is None or i+1 in sel: dump(i+1)
q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True, capture_output=True)
dbg = [l for l in (q.stderr + q.stdout).splitlines() if l.startswith("DEBUG")]
k = 0; last = None
srcl = [l for l in src.splitlines() if l.strip() and not l.strip().startswith("#")]
def lab(h):
    a, b = int(h[:8], 16), int(h[8:], 16)
    if a == 0 and b == 0: return "  . "
    if b == 0 and 0x3FF00000 <= a < 0x3FF01000: return f"{(a>>8)&15:x}.{a&15:x} "[:4].rjust(4)
    return f"?{h[-3:]}"
for (w, reg, m, n) in tags:
    if w != last: print(f"== {w}: {srcl[w-1] if 0 < w <= len(srcl) else ''}"); last = w
    vals = []
    for _ in range(n):
        line = dbg[k]; k += 1
        mm = re.findall(r"[0-9A-Fa-f]{16}", line)
        vals.append(lab(mm[-1]) if mm else "?")
    print(f"  {reg} m{m:2d}: {' '.join(vals)}")
if q.returncode: print("EMU ERR", q.stderr[-1500:])
