#!/usr/bin/env python3
import subprocess
from pathlib import Path
ASM = Path(__file__).resolve().parents[3] / "judge/judge-py/mncore2_emuenv/assemble3"
CASES = [
 ("dmread alone (correct syntax)", 'dmread $lx0 $lr16v'),
 ("dmread + imm", 'dmread $lx0 $lr16v;imm i"7" $s16'),
 ("dmread + lpassa(ALU)", 'dmread $lx0 $lr16v;lpassa $lm0v $ln0v'),
 ("dmread + lpassa + L1BM + L2BM", 'dmread $lx0 $lr16v;lpassa $lm0v $ln0v;l1bmd $lr0v $lb0;l2bmd $lb64 $lc0'),
 ("dvpassa + dmread (both d)", 'dvpassa $ls16v $ls24v;dmread $lx0 $lr16v'),
 ("dmwrite + dmread (both d)", 'dmwrite $ls16v $ly0;dmread $lx0 $lr16v'),
 ("calc+mwrite+mread rejected", 'dvpassa $ls16v $ls24v;dmwrite $ls32v $ly0;dmread $lx0 $lr48v'),
 ("dmread two dests", 'dmread $lx0 $lr16v $ls16v'),
]
def run(src):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(src+"\n").encode(), capture_output=True)
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")
for label, src in CASES:
    rc, out, err = run(src)
    if rc == 0:
        j = sum(1 for l in out.splitlines() if l[:1]=="j"); m = sum(1 for l in out.splitlines() if l[:1]=="m")
        print(f"OK   {label:40s} j={j} m={m} words={j+m}")
    else:
        msg = next((l.strip() for l in err.splitlines() if l.strip()), "")
        print(f"FAIL {label:40s} {msg}")
