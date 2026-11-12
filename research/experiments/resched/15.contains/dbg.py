#!/usr/bin/env python3
"""Run solution in official emulator with extra 'd get' lines.
usage: dbg.py sol.vsm 'K:getspec' ...   (K = insert after K-th solution line, 0-based count of lines before)
"""
import sys, subprocess, re
from pathlib import Path
ROOT = Path('/home/wogikaze/wgkz/mncore')
E = ROOT/'judge/judge-py/mncore2_emuenv'
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
tc = (ROOT/'problems/challenge/15.contains/testcase.vsm').read_text()
pre, suf = tc.split(MARK)
pre = sys.argv[3] if False else pre
sol = Path(sys.argv[1]).read_text().splitlines()
ins = {}
for a in sys.argv[2:]:
    k, s = a.split(':', 1)
    ins.setdefault(int(k), []).append(s)
out = []
for i, l in enumerate(sol):
    for s in ins.get(i, []): out.append(s)
    out.append(l)
for s in ins.get(len(sol), []): out.append(s)
full = pre + "\n".join(out) + "\n"
asm = subprocess.run([str(E/'assemble3'), '--instruction-mode', 'flat'], input=full.encode(), capture_output=True)
if asm.returncode:
    print(asm.stderr.decode()); sys.exit(1)
lines = [l for l in asm.stdout.decode().split('\n') if l.split() and (l.split()[0] in 'jm' or (l.split()[0]=='d'))]
r = subprocess.run([str(E/'gpfn3_package_main'), '--offchip-memory-init', 'zero'], input="\n".join(lines).encode(), capture_output=True)
for l in r.stderr.decode().splitlines():
    print(l)
