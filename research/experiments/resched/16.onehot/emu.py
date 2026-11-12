#!/usr/bin/env python3
"""Run testcase inputs + program (+ debug lines) on the official emulator.
usage: emu.py prog.vsm [dbg.vsm] [--lines N]"""
import sys, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
E = ROOT/"judge/judge-py/mncore2_emuenv"
tc = (ROOT/"problems/16.onehot/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======")
args=[a for a in sys.argv[1:]]
n=None
if "--lines" in args:
    i=args.index("--lines"); n=int(args[i+1]); del args[i:i+2]
prog = Path(args[0]).read_text().splitlines()
if n is not None: prog=prog[:n]
dbg = Path(args[1]).read_text() if len(args) > 1 else ""
text = pre + "\n" + "\n".join(prog) + "\n" + dbg
a = subprocess.run([str(E/"assemble3"), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
if a.returncode:
    print("ASM ERR", a.stderr[-2000:]); sys.exit(1)
r = subprocess.run([str(E/"gpfn3_package_main"), "--offchip-memory-init", "zero"], input=a.stdout, text=True, capture_output=True)
print(r.stdout); print(r.stderr)
