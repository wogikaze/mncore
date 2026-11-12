#!/usr/bin/env python3
"""Run testcase inputs + program + extra debug lines on the official emulator. usage: emu.py prog.vsm [dbg.vsm]"""
import sys, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
E = ROOT/"judge/judge-py/mncore2_emuenv"
tc = (ROOT/"problems/challenge/6.fadd-mul/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======")
prog = Path(sys.argv[1]).read_text()
dbg = Path(sys.argv[2]).read_text() if len(sys.argv) > 2 else ""
text = pre + "\n" + prog + "\n" + dbg
a = subprocess.run([str(E/"assemble3"), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
if a.returncode:
    print("ASM ERR", a.stderr[-2000:]); sys.exit(1)
r = subprocess.run([str(E/"gpfn3_package_main"), "--offchip-memory-init", "zero"], input=a.stdout, text=True, capture_output=True)
print(r.stdout[-20000:]); print(r.stderr[-3000:])
