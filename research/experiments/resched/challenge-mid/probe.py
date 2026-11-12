#!/usr/bin/env python3
"""probe.py <problem> <cand.vsm> [dump lines file or '-' for stdin]  -- run with official assembler+emulator, print raw debug output"""
import sys, os, subprocess
sys.path.insert(0, '/home/wogikaze/wgkz/mncore')
from mncompile.sim import assembler, EMU_DIR
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
prob, cand = sys.argv[1], sys.argv[2]
pre, suf = open(f'/home/wogikaze/wgkz/mncore/problems/{prob}/testcase.vsm').read().split(MARKER, 1)
extra = sys.stdin.read() if len(sys.argv) > 3 and sys.argv[3] == '-' else ''
asm = assembler().assemble(open(cand).read())
if not asm.ok:
    print(asm.error); sys.exit(1)
body = "".join(l + "\n" for l in asm.code.splitlines() if l.startswith(("j ", "m ")))
p = subprocess.run([str(EMU_DIR / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=pre + body + extra + (suf if not extra else ''), text=True, capture_output=True)
print(p.stdout[-6000:]); print(p.stderr[-6000:])
