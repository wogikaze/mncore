#!/usr/bin/env python3
import sys
sys.path.insert(0, '/home/wogikaze/wgkz/mncore')
from mncompile.sim import assembler
txt = sys.stdin.read() if len(sys.argv) < 2 else open(sys.argv[1]).read()
r = assembler().assemble(txt)
print("OK" if r.ok else "ERR: " + (r.error.strip().splitlines()[-1] if r.error else ''), r.words)
