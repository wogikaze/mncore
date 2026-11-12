#!/usr/bin/env python3
"""asm.py: assemble candidates separated by '----' lines from stdin; print ok/error (hazard probe)."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from mncompile.sim import assembler
for t in sys.stdin.read().split("----\n"):
    if not t.strip(): continue
    r = assembler().assemble(t)
    msg = "OK" if r.ok else (r.error.splitlines()[-1].strip() if r.error else "fail")
    print(msg.replace("what():  ", ""), "|", " / ".join(l.strip() for l in t.strip().splitlines()))
