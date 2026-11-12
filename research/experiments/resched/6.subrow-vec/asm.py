#!/usr/bin/env python3
"""Assemble each argument (\\n-separated lines) with the official assembler and print ok/error."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from mncompile.sim import assembler
A = assembler()
for t in sys.argv[1:]:
    t = t.replace('\\n', '\n')
    r = A.assemble(t + '\n')
    print(('OK  ' if r.ok else 'ERR ') + t.replace('\n', ' | ') + ('' if r.ok else '  => ' + (r.error.strip().splitlines()[-1] if r.error else '')))
