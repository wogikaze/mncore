#!/usr/bin/env python3
"""Assembler + hazard gate (fast, ~0.1 s).

    python3 tools/fbasm.py candidate.vsm

Returns the judge's own assembly step: `assemble3 --instruction-mode flat` on
stdin. If the assembler rejects the program (including instruction-field
conflicts and hazard-checker failures) this exits non-zero and prints the
reason, which the native simulator does NOT model.
"""
from __future__ import annotations
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ASSEMBLER = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"


def assemble(text: str) -> tuple[bool, int, str]:
    run = subprocess.run(
        [str(ASSEMBLER), "--instruction-mode", "flat"],
        input=text, text=True, capture_output=True,
    )
    words = sum(1 for line in run.stdout.splitlines() if line.startswith(("j ", "m ")))
    error = run.stderr.strip().splitlines()[-1] if run.stderr.strip() else ""
    return run.returncode == 0, words, error


def main(argv: list[str]) -> int:
    worst = 0
    for name in argv[1:]:
        ok, words, error = assemble(Path(name).read_text(encoding="utf-8"))
        print(f"{'ASM-OK' if ok else 'ASM-FAIL'} words={words} {name}" + (f": {error}" if not ok else ""))
        worst = max(worst, 0 if ok else 1)
    return worst


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
