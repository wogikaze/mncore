#!/usr/bin/env python3
"""Candidate builder/checker for constants experiments.

Applies a named transformation to base.vsm, writes cand_<name>.vsm, then runs
fbasm.py and fbcheck.py.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = HERE / "base.vsm"

BASE_LINES = [l for l in BASE.read_text().splitlines() if l.split("#")[0].strip()]


def build(repl=None, delete=(), append=None, name="cand"):
    lines = list(BASE_LINES)
    for ln, new in (repl or {}).items():
        lines[ln - 1] = new
    lines = [l for i, l in enumerate(lines, 1) if i not in delete]
    if append:
        lines.extend(append)
    path = HERE / f"{name}.vsm"
    path.write_text("\n".join(lines) + "\n")
    return path


def check(path, verify=False):
    print(f"--- {path.name}")
    for tool, args in (("fbasm.py", []), ("fbcheck.py", [])):
        p = subprocess.run([sys.executable, str(ROOT / "tools" / tool), str(path)],
                           capture_output=True, text=True)
        out = (p.stdout + p.stderr).strip()
        print(f"  {tool}: {out}")
    if verify:
        p = subprocess.run([sys.executable, str(ROOT / "tools" / "fbverify.py"), str(path)],
                           capture_output=True, text=True)
        print(f"  fbverify: {(p.stdout + p.stderr).strip()}")


if __name__ == "__main__":
    # V1: 63.0 synthesized by two co-issued MAU ops on L18/L19 (which hold the
    # 32/408/4672 imms); imm-only line L26 deleted; L27/L36 read the new word.
    repl = {
        18: 'imm i"32" $r25; fvmul $r108 $s108 $s160',
        19: 'imm i"408" $r26; fvfma $mauf $s108 -$r102 $s164',
        27: 'fvadd $s164 $r116 $s[8,8,3,8]/$imr1; imm ui"0x4b000030" $lr12',
        36: 'fvfma $s164 -$aluf $n1 $nowrite; imm ui"0x4b00007a" $r[65,66,69,70]',
    }
    p = build(repl, delete={26}, name="cand_v1_63mau")
    check(p)
