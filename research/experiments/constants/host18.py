#!/usr/bin/env python3
"""For the L18 imm (`imm i"32" $r25`), try every host line k: put the imm on line k
and delete line 18. Report assemble verdict; run fbcheck on survivors."""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
lines = [l for l in (HERE / "base.vsm").read_text().splitlines() if l.split("#")[0].strip()]
IMM = 'imm i"32" $r25'


def asm(cand):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"],
                       input=("\n".join(cand) + "\n").encode(), capture_output=True)
    if p.returncode == 0:
        return True, ""
    err = [l for l in p.stderr.decode().strip().splitlines() if l.strip()]
    return False, err[-1] if err else "?"


survivors = []
for k in range(1, 94):
    if k == 18:
        continue
    cand = list(lines)
    cand[k - 1] = cand[k - 1] + "; " + IMM
    cand = [l for i, l in enumerate(cand, 1) if i != 18]
    ok, err = asm(cand)
    if ok:
        survivors.append(k)
        path = HERE / f"host18_{k}.vsm"
        path.write_text("\n".join(cand) + "\n")
        p = subprocess.run([sys.executable, str(ROOT / "tools" / "fbcheck.py"), str(path)],
                           capture_output=True, text=True)
        print(f"L{k:3d}: ASM-OK  {(p.stdout + p.stderr).strip().splitlines()[-1]}")
    else:
        print(f"L{k:3d}: FAIL {err[:100]}")
print("survivors:", survivors)
