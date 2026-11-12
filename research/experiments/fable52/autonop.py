#!/usr/bin/env python3
"""Iteratively insert nops before lines the official assembler reports as hazards."""
import re, subprocess, sys
from pathlib import Path
ASM = Path(__file__).resolve().parents[3] / "judge/judge-py/mncore2_emuenv/assemble3"
def asm(text):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
    return p.returncode, p.stderr
def fix(text, maxit=400):
    lines = text.rstrip("\n").split("\n")
    for it in range(maxit):
        rc, err = asm("\n".join(lines) + "\n")
        if rc == 0:
            return "\n".join(lines) + "\n", it
        m = re.search(r"at line (\d+)", err)
        if not m or not re.search(r"racy|port is unavailable|Consider inserting a nop", err):
            raise RuntimeError(err.strip().splitlines()[-1])
        ln = int(m.group(1)) - 1
        lines.insert(ln, "nop")
    raise RuntimeError("too many iterations")
if __name__ == "__main__":
    t, n = fix(open(sys.argv[1]).read())
    open(sys.argv[2], "w").write(t)
    print("inserted", n, "nops")
