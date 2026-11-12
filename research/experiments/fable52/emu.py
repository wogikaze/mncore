#!/usr/bin/env python3
"""Run a VSM snippet (may contain `d get`) through the official assembler + emulator.

    python3 emu.py file.vsm            # print dump lines
    echo '...' | python3 emu.py -      # from stdin

Prints assembler errors, word count (j+m) and the emulator's debug dump lines.
"""
import subprocess, sys, re, os
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"

def run(text, zero=True, quiet=False):
    p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
    if p.returncode != 0:
        return None, "ASM-FAIL: " + (p.stderr.strip().splitlines()[-1] if p.stderr.strip() else "?"), 0
    asm = p.stdout
    words = sum(1 for l in asm.splitlines() if l.startswith(("j ", "m ")))
    args = [str(EMU / "gpfn3_package_main")]
    if zero:
        args += ["--offchip-memory-init", "zero"]
    env = dict(os.environ); env["OMP_THREAD_LIMIT"] = "1"
    q = subprocess.run(args, input=asm, text=True, capture_output=True, env=env)
    if q.returncode != 0:
        return None, "EMU-FAIL: " + (q.stderr + q.stdout).strip()[-600:], words
    return q.stderr, None, words

if __name__ == "__main__":
    src = sys.stdin.read() if sys.argv[1] == "-" else Path(sys.argv[1]).read_text()
    out, err, words = run(src)
    print(f"words={words}")
    if err:
        print(err); sys.exit(1)
    for line in out.splitlines():
        # strip trailing '#d get ...' echo for brevity
        print(line.split(" #")[0])
