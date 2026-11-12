#!/usr/bin/env python3
"""Run candidate(s) on the official emulator with the 14.exp testcase; report max |actual-expect| and margin."""
import subprocess, sys, os, re, struct
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
def run(src, tc=ROOT / "problems/14.exp/testcase.vsm"):
    pre, suf = Path(tc).read_text().split(MARK, 1)
    p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
    if p.returncode: return None, p.stderr.strip().splitlines()[-1]
    body = "".join(l + "\n" for l in p.stdout.splitlines() if l.startswith(("j ", "m ")))
    q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=pre + body + suf,
                       text=True, capture_output=True, env={**os.environ, "OMP_THREAD_LIMIT": "1"})
    exp = []
    for l in suf.splitlines():
        m = re.search(r"expect=\[([^\]]*)\]", l)
        if m: exp.append([float(v) for v in m[1].split(",")])
    act = []
    for l in (q.stderr + q.stdout).splitlines():
        if l.startswith("DEBUG-LM1"):
            m = re.search(r"\) \(0x([0-9a-fA-F]+)\)", l)
            v = int(m[1], 16)
            act.append([struct.unpack('>f', struct.pack('>I', v >> 32))[0], struct.unpack('>f', struct.pack('>I', v & 0xffffffff))[0]])
    errs = [abs(a - e) for A, E in zip(act, exp) for a, e in zip(A, E)]
    return errs, None
if __name__ == "__main__":
    for f in sys.argv[1:]:
        errs, e = run(Path(f).read_text())
        if errs is None: print(f, "ASM", e); continue
        errs_s = sorted(errs)
        print(f, "n=%d max=%.3e bad=%d top5=%s" % (len(errs), errs_s[-1], sum(x > 1e-6 for x in errs), ["%.2e" % x for x in errs_s[-5:]]))
