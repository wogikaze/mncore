#!/usr/bin/env python3
"""Run a candidate on the official emulator with custom inputs (13.exp-low-prec layout).
usage: dense.py cand.vsm [nruns] [lo hi]   -> max |Y-exp(x)| over testcase and over a dense grid.
Grid: nruns*4096 evenly spaced f32 points in [lo,hi] (default [-2,2])."""
import subprocess, sys, os, re, struct
import numpy as np
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
ROOT = Path(__file__).resolve().parents[4]
EMU = ROOT / "judge/judge-py/mncore2_emuenv"
TC = (ROOT / "problems/13.exp-low-prec/testcase.vsm").read_text()
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
pre, suf = TC.split(MARK, 1)
setl = [l for l in pre.splitlines() if l.startswith("d set")]
other = [l for l in pre.splitlines() if not l.startswith("d set")]
setidx = [tuple(map(int, re.findall(r"@\[(\d+),(\d+)\],\[(\d+),(\d+)\]", l)[0])) for l in setl]
getidx = [tuple(map(int, re.findall(r"@\[(\d+),(\d+)\],\[(\d+),(\d+)\]", l)[0])) for l in suf.splitlines() if "expect=" in l]
tcx = {}
for l, (a, b, c, d) in zip(setl, setidx):
    h = l.split()[4]
    tcx[(a, b)] = struct.unpack('>f', bytes.fromhex(h[:8]))[0]; tcx[(c, d)] = struct.unpack('>f', bytes.fromhex(h[8:]))[0]
tcy = {}
for l, (a, b, c, d) in zip([l for l in suf.splitlines() if "expect=" in l], getidx):
    v = [float(s) for s in re.search(r"expect=\[([^\]]*)\]", l)[1].split(",")]
    tcy[(a, b)] = v[0]; tcy[(c, d)] = v[1]
def asm(src):
    p = subprocess.run([str(EMU / "assemble3"), "--instruction-mode", "flat"], input=src, text=True, capture_output=True)
    if p.returncode: raise SystemExit(p.stderr)
    return "".join(l + "\n" for l in p.stdout.splitlines() if l.startswith(("j ", "m ")))
def f2h(v): return struct.pack('>f', v).hex().upper()
def run(body, xs):  # xs: dict (i,j)->f32 ; returns dict (i,j)->output
    lines = []
    for l, (a, b, c, d) in zip(setl, setidx):
        p = l.split()
        lines.append(f"{p[0]} {p[1]} {p[2]} {p[3]} {f2h(xs[(a,b)])+f2h(xs[(c,d)])}")
    text = "\n".join(lines) + "\n" + body + suf
    q = subprocess.run([str(EMU / "gpfn3_package_main"), "--offchip-memory-init", "zero"], input=text, text=True,
                       capture_output=True, env={**os.environ, "OMP_THREAD_LIMIT": "1"})
    out = []
    for l in (q.stderr + q.stdout).splitlines():
        if l.startswith("DEBUG-LM1"):
            v = int(re.search(r"\) \(0x([0-9a-fA-F]+)\)", l)[1], 16)
            out.append((struct.unpack('>f', struct.pack('>I', v >> 32))[0], struct.unpack('>f', struct.pack('>I', v & 0xffffffff))[0]))
    res = {}
    for (a, b, c, d), (u, w) in zip(getidx, out):
        res[(a, b)] = u; res[(c, d)] = w
    return res
if __name__ == "__main__":
    body = asm(Path(sys.argv[1]).read_text())
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    lo, hi = (float(sys.argv[3]), float(sys.argv[4])) if len(sys.argv) > 4 else (-2.0, 2.0)
    r = run(body, tcx)
    e = max(abs(r[k] - tcy[k]) for k in tcy)
    bad = sum(abs(r[k] - tcy[k]) > 0.009 for k in tcy)
    print(f"testcase: max|Y-expect|={e:.6f} bad={bad}")
    keys = sorted(tcx)
    grid = np.linspace(lo, hi, n * len(keys)).astype(np.float32)
    def job(i):
        g = grid[i::n]
        rr = run(body, {k: float(v) for k, v in zip(keys, g)})
        y = np.array([rr[k] for k in keys]); err = np.abs(y - np.exp(g.astype(np.float64)))
        j = err.argmax(); return err[j], float(g[j])
    with ThreadPoolExecutor(2) as ex:
        res = list(ex.map(job, range(n)))
    m = max(res); print(f"grid {n*len(keys)} pts [{lo},{hi}]: max|Y-exp(x)|={m[0]:.6f} at x={m[1]:.6f}")
