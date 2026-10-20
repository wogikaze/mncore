#!/usr/bin/env python3
"""Run a candidate on the native simulator, dump DRAM words 0..4095, diff vs the official expectation."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/"research/experiments/offset-inversion"))
import ref
from mncompile.sim import simulator
TC = ROOT/"problems/challenge/20.fizzbuzz/testcase.vsm"
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
prog = Path(sys.argv[1]).read_text()
tc = TC.read_text(); pre, suf = tc.split(MARK,1)
suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip())+"\n"
sim = simulator(); sim.register("dp",pre); sim.register("ds",suf)
r = sim.run(prog.rstrip("\n")+"\nd getd $d0n0 4096\n", prefix_key="dp", suffix_key="ds")
if r.error:
    print("ERR", r.part, r.line, r.error); raise SystemExit(1)
pieces, out, L, owner = ref.build()
exp = ref.official_expectation()
dr = {a:v for (m,p,a),v in r.dump.items() if m=="DRAM"}
print("DRAM dump keys sample:", sorted(dr)[:3], "pe sample:", sorted({p for (m,p,a) in r.dump if m=="DRAM"})[:3])
got = b"".join(dr[i].to_bytes(8,"big") for i in range(4096))
bad_words = []
bad_bytes = 0
for b in range(4096):
    e = exp[8*b:8*b+8]; g = got[8*b:8*b+8]
    n = sum(1 for i in range(len(e)) if e[i] != g[i])
    if n: bad_words.append((b,n)); bad_bytes += n
print(f"{sys.argv[1]}: wrong bytes={bad_bytes} words={len(bad_words)}")
for b,n in bad_words[:14]:
    lo=8*b
    print(f"  word {b:4d} bytes {lo:5d}..{lo+7:5d} ({n} wrong) exp={exp[lo:lo+8]!r} got={got[lo:lo+8]!r}")
if bad_words:
    print(f"  first={bad_words[0][0]} last={bad_words[-1][0]}")
