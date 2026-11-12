#!/usr/bin/env python3
"""diff.py <problem> cand.vsm [extra get lines...]: print each mismatching testcase dump (cand vs answer) as floats.
With extra args, also run them as d get lines after the program and print the values."""
import sys, struct, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator
MARK = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
prob = ROOT / "problems" / sys.argv[1]
pre, suf = (prob / "testcase.vsm").read_text().split(MARK, 1)
suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip()) + "\n"
s = simulator()
s.register("dpre", pre)
def f(x): return struct.unpack(">f", struct.pack(">I", x))[0]
def fl(v): return (f(v >> 32), f(v & 0xffffffff))
ref = s.run((prob / "answer.vsm").read_text(), prefix_key="dpre", suffix=suf)
prog = Path(sys.argv[2]).read_text()
r = s.run(prog, prefix_key="dpre", suffix=suf)
print("words", r.words, "err", r.error, r.part, r.line)
if r.dump:
    bad = [k for k in ref.dump if r.dump.get(k) != ref.dump[k]]
    print("mismatch", len(bad), "/", len(ref.dump))
    for k in sorted(bad)[:int(__import__('os').environ.get('N', '40'))]:
        print(k, "got", fl(r.dump.get(k, 0)), "exp", fl(ref.dump[k]))
if len(sys.argv) > 3:
    r2 = s.run(prog, prefix_key="dpre", suffix="\n".join(sys.argv[3:]) + "\n")
    print("err", r2.error)
    for k, v in sorted(r2.dump.items()):
        print(k, f"{v:016x}", fl(v))
