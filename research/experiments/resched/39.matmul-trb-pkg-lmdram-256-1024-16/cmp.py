#!/usr/bin/env python3
"""cmp.py cand.vsm [n]: show expected vs actual for the first mismatching DRAM long words."""
import sys, struct, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator
P = ROOT/"problems/39.matmul-trb-pkg-lmdram-256-1024-16/testcase.vsm"
pre, suf = P.read_text().split("# ======= YOUR VSM WILL BE INSERTED HERE =======")
exp = []
for l in suf.splitlines():
    m = re.match(r"d getd (\S+) 1 # expect=\[([^,]+), ([^\]]+)\]", l)
    if m: exp.append((m[1], float(m[2]), float(m[3])))
s = simulator(); s.register("cmp39pre", pre)
gets = "\n".join(f"d getd {e[0]} 1" for e in exp) + "\n"
r = s.run(Path(sys.argv[1]).read_text(), prefix_key="cmp39pre", suffix=gets)
print("words", r.words, "err", r.error)
f = lambda x: struct.unpack(">f", struct.pack(">I", x))[0]
vals = [v for k, v in sorted(r.dump.items(), key=lambda kv: (kv[0][1], kv[0][2]))]
# map by order of request is lost; rebuild by key
d = {}
for (mem, pe, addr), v in r.dump.items(): d[(pe, addr)] = v
bad = 0; n = int(sys.argv[2]) if len(sys.argv) > 2 else 10
for name, a, b in exp:
    m = re.match(r"\$d(\d+)n(\d+)", name); addr, grp = int(m[1]), m[2]
    key = [k for k in d if k[1] == addr and k[0].startswith("n" + grp)]
    v = d[key[0]] if key else None
    got = (f(v >> 32), f(v & 0xffffffff)) if v is not None else None
    if got != (a, b):
        bad += 1
        if bad <= n: print(name, "exp", a, b, "got", got)
print("bad", bad, "of", len(exp))
