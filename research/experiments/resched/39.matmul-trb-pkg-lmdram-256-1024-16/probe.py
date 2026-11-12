#!/usr/bin/env python3
"""probe.py prog.vsm "getline" ... : run program after testcase inputs, print dumped long words."""
import sys, struct
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator
P = ROOT/"problems/39.matmul-trb-pkg-lmdram-256-1024-16/testcase.vsm"
pre = P.read_text().split("# ======= YOUR VSM WILL BE INSERTED HERE =======")[0]
prog = Path(sys.argv[1]).read_text()
gets = "\n".join(sys.argv[2:]) + "\n"
s = simulator()
s.register("probe39pre", pre)
r = s.run(prog, prefix_key="probe39pre", suffix=gets)
print("words", r.words, "err", r.error, r.part, r.line)
def f(x): return struct.unpack(">f", struct.pack(">I", x))[0]
def h(x): return struct.unpack(">e", struct.pack(">H", x))[0]
for k, v in sorted(r.dump.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])):
    hi, lo = v >> 32, v & 0xffffffff
    hs = [h((v >> s_) & 0xffff) for s_ in (48, 32, 16, 0)]
    print(k, f"{v:016x}", "f:", f(hi), f(lo), "h:", hs)
