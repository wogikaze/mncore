#!/usr/bin/env python3
import sys, json, importlib, relax2
gen = importlib.import_module(sys.argv[1])
cfg = json.load(open(sys.argv[2]))
for kv in sys.argv[3:]:
    k, v = kv.split("="); cfg[k] = int(v) if v.isdigit() else v
g = gen.G(cfg)
L, opt, tv = relax2.relaxed(g.OPS, timeout=40)
print("bound", L, opt, "viol", g.viol)
rows = {}
for i, o in enumerate(g.OPS): rows.setdefault(tv[i], []).append(o)
for t in range(L):
    r = rows.get(t, [])
    a = [o for o in r if o["unit"] in ("alu", "imm")]
    mm = [o for o in r if o["unit"] == "mau"]
    oth = [o for o in r if o["unit"] not in ("alu", "imm", "mau")]
    print(f"{t+1:2d} A: {(a[0]['unit'] + ' ' + ','.join(a[0]['dst'])) if a else '--':24s} | M: {(','.join(mm[0]['dst'])) if mm else '--':10s} | " + " ; ".join(','.join(o['dst']) for o in oth))
