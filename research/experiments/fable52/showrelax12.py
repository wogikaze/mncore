#!/usr/bin/env python3
import sys, json, random
import gen12, search12, relax2
base = dict(gen12.DEFAULT)
for k, v in json.load(open("cfg9_55.json")).items():
    if k in base: base[k] = v
c = dict(base); c.update(o_ubf=0, o_tabalu=0, o_mtab=1)
for kv in sys.argv[1:]:
    k, v = kv.split("="); c[k] = int(v)
r = search12.repair(c, random.Random(3), gen=gen12)
g = gen12.G(r)
L, opt, tv = relax2.relaxed(g.OPS, timeout=40)
print("bound", L, opt)
rows = {}
for i, o in enumerate(g.OPS): rows.setdefault(tv[i], []).append(o)
for t in range(L):
    rr = rows.get(t, [])
    a = [o for o in rr if o["unit"] in ("alu", "imm")]
    mm = [o for o in rr if o["unit"] == "mau"]
    oth = [o for o in rr if o["unit"] not in ("alu", "imm", "mau")]
    print(f"{t+1:2d} A: {(a[0]['unit'] + ' ' + ','.join(a[0]['dst'])) if a else '--':24s} | M: {(','.join(mm[0]['dst'])) if mm else '--':10s} | " + " ; ".join(','.join(o['dst']) for o in oth))
