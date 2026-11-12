#!/usr/bin/env python3
"""print a jopt solution as a table: jshow.py <sol.json> [build opts k=v ...]"""
import sys, json, jopt
res = json.load(open(sys.argv[1]))
kv = dict(a.split("=") for a in sys.argv[2:])
S = jopt.build(**{k: bool(int(v)) for k, v in kv.items()})
rows = {}
for o in S.ops: rows.setdefault(res["t"][o.name], []).append(o)
for k in range(1, res["lines"] + 1):
    r = rows.get(k, [])
    a = [o for o in r if o.unit in ("alu", "imm")]; m = [o for o in r if o.unit == "mau"]; l = [o for o in r if o.unit == "l1"]
    def d(o):
        fs = "".join(sorted({f for v, _ in o.writes for f in res["st"][v]}))
        rs = "".join(res["ru"].get(f"{o.name}:{i}") or "-" for i in range(len(o.reads)))
        return f"{o.name}[{rs}>{fs}]" + ("*" if res.get("um", {}).get(o.name) else "")
    print(f"{k:2d} A: {d(a[0]) if a else '--':22s} M: {d(m[0]) if m else '--':22s} {d(l[0]) if l else ''}")
print({v: "".join(f) for v, f in res["st"].items() if len(f) != 1})
