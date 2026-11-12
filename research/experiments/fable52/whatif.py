#!/usr/bin/env python3
"""What-if lower bounds: drop / retype ops of a gen8 op list and re-solve the port-free relaxation."""
import sys, json, copy
import gen8, relax2, sched3
cfg = json.load(open(sys.argv[1]))
cfg.update(o_tabalu=0, o_vreg=1, o_ubf=1)
g = gen8.G(cfg)
def variant(ops, free_units=(), drop_imm=(), extra_mau=0, drop=()):
    ops = copy.deepcopy(ops)
    out = []
    dropped = set()
    for o in ops:
        if any(d in o["dst"] for d in drop):
            dropped.update(o["dst"]); continue
        if any(d in o["dst"] for d in free_units):
            o["unit"] = "mw"                 # not limited in relax2
        if any(d in o["dst"] for d in drop_imm) and o["unit"] == "imm":
            o["unit"] = "mau"                # derived by one MAU op (optimistic: no extra deps)
        out.append(o)
    for o in out:
        o["src"] = [s for s in o["src"] if s[0] not in dropped]
    for k in range(extra_mau):
        out.append(sched3.op(f"fvpassa $lr0 >$lr{200 + 2 * k}", "mau", [f"xtra{k}"]))
    return out
def bound(ops, label):
    r = relax2.relaxed(ops, timeout=25)
    ra = relax2.relaxed(ops, units=(("alu", "imm"), ("l1",)), timeout=25)
    rm = relax2.relaxed(ops, units=(("mau",), ("l1",)), timeout=25)
    print(f"{label:60s} all {r[0]} {'opt' if r[1] else '?'}  alu-only {ra[0]}  mau-only {rm[0]}")
T = ("tE1", "tE2", "tT1", "tT2")
bound(g.OPS, "gen8 baseline")
bound(variant(g.OPS, free_units=T), "tables on matrix units (free)")
bound(variant(g.OPS, free_units=T, drop_imm=("X", "DY"), extra_mau=2), "+ X, DY derived (2 MAU each)")
bound(variant(g.OPS, free_units=T, drop_imm=("X", "DY", "H1516"), extra_mau=3), "+ X, DY, H1516 derived")
bound(variant(g.OPS, free_units=T, drop_imm=("X", "DY", "H1516", "H8"), extra_mau=4), "+ X, DY, H1516, H8 derived")
bound(variant(g.OPS, free_units=T, drop_imm=("X", "DY", "H1516", "H8", "DX"), extra_mau=6), "+ ... DX derived")

def show(ops):
    L, opt, tv = relax2.relaxed(ops, timeout=40)
    print("bound", L, opt)
    rows = {}
    for i, o in enumerate(ops): rows.setdefault(tv[i], []).append(o)
    for t in range(L):
        r = rows.get(t, [])
        a = [o for o in r if o["unit"] in ("alu", "imm")]
        mm = [o for o in r if o["unit"] == "mau"]
        oth = [o for o in r if o["unit"] not in ("alu", "imm", "mau")]
        print(f"{t+1:2d} A: {(a[0]['unit'] + ' ' + ','.join(a[0]['dst'])) if a else '--':24s} | M: {(','.join(mm[0]['dst'])) if mm else '--':10s} | " + " ; ".join(','.join(o['dst']) for o in oth))
if len(sys.argv) > 2:
    show(variant(g.OPS, free_units=T, drop_imm=("X", "DY", "H1516", "H8"), extra_mau=4))
