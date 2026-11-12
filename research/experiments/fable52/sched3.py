#!/usr/bin/env python3
"""Backward list scheduler for MN-Core PE expressions (v3).

op(text, unit, dst, src, fwd, prio)
  text : expression; destinations are marked with a leading '>' (removed when rendering)
  unit : 'alu' | 'imm' | 'mau' | 'mw' | 'mr' | 'l1' | 'l2'
  dst  : value names defined by the op
  src  : list of (value, file[, lat]) register dependencies; lat defaults to 2 (3 if the producer is an imm)
  fwd  : value name(s) read through $aluf/$mauf/$mreadf/$lbf: producer is exactly one line earlier

The scheduler works in reversed time (tau = 0 is the last line): an op is placed once all its
consumers are placed, as late as possible in forward time.  Forwarding links make rigid groups.
Port model per line: one distinct read pattern and one write per register file, LM0/LM1 never
read and written on the same line, an LM write blocks reads of that LM for the next 2 lines,
imm excludes LM0 access, at most one mask entry per line.
"""
import re, random

def op(text, unit, dst=(), src=(), fwd=(), prio=0, at=()):
    """at: list of (value, delta): this op sits exactly delta lines after the producer of value (timing link only)."""
    if isinstance(fwd, str): fwd = [fwd]
    return dict(text=text, unit=unit, dst=list(dst), src=[tuple(s) for s in src], fwd=list(fwd or []), prio=prio,
                at=[tuple(a) for a in at])

OPND = re.compile(r"-?\$(l?l?)([rsmnt])(t?)(\[[^\]]*\]|\d*)(v\d*)?(e)?")
MASK = re.compile(r"/(?:\$(?:ll)?imr(\d+)|([01]{4})(?![0-9]))")

def operand_info(text):
    reads, writes = [], []
    for tok in text.split():
        isdst = tok.startswith(">")
        tok = tok.lstrip(">")
        if "/" in tok: tok = tok.split("/")[0]
        if isdst and tok.startswith("$omr"):
            writes.append(("o", tok)); continue
        m = OPND.fullmatch(tok)
        if not m: continue
        f = m.group(2)
        key = m.group(1) + m.group(3) + m.group(4) + (m.group(5) or "") + (m.group(6) or "")
        (writes if isdst else reads).append((f, key))
    masks = set(a or ("f" + b) for a, b in MASK.findall(text))      # variable entry number or fixed per-cycle pattern
    zf = bool(re.match(r"\S+/\$", text))
    return reads, writes, masks, zf

class Line:
    __slots__ = ("alu", "mau", "mw", "mr", "l1", "l2", "reads", "writes", "imm", "masks", "zf", "ops")
    def __init__(self):
        self.alu = self.mau = self.mw = self.mr = self.l1 = self.l2 = 0
        self.reads = {}; self.writes = {}; self.imm = False; self.masks = set(); self.zf = False; self.ops = []

INFO = {}
def info(o):
    k = o["text"]
    if k not in INFO: INFO[k] = operand_info(k)
    return INFO[k]

MATREG = re.compile(r"\$l+([xy])\d*")
def mat_ok(a, b):
    """extra rules between two ops of one line: a matrix register appears once; fvfma/fvmul next to an
    mwrite must have the mwrite source as its second operand (same sign / extension)."""
    ta, tb = a["text"], b["text"]
    if set(MATREG.findall(ta)) & set(MATREG.findall(tb)): return False
    for x, y in ((a, b), (b, a)):
        if x["unit"] == "mw" and y["unit"] == "mau":
            ty = y["text"].replace(">", "").split()
            if ty[0].split("/")[0] in ("fvfma", "fvmul") and ty[2] != x["text"].replace(">", "").split()[1]: return False
    return True

def fits(lines, tau, o):
    """can op o go on reversed line tau?  lines: dict tau -> Line"""
    L = lines.get(tau)
    u = o["unit"]
    reads, writes, masks, zf = info(o)
    if L is not None and (u in ("mw", "mr") or L.mw or L.mr):
        for p in L.ops:
            if not mat_ok(p, o): return False
    if L is not None:
        if u in ("alu", "imm") and L.alu: return False
        if u == "mau" and L.mau: return False
        if u == "mw" and L.mw: return False
        if u == "mr" and L.mr: return False
        if u in ("mau", "mw", "mr") and (L.mau + L.mw + L.mr) >= 2: return False
        if u == "l1" and L.l1: return False
        if u == "l2" and L.l2: return False
        if u == "imm" and ("m" in L.reads or "m" in L.writes): return False
        if L.imm and any(f == "m" for f, _ in reads + writes): return False
        if masks and L.masks and masks != L.masks: return False
        if len(masks) > 1: return False
        if zf and L.zf: return False
        for f, k in reads:
            if f in L.reads and L.reads[f] != k: return False
        for f, k in writes:
            if f in L.writes: return False
        for f in ("m", "n"):
            r = any(x[0] == f for x in reads); w = any(x[0] == f for x in writes)
            if (r and f in L.writes) or (w and f in L.reads): return False
    rd = {}
    for f, k in reads:
        if f in rd and rd[f] != k: return False
        rd[f] = k
    if len({f for f, _ in writes}) != len(writes): return False
    for f in ("m", "n"):
        r = any(x[0] == f for x in reads); w = any(x[0] == f for x in writes)
        if r and w: return False
        # a write at forward t blocks reads at t+1, t+2  <=>  reversed: write at tau_r+1, tau_r+2
        if r:
            for d in (1, 2):
                M = lines.get(tau + d)
                if M is not None and f in M.writes: return False
        if w:
            for d in (1, 2):
                M = lines.get(tau - d)
                if M is not None and f in M.reads: return False
    return True

def take(lines, tau, o):
    L = lines.setdefault(tau, Line())
    u = o["unit"]
    if u in ("alu", "imm"): L.alu = 1
    if u == "imm": L.imm = True
    if u in ("mau", "mw", "mr", "l1", "l2"): setattr(L, u, 1)
    reads, writes, masks, zf = info(o)
    for f, k in reads: L.reads[f] = k
    for f, k in writes: L.writes[f] = k
    L.masks |= masks; L.zf = L.zf or zf
    L.ops.append(o)

UNIT_ORDER = {"imm": 0, "alu": 0, "mau": 1, "mw": 2, "mr": 3, "l1": 4, "l2": 5}

def prepare(ops, lat=2, imm_lat=3):
    n = len(ops)
    producer = {}
    for i, o in enumerate(ops):
        for d in o["dst"]:
            assert d not in producer, f"value {d} defined twice"
            producer[d] = i
    for i, o in enumerate(ops):
        for v in o["fwd"]: assert v in producer, f"unknown fwd value {v} in {o['text']}"
        for s in o["src"]: assert s[0] in producer, f"unknown src value {s[0]} in {o['text']}"
    # rigid groups via forwarding links: line(c) = line(p) + 1  (forward time)
    off = {}; grp = {}
    adj = {i: [] for i in range(n)}
    for c, o in enumerate(ops):
        for v in o["fwd"]:
            p = producer[v]
            adj[c].append((p, -1)); adj[p].append((c, +1))
        for v, d in o.get("at", ()):
            p = producer[v]
            adj[c].append((p, -d)); adj[p].append((c, +d))
    groups = []
    for i in range(n):
        if i in grp: continue
        g = len(groups); grp[i] = g; off[i] = 0; stack = [i]; mem = [i]
        while stack:
            a = stack.pop()
            for b, d in adj[a]:
                if b in grp:
                    assert off[b] == off[a] + d, f"inconsistent forwarding around {ops[b]['text']}"
                else:
                    grp[b] = g; off[b] = off[a] + d; stack.append(b); mem.append(b)
        mx = max(off[m] for m in mem)
        for m in mem: off[m] = mx - off[m]          # reversed offset inside the group (0 = last line)
        groups.append(mem)
    # dependencies (consumer c needs producer p at least L lines earlier)
    deps = []            # (p, c, L)
    for c, o in enumerate(ops):
        for s in o["src"]:
            p = producer[s[0]]
            L = s[2] if len(s) > 2 else (imm_lat if ops[p]["unit"] == "imm" else lat)
            deps.append((p, c, L))
    for p, c, L in deps:
        if grp[p] == grp[c]:
            assert off[p] - off[c] >= L, f"rigid group violates latency: {ops[p]['text']} -> {ops[c]['text']}"
    return producer, grp, off, groups, deps

def schedule(ops, lat=2, imm_lat=3, noise=0.0, seed=0, prep=None):
    rnd = random.Random(seed)
    producer, grp, off, groups, deps = prep or prepare(ops, lat, imm_lat)
    ng = len(groups)
    # group-level DAG: gp -> gc with reversed-time lower bounds
    cons = {g: [] for g in range(ng)}      # consumers of group g: (gc, need) with tau_start(g) >= tau_start(gc) + need
    npred_unplaced = {g: set() for g in range(ng)}
    for p, c, L in deps:
        gp, gc = grp[p], grp[c]
        if gp == gc: continue
        # tau(p) >= tau(c) + L ; tau(x) = start(g) + off[x]
        cons[gp].append((gc, off[c] + L - off[p]))
        npred_unplaced[gp].add(gc)
    # depth = longest chain of ancestors (how much must precede the group), for priority
    preds = {g: [] for g in range(ng)}
    for gp in range(ng):
        for gc, need in cons[gp]: preds[gc].append((gp, need))
    depth = {}
    def dp(g):
        if g in depth: return depth[g]
        depth[g] = -1
        span = max(off[m] for m in groups[g])
        best = span
        for gp, need in preds[g]:
            best = max(best, dp(gp) + need)
        depth[g] = best + max(ops[m]["prio"] for m in groups[g])
        return depth[g]
    for g in range(ng): dp(g)
    key = {g: depth[g] + rnd.random() * noise for g in range(ng)}
    lines = {}
    start = {}
    waiting = {g: set(npred_unplaced[g]) for g in range(ng)}
    ready = [g for g in range(ng) if not waiting[g]]
    rev_cons = {g: [] for g in range(ng)}
    for gp in range(ng):
        for gc, need in cons[gp]: rev_cons[gc].append(gp)
    while ready:
        ready.sort(key=lambda g: -key[g])
        g = ready.pop(0)
        lo = 0
        for gc, need in cons[g]:
            lo = max(lo, start[gc] + need)
        t = lo
        while True:
            ok = True
            placed_tmp = []
            for m in groups[g]:
                if not fits(lines, t + off[m], ops[m]): ok = False; break
            if ok:
                # ops of the same group on the same line must also be mutually compatible
                tmp = {}
                for m in sorted(groups[g], key=lambda m: off[m]):
                    tau = t + off[m]
                    if not fits(tmp, tau, ops[m]): ok = False; break
                    take(tmp, tau, ops[m])
            if ok: break
            t += 1
            if t > 400: raise RuntimeError("overflow")
        for m in groups[g]: take(lines, t + off[m], ops[m])
        start[g] = t
        for gp in set(rev_cons[g]):
            waiting[gp].discard(g)
            if not waiting[gp] and gp not in start and gp not in ready: ready.append(gp)
    assert len(start) == ng, "cyclic dependencies"
    T = max(lines)
    out = []
    for tau in range(T, -1, -1):
        L = lines.get(tau)
        out.append(sorted(L.ops, key=lambda o: UNIT_ORDER[o["unit"]]) if L else [])
    line_of = {}
    for g in range(ng):
        for m in groups[g]: line_of[m] = T - (start[g] + off[m])
    return out, line_of

def render(lines):
    out = []
    for l in lines:
        out.append("; ".join(o["text"].replace(">", "") for o in l) if l else "nop")
    return "\n".join(out) + "\n"

def best_schedule(ops, tries=50, noise=4.0, seed0=0, verbose=False):
    prep = prepare(ops)
    best = None
    for k in range(tries):
        try:
            lines, line_of = schedule(ops, noise=noise if k else 0.0, seed=seed0 + k, prep=prep)
        except RuntimeError:
            continue
        if best is None or len(lines) < len(best[0]):
            best = (lines, line_of, seed0 + k)
            if verbose: print("  try", k, "lines", len(lines))
    return best
