#!/usr/bin/env python3
"""Tiny list scheduler for MN-Core PE expressions.

An op is a dict built by op(text, unit, dst=[...], src=[...], fwd=None):
  text : expression text; may contain {aluf}/{mauf}/{mreadf} placeholders resolved by the scheduler
  unit : 'alu' | 'imm' | 'mau' | 'mw' | 'mr' | 'l1' | 'l2'
  dst  : list of value names this op defines (stored in registers given by the text itself)
  src  : list of (value name, regfile) read through registers
  fwd  : value name read through forwarding ($aluf/$mauf/$mreadf); producer must be the
         immediately preceding line
Values defined via forwarding only (nowrite) must be consumed on the next line.
Port model: per line, per register file at most one distinct read operand text and one write.
"""
import re

FILES = {"r": "r", "s": "s", "m": "m", "n": "n", "t": "t"}

def op(text, unit, dst=(), src=(), fwd=None, prio=0):
    return dict(text=text, unit=unit, dst=list(dst), src=list(src), fwd=fwd, prio=prio)

def rd_operands(text):
    """register read operands (file letter, operand text) of an expression (all but dests)."""
    toks = text.replace(";", " ").split()
    return toks

def schedule(ops, lat=2, max_lines=400, fixed=None):
    """chain-aware list scheduler. returns (lines, line_of)."""
    n = len(ops)
    producer = {}
    for i, o in enumerate(ops):
        for d in o["dst"]:
            assert d not in producer, f"value {d} defined twice"
            producer[d] = i
    for i, o in enumerate(ops):
        if not fits(newline(), o):
            raise RuntimeError(f"op {i} cannot be placed even alone: {o['text']}")
    # chains: follow fwd links
    nxt = {}
    for i, o in enumerate(ops):
        if o["fwd"]:
            p = producer[o["fwd"]]
            assert p not in nxt, f"two forwarding consumers of {ops[p]['text']}"
            nxt[p] = i
    heads = [i for i in range(n) if not ops[i]["fwd"]]
    chains = []
    chain_of = {}
    for h in heads:
        c = [h]
        while c[-1] in nxt: c.append(nxt[c[-1]])
        for j in c: chain_of[j] = len(chains)
        chains.append(c)
    ext = []   # external deps per chain
    for c in chains:
        inner = set(c)
        d = set()
        for j in c:
            for v, _ in ops[j]["src"]:
                pi = producer[v]
                if pi not in inner: d.add(pi)
        ext.append(d)
    # priority: longest path (in lines) to the end
    succ = {k: set() for k in range(len(chains))}
    for k, d in enumerate(ext):
        for pi in d: succ[chain_of[pi]].add(k)
    height = {}
    def h(k):
        if k in height: return height[k]
        height[k] = len(chains[k]) + max([h(j) + lat for j in succ[k]] or [0]) + max(ops[i]["prio"] for i in chains[k])
        return height[k]
    for k in range(len(chains)): h(k)
    line_of = {}
    lines = []
    placed = set()
    pending = sorted(range(len(chains)), key=lambda k: -height[k])
    while pending:
        for k in pending:
            if all(pi in line_of for pi in ext[k]): break
        else:
            raise RuntimeError("deadlock")
        c = chains[k]
        t = 0
        while True:
            ok = True
            for j, oi in enumerate(c):
                tj = t + j
                for v, _ in ops[oi]["src"]:
                    pi = producer[v]
                    L = lat + (1 if ops[pi]["unit"] == "imm" else 0)
                    if pi in line_of and line_of[pi] + L > tj: ok = False
                    if pi in c and c.index(pi) + t + lat > tj and ops[oi]["fwd"] != v: ok = False
                if fixed and oi in fixed and tj < fixed[oi]: ok = False
                if not ok: break
                while len(lines) <= tj: lines.append(newline())
                if not fits(lines[tj], ops[oi], lines, tj): ok = False; break
            if ok: break
            t += 1
            if t > max_lines: raise RuntimeError("overflow")
        for j, oi in enumerate(c):
            take(lines[t + j], ops[oi]); line_of[oi] = t + j
        pending.remove(k)
    return [l["ops"] for l in lines], line_of

def newline():
    return dict(alu=0, mau=0, mw=0, mr=0, l1=0, l2=0, reads={}, writes={}, lm0=False, imm=False, ops=[])

OPND = re.compile(r"-?\$(l?l?)([rsmnt])(t?)(\[[^\]]*\]|\d*)(v\d*)?(e)?")

def operand_info(text):
    """(reads, writes, lm0) from expression text using convention: last k operands are dests.
    We mark dests by a leading '>' in the text, e.g. 'fvadd $lr0v $ls8 >$lr16v'."""
    reads, writes = [], []
    lm0 = False
    for tok in text.split():
        isdst = tok.startswith(">")
        tok = tok.lstrip(">")
        if "/" in tok: tok = tok.split("/")[0]
        m = OPND.fullmatch(tok)
        if not m: continue
        f = m.group(2)
        if f == "m": lm0 = True
        key = m.group(3) + m.group(4) + (m.group(5) or "")
        (writes if isdst else reads).append((f, key))
    return reads, writes, lm0

def fits(L, o, lines=None, t=None):
    u = o["unit"]
    if u in ("alu", "imm") and L["alu"]: return False
    if u == "mau" and L["mau"]: return False
    if u == "mw" and L["mw"]: return False
    if u == "mr" and L["mr"]: return False
    if u in ("mau", "mw", "mr") and (L["mau"] + L["mw"] + L["mr"]) >= 2: return False
    if u == "l1" and L["l1"]: return False
    if u == "l2" and L["l2"]: return False
    reads, writes, lm0 = operand_info(o["text"])
    if u == "imm" and L["lm0"]: return False
    if lm0 and L["imm"]: return False
    for f, k in reads:
        if f in L["reads"] and L["reads"][f] != k: return False
    rd = {}
    for f, k in reads:
        if f in rd and rd[f] != k: return False
        rd[f] = k
    for f, k in writes:
        if f in L["writes"]: return False
    if lines is not None:
        for f in ("m", "n"):
            if any(r[0] == f for r in reads):
                for dt in (1, 2):
                    if t - dt >= 0 and f in lines[t - dt]["writes"]: return False
            if any(w[0] == f for w in writes):
                for dt in (1, 2):
                    if t + dt < len(lines) and f in lines[t + dt]["reads"]: return False
    for f in ("m", "n"):
        if f in L["reads"] and any(w[0] == f for w in writes): return False
        if f in L["writes"] and any(r[0] == f for r in reads): return False
        if any(w[0] == f for w in writes) and any(r[0] == f for r in reads): return False
    return True

def take(L, o):
    u = o["unit"]
    if u in ("alu", "imm"): L["alu"] = 1
    if u == "imm": L["imm"] = True
    if u in ("mau", "mw", "mr"): L[u] = 1
    if u in ("l1", "l2"): L[u] = 1
    reads, writes, lm0 = operand_info(o["text"])
    if lm0: L["lm0"] = True
    for f, k in reads: L["reads"][f] = k
    for f, k in writes: L["writes"][f] = k
    L["ops"].append(o["text"].replace(">", ""))

def render(lines):
    out = []
    for l in lines:
        out.append("; ".join(l) if l else "nop")
    return "\n".join(out) + "\n"

def schedule2(ops, lat=2, imm_lat=3):
    """non-imm ops first (constants assumed ready), then imms inserted into free ALU slots
    (earliest-deadline-first); prepend lines if needed."""
    imm_ids = [i for i, o in enumerate(ops) if o["unit"] == "imm"]
    imm_vals = {}
    for i in imm_ids:
        for d in ops[i]["dst"]: imm_vals[d] = i
    # strip imm deps (but keep ordering deps between imms)
    core = []
    remap = {}
    for i, o in enumerate(ops):
        if o["unit"] == "imm": continue
        o2 = dict(o); o2["src"] = [(v, f) for v, f in o["src"] if v not in imm_vals]
        remap[len(core)] = i; core.append(o2)
    for pre in range(0, 40):
        lines, line_of = schedule(core, lat=lat, fixed={k: pre for k in range(len(core))})
        L = _rebuild(lines, core)
        # deadlines
        deadline = {}
        for k, o in enumerate(core):
            i = remap[k]
            for v, f in ops[i]["src"]:
                if v in imm_vals:
                    j = imm_vals[v]
                    deadline[j] = min(deadline.get(j, 10 ** 9), line_of[k] - imm_lat)
        # imms that feed other imms (pair longs): second must follow first by >= 1 line
        ok = True
        placed = {}
        for j in sorted(deadline, key=lambda j: deadline[j]):
            lo = 0
            for v, f in ops[j]["src"]:
                if v in imm_vals and imm_vals[v] not in placed:
                    pj = imm_vals[v]
                    t = _find_slot(L, ops[pj], 0, deadline[j] - 1)
                    if t is None: ok = False; break
                    _take_line(L[t], ops[pj]); placed[pj] = t
                if v in imm_vals and imm_vals[v] in placed:
                    lo = max(lo, placed[imm_vals[v]] + 1)
            if not ok: break
            if j in placed: continue
            t = _find_slot(L, ops[j], lo, deadline[j])
            if t is None: ok = False; break
            _take_line(L[t], ops[j]); placed[j] = t
        if ok:
            return [l["ops"] for l in L], pre
    raise RuntimeError("could not place imms")

def _rebuild(lines, core):
    L = []
    for ops_txt in lines:
        l = newline()
        for txt in ops_txt:
            o = next(o for o in core if o["text"].replace(">", "") == txt)
            take(l, o)
        L.append(l)
    return L

def _find_slot(L, o, lo, hi):
    for t in range(max(lo, 0), min(hi, len(L) - 1) + 1):
        if fits(L[t], o, L, t): return t
    return None

def _take_line(l, o):
    take(l, o)

def schedule_best(ops, tries=200, seed=1, lat=2):
    import random
    rnd = random.Random(seed)
    best = None
    for t in range(tries):
        noisy = []
        for o in ops:
            o2 = dict(o); o2["prio"] = o["prio"] + (rnd.random() * 6 if t else 0)
            noisy.append(o2)
        try:
            lines, line_of = schedule(noisy, lat=lat)
        except RuntimeError:
            continue
        if best is None or len(lines) < len(best[0]):
            best = (lines, line_of, t)
    return best

def schedule3(ops, lat=2, imm_lat=3, extra_deps=None, max_pre=60, noise=0.0, seed=0):
    """core ops list-scheduled from line `pre`, imms inserted EDF into free ALU slots."""
    import random
    rnd = random.Random(seed)
    imm_vals = {}
    for i, o in enumerate(ops):
        if o["unit"] == "imm":
            for d in o["dst"]: imm_vals[d] = i
    core, remap = [], {}
    for i, o in enumerate(ops):
        if o["unit"] == "imm": continue
        o2 = dict(o); o2["src"] = [(v, f) for v, f in o["src"] if v not in imm_vals]
        if extra_deps and i in extra_deps: o2["src"] = o2["src"] + extra_deps[i]
        o2["prio"] = o["prio"] + rnd.random() * noise
        remap[len(core)] = i; core.append(o2)
    for pre in range(0, max_pre):
        try:
            lines, line_of = schedule(core, lat=lat, fixed={k: pre for k in range(len(core))})
        except RuntimeError:
            continue
        L = _rebuild(lines, core)
        deadline = {}
        for k, o in enumerate(core):
            for v, f in ops[remap[k]]["src"]:
                if v in imm_vals:
                    j = imm_vals[v]
                    deadline[j] = min(deadline.get(j, 10 ** 9), line_of[k] - imm_lat)
        # imm->imm (pair second word) deps
        need = dict(deadline)
        for j in list(deadline):
            for v, f in ops[j]["src"]:
                if v in imm_vals:
                    pj = imm_vals[v]; need[pj] = min(need.get(pj, 10 ** 9), need[j] - 1)
        placed = {}; ok = True
        # reverse EDF: latest deadlines first, each at its latest feasible slot
        dep_of = {}
        for j in need:
            for v, f in ops[j]["src"]:
                if v in imm_vals: dep_of.setdefault(imm_vals[v], []).append(j)
        for j in sorted(need, key=lambda j: -need[j]):
            hi = need[j]
            for dj in dep_of.get(j, []):
                if dj in placed: hi = min(hi, placed[dj] - 1)
            t = None
            for tt in range(min(hi, len(L) - 1), -1, -1):
                if fits(L[tt], ops[j], L, tt): t = tt; break
            if t is None: ok = False; break
            take(L[t], ops[j]); placed[j] = t
        if ok:
            return [l["ops"] for l in L], pre
    raise RuntimeError("schedule3 failed")
