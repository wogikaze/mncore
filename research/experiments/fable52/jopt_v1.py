#!/usr/bin/env python3
"""Joint optimiser for the model14 dataflow: register-file storage (every value may be stored in several files, each
reader picks one copy), forwarding alternatives and the line schedule are solved together with CP-SAT.

usage: jopt.py <horizon> <timeout_s> [key=value ...]     (options: k1d=0/1, workers=N, out=/tmp/j.vsm, and any
       decision switch fixed to 0/1: tf nff daf ubf sfw vfw)

Port model (measured on the official assembler/emulator):
  per line and register file: one read pattern, one write;  an op writes at most one register per file;
  LM0/LM1: never read and written on one line, a write blocks all reads of that memory on the next 2 lines;
  imm cannot share a line with any LM0 access;  one mask entry per line (/1000 constant writes vs /$imrN flush);
  constants written to GRF with /1000 and per-cycle variables are readable 2 lines later.
"""
import sys, json, struct, time
import numpy as np
from ortools.sat.python import cp_model
from f32util import hpair
import model3, model14

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]
BIGV = 16384 * (1 + 56 / 512)
MGB = 0x4b400180
MGV = float(np.array([MGB], ">u4").view(">f4")[0])
GRF = "rs"; LMF = "nm"

class Use:
    def __init__(self, vals, form, cond=None, lat=2):
        self.vals = vals if isinstance(vals, (list, tuple)) else [(vals, 0)]
        self.vals = [v if isinstance(v, tuple) else (v, 0) for v in self.vals]
        self.form, self.cond, self.lat = form, cond, lat
        self.key = (form, tuple(self.vals))
def L(v, off=0, cond=None, lat=2): return Use([(v, off)], "L", cond, lat)
def E(v, cond=None): return Use(v, "E", cond)
def LV(v, cond=None): return Use(v, "LV", cond)
def W1(v, cond=None): return Use(v, "W1", cond)
def PAT(a, b, c, d): return Use([a, b, c, d], "PAT")

class Op:
    def __init__(self, name, unit, text, reads=(), writes=(), deps=(), fwd=(), flush=None, special=(), lmt=None):
        self.name, self.unit, self.text = name, unit, text
        self.reads, self.writes = list(reads), list(writes)
        self.deps = [d if len(d) == 3 else (d[0], d[1], None) for d in deps]
        self.fwd = [(f, None) if isinstance(f, str) else f for f in fwd]
        self.flush, self.special, self.lmt = flush, list(special), lmt

class Spec:
    def __init__(self): self.vals = {}; self.ops = []; self.opts = []
    def val(self, names, kind, files):
        for n in names.split(): self.vals[n] = (kind, files)
    def op(self, *a, **k): self.ops.append(Op(*a, **k)); return self.ops[-1]
    def imm(self, name, word, writes): self.op("i." + name, "imm", f'imm ui"0x{word:08x}" {{d}}', writes=writes)

def build(k1d=True, xd=False, dyd=False, hd=False, h8d=False, xcw=False, ta1=False, ta2=False, treg=False, bm=False):
    P = dict(model14.DEFAULT)
    (a2, b2), (a3, b3), (a4, b4) = P["lines"]
    A4 = float(np.float32(a4)) * 8.0; C10 = float(np.float32(P["c10"]))
    (ys0, yi0), (ys1, yi1) = P["Y"]; (xs0, xi0), (xs1, xi1) = P["X"]
    K1V = -73 * MGV / 8
    THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
    assert hpair(a3 * 8, a2 * 8) & 7 == 1 and fb(A4) & 0x3f == 0x0c and hpair(b4, BIGV) & 0x3f == 0x38 and fb(C10) & 0x3f == 7
    assert fb(K1V) & 7 == 6 and hpair(1, 0) == 0x3e000000
    S = Spec(); S.opts = ["tf", "nff", "daf", "ubf", "sfw", "vfw"]
    assert not (k1d and xd)
    S.val("MG A23 B4 C10 CP X A4 NLc TF TB TH N23 N4 XC TC0 K1" + (" T9" if k1d else ""), "cl", "rsn")
    S.val("KBc2 B23 P_A P_B cUB KBc1 DX IX IY", "cw", "rsn")
    S.val("H8", "cl" if h8d else "cw", "rsn"); S.val("DY", "cl" if dyd else "cw", "rsn"); S.val("H1516", "cl" if hd else "cw", "rsn")
    rH8 = (lambda: L("H8")) if h8d else (lambda: E("H8"))
    rDY = (lambda: L("DY")) if dyd else (lambda: E("DY"))
    rHH = (lambda: L("H1516")) if hd else (lambda: E("H1516"))
    rX = (lambda: L("X")) if xd else (lambda: E("X"))
    S.val("SL RW", "lv", "rs")
    S.val("AT", "lv", "rsn")
    S.val("RB Bv KBU L23 Z Y1 m Wv nR N0 us S1s S2r UAv DA D Za Zb Spv XA Vreg", "lv", "rsnm")
    if treg:                                             # long constants with one writer may also sit in the T register
        for v in ["MG", "N23", "N4", "C10", "Bv", "KBU", "L23"] + (["T9", "X"] if k1d else []) + ([] if xcw else ["XC"]):
            S.vals[v] = (S.vals[v][0], S.vals[v][1] + "t")
    I = S.imm
    I("MG", MGB, [("MG", "L"), ("AT", "W1")])
    if not k1d: I("K1", fb(K1V), [("K1", "L")])
    I("KBc2", hpair(4, 256), [("KBc2", "W")])
    if not h8d: I("H8", hpair(8, 8), [("H8", "W")])
    I("A23", hpair(a3 * 8, a2 * 8), [("A23", "L")]); I("B23", hpair(b3, b2), [("B23", "W")])
    I("A4", fb(A4), [("A4", "W")]); I("B4", hpair(b4, BIGV), [("B4", "L")])
    I("C10", fb(C10), [("C10", "L"), ("CP", "W+1")] + ([("XC", "W")] if xcw else []))
    I("P_A", hpair(61.5, -2560), [("P_A", "W")]); I("P_B", hpair(0.25, 246), [("P_B", "W")])
    I("cUB", hpair(3072, 12288), [("cUB", "W")]); I("KBc1", hpair(4, 65536), [("KBc1", "W")])
    if not xd: I("X", hpair(1, 0), [("X", "L")])
    if not dyd: I("DY", hpair(ys0 / 16, ys1 / 16), [("DY", "W")])
    if not hd: I("H1516", hpair(15 / 16, 15 / 16), [("H1516", "W")])
    I("NLc", fb(model14.NLP), [("NLc", "W+1")])
    I("DX", hpair(xs0 / 16, xs1 / 16), [("DX", "W")]); I("IX", hpair(xi0, xi1), [("IX", "W")]); I("IY", hpair(yi0, yi1), [("IY", "W")])
    I("TXlo", fb(float(TLO)), [("TF", "W+1"), ("TB", "W+1")]); I("TXhiF", fb(float(THI_F)), [("TF", "W"), ("TH", "W")])
    I("TXhiB", fb(float(THI_B)), [("TB", "W")]); I("TXloh", fb(float(TLO_H)), [("TH", "W+1")])
    O = S.op
    # derived constants
    O("CP", "mau", "fvmul {0} {0} {d}", [L("C10")], [("CP", "W")])
    if xd: O("Xd", "mau", "fvmul {0} {1} {d}", [E("P_B"), E("KBc2")], [("X", "W")])                      # [1, 0]
    if not xcw: O("XC", "mau", "fvmul {0} {1} {d}", [rX(), L("C10")], [("XC", "L")])
    if h8d:
        O("H8a", "mau", "fvadd {0} {0} {d}", [E("KBc2")], [("H8", "W")])
        O("H8b", "mau", "fvadd {0} {0} {d}", [E("KBc2")], [("H8", "W+1")])
    if dyd:
        assert (ys0 / 16, ys1 / 16) == (-1 / 16, -3 / 16)
        O("DYa", "mau", "fvmul -{0} {0} {d}", [E("P_B")], [("DY", "W")])
        O("DYb", "mau", "fvfma {0} {0} -{0} {d}", [E("P_B")], [("DY", "W+1")])
    if hd:
        O("HHa", "mau", "fvfma {0} {1} {2} {d}", [E("P_B"), E("KBc2"), rDY()], [("H1516", "W")])
        O("HHb", "mau", "fvfma {0} {1} {2} {d}", [E("P_B"), E("KBc2"), rDY()], [("H1516", "W+1")])
    if k1d:
        O("T9", "mau", "fvfma {0} -{1} -{0} {d}", [L("MG"), rH8()], [("T9", "L")])
        O("K1", "mau", "fvfma {0} -{1} {2} {d}", [L("MG"), L("X"), L("T9")], [("K1", "L")])
    O("N23", "mau", "fvadd {0} -{1} {d}", [E("B23"), L("MG")], [("N23", "L")])
    O("N4", "mau", "fvadd {0} -{1} {d}", [E("B4"), L("MG")], [("N4", "L")])
    O("N0c", "mau", "fvfma {0} {1} -{2} {d}", [E("B23"), rHH(), rDY()], [("N0", "W0")])
    # coordinates
    O("o5", "alu", "iadd $l2bid {0} {d}", [L("MG")])
    O("TC0", "alu", "iadd $l2bid $aluf {d}", [], [("TC0", "L")], fwd=["o5"])
    O("o1", "alu", "iand $l1bid {0} {d}", [PAT("K1", "A23", "A23", "A23")])
    O("SL", "alu", "ixor $aluf {0} {d}", [PAT("K1", "TC0", "TC0", "TC0")], [("SL", "LV")], fwd=["o1"])
    O("o3", "alu", "iand $peid {0} {d}", [PAT("B4", "C10", "A4", "A4")])
    O("RW", "alu", "ior $aluf {0} {d}", [L("MG")], [("RW", "LV")], fwd=["o3"])
    O("LB", "l1", "l1bmd $aluf $lb0", fwd=["RW"])
    O("RA", "l1", "l1bmm4 $lb0 $nowrite", deps=[("LB", 3)])
    O("RB", "l1", "l1bmm4 $lb64 {d}", [], [("RB", "LV")], deps=[("LB", 3)])
    O("acc1", "mau", "fvfma $lbf {0} {1} {d}", [rH8(), L("SL", 0)], fwd=["RA"])
    O("acc2", "mau", "fvadd $mauf {0} {d}", [L("SL", 2)], fwd=["acc1"])
    O("Bv", "mau", "fvfma $mauf {0} {1} {d}", [rH8(), LV("RB")], [("Bv", "LV")], fwd=["acc2"])
    O("KBU", "mau", "fvadd {0} -{1} {d}", [L("RW", 4, lat=3), L("MG")], [("KBU", "LV")])
    O("KB", "mau", "fvfma {0} {1} {2} {d}", [LV("KBU"), E("P_B"), L("MG")], [("Z", "W1"), ("Y1", "W0")])
    O("AT0", "mau", "fvmul -{0} {1} {d}", [LV("Bv"), rH8()], [("AT", "W0")])
    # estimator
    O("L23", "mau", "fvfma $mauf {0} {1} {d}", [E("A23"), L("N23")], [("L23", "LV")], fwd=["Bv"])
    O("L4", "mau", "fvfma {0} {1} {2} {d}", [LV("Bv"), L("A4"), L("N4")])
    O("mn1", "alu", "fmin {0} $mauf {d}", [LV("L23")], fwd=["L4"])
    O("Zy", "alu", "fmin {0} $aluf {d}", [W1("L23")], [("Z", "W0"), ("Y1", "W1")], fwd=["mn1"])
    O("m", "mau", "fvadd {0} {1} {d}", [LV("Z"), LV("Y1")], [("m", "LV")])
    # token
    O("T", "mau", {"tf": "fvfma $mauf {1} {2} {d}", "!tf": "fvfma {0} {1} {2} {d}"}, [LV("m", "!tf"), E("KBc2"), LV("AT")],
      [("Wv", "LV")], fwd=[("m", "tf")], special=["$t"])
    O("nF", "mau", {"nff": "fvfma $mauf {1} {1} {d}", "!nff": "fvfma {0} {1} {1} {d}"}, [LV("m", "!nff"), rHH()], fwd=[("m", "nff")])
    O("n", "alu", "ffloor $mauf {d}", [], [("nR", "LV"), ("N0", "W1")], fwd=["nF"])
    O("us", "mau", "fvfma {0} {1} $lmt2 {d}", [LV("m"), rH8()], [("us", "LV")], deps=[("T", 2), ("tE1", 3), ("tE2", 3)], lmt=2)
    # digits
    O("R1", "mau", "fvfma $aluf {0} -{1} {d}", [L("CP"), rX()], fwd=["n"], special=["$omr1"])
    O("S1", "alu", "ffloor $mauf {d}", [], [("S1s", "LV")], fwd=["R1"])
    O("R2", "mau", "fvfma $aluf {0} {1} {d}", [L("C10"), L("XC")], fwd=["S1"])
    O("S2", "alu", "ffloor $mauf {d}", [], [("S2r", "LV")], fwd=["R2"])
    O("UA", "mau", "fvfma/$imr1 {0} {1} {2} {d}", [LV("S1s"), E("P_B"), LV("N0")], [("UAv", "LV")], deps=[("R1", 1)], flush=1)
    O("UB", "mau", {"ubf": "fvfma/$imr2 $aluf {1} {2} {d}", "!ubf": "fvfma/$imr2 {0} {1} {2} {d}"},
      [LV("S2r", "!ubf"), E("P_A"), E("cUB")], fwd=[("S2", "ubf")], deps=[("DM", 1)], flush=2)
    O("Ys", "mau", "fvadd $mauf {0} {d}", [LV("UAv")], fwd=["UB"])
    O("V2", "mau", "fvfma $mauf {0} {1} {d}", [E("KBc1"), L("NLc")], fwd=["Ys"])
    O("VT", "alu", "fmax $mauf $lmt0 {d}", fwd=["V2"], deps=[("T", 2), ("tT1", 3), ("tT2", 3)], lmt=0)
    # position
    O("DA", "mau", {"daf": "fvfma $mauf {1} {2} {d}", "!daf": "fvfma {0} {1} {2} {d}"}, [LV("us", "!daf"), E("DX"), E("IX")],
      [("DA", "LV")], fwd=[("us", "daf")])
    O("DB", "mau", "fvfma {0} {1} {2} {d}", [LV("us"), rDY(), E("IY")])
    O("DM", "alu", "fmax {0} $mauf {d}", [LV("DA")], [("D", "LV")], fwd=["DB"], special=["$omr2"])
    O("Dw", "alu", "fmax {0} {1} {d}", [W1("D"), LV("D")], [("Za", "W0"), ("Zb", "W1")])
    O("NR", "mau", "fvadd -{0} -{1} {d}", [LV("nR"), LV("Wv")], [("Za", "W1"), ("Zb", "W0")])
    O("S", "mau", "fvadd -{0} {1} {d}", [LV("Za"), LV("Zb")], [("Spv", "LV")], special=["$omr3"])
    O("AM", "mau", {"sfw": "fvfma/$imr3 $mauf {1} {2} {d}", "!sfw": "fvfma/$imr3 {0} {1} {2} {d}"},
      [LV("Spv", "!sfw"), rH8(), L("MG")], [("XA", "W1")], fwd=[("S", "sfw")], deps=[("S", 1)], flush=3)
    O("V", "alu", "fftoi $aluf {d}", [], [("Vreg", "LV")], fwd=["VT"])
    O("F1x", "alu", {"vfw": "ullsr $aluf $mauf {d}", "!vfw": "ullsr {0} $mauf {d}"}, [LV("Vreg", "!vfw")], fwd=["AM", ("V", "vfw")])
    O("FO", "alu", "llsl $aluf {0} {d}", [LV("XA")], fwd=["F1x"])
    O("OUT", "l1", "l1bmr4lbor $aluf $lb0", fwd=["FO"])
    # tables (LM0, T-indirect)
    toff = MGB & 0xfff
    def ad(ids, base): return "$lm[" + ",".join(str((256 * i + toff) % 4096 + base) for i in ids) + "]"
    O("tT1", "alu" if ta1 else "mau", ("lpassa" if ta1 else "fvpassa") + " {0} {d}", [L("TF")], special=[ad([3, 6, 9, 12], 0)])
    O("tT2", "alu" if ta2 else "mau", ("lpassa" if ta2 else "fvpassa") + " {0} {d}", [PAT("TB", "TB", "TB", "TH")], special=[ad([0, 5, 10, 15], 0)])
    O("tE1", "mau", "fvpassa -{0} {d}", [rH8()], special=[ad([0, 6, 10, 12], 2)])
    O("tE2", "mau", "fvpassa {0} {d}", [rH8()], special=[ad([2, 4, 8, 14], 2)])
    if bm:                                               # constants written whole by one op may also sit in the L1BM
        for v, (kind, fl) in list(S.vals.items()):
            ws = [(o, form) for o in S.ops for x, form in o.writes if x == v]
            if kind in ("cl", "cw") and len(ws) == 1 and ws[0][1] == ("L" if kind == "cl" else "W"):
                S.vals[v] = (kind, fl + "b")
    return S

def special_file(s):
    if s == "$t": return "t"
    if s.startswith("$omr"): return "o"
    if s.startswith("$lm"): return "m"
    raise ValueError(s)

def solve(S, H, timeout=120, workers=12, fixed=None, hint=None, log=False, lb=1, relax=()):
    fixed = fixed or {}
    M = cp_model.CpModel()
    ops = S.ops; byname = {o.name: o for o in ops}
    t = {o.name: M.NewIntVar(1, H, "t_" + o.name) for o in ops}
    TRUE = M.NewConstant(1); FALSE = M.NewConstant(0)
    opt = {}
    for n in S.opts:
        opt[n] = M.NewBoolVar("opt_" + n)
        if n in fixed: M.Add(opt[n] == int(fixed[n]))
    M.AddBoolOr([opt["tf"].Not(), opt["nff"].Not()])
    def lit(c):
        if c is None: return TRUE
        return opt[c[1:]].Not() if c.startswith("!") else opt[c]
    st = {v: {f: M.NewBoolVar(f"st_{v}_{f}") for f in fl} for v, (kind, fl) in S.vals.items()}
    writers = {v: [] for v in S.vals}
    for o in ops:
        for v, form in o.writes: writers[v].append(o)
    ru = {}; rd = {}; wr = {}; mk = {}
    um = {o.name: M.NewBoolVar("um_" + o.name) for o in ops if any(S.vals[v][0] in ("cl", "cw") for v, form in o.writes)}
    def OR(lits, name):
        lits = [x for x in lits if x is not FALSE]
        if any(x is TRUE for x in lits): return TRUE
        if not lits: return FALSE
        if len(lits) == 1: return lits[0]
        b = M.NewBoolVar(name)
        M.AddBoolOr(lits).OnlyEnforceIf(b)
        for x in lits: M.AddImplication(x, b)
        return b
    for o in ops:
        for i, u in enumerate(o.reads):
            fl = None
            for v, off in u.vals:
                s = set(S.vals[v][1]); fl = s if fl is None else fl & s
            if u.form not in ("L", "LV") or u.vals[0][1] != 0: fl.discard("t")
            if u.form not in ("L", "E") or u.vals[0][1] != 0 or any(byname[p].unit == "l1" for p, c in o.fwd): fl.discard("b")
            fl = sorted(fl)
            r = {f: M.NewBoolVar(f"ru_{o.name}_{i}_{f}") for f in fl}
            a = lit(u.cond)
            M.Add(sum(r.values()) == 1).OnlyEnforceIf(a)
            if a is not TRUE: M.Add(sum(r.values()) == 0).OnlyEnforceIf(a.Not())
            for f in fl:
                for v, off in u.vals: M.AddImplication(r[f], st[v][f])
            ru[(o.name, i)] = r
            for v in {v for v, off in u.vals}:
                for p in writers[v]:
                    if p is not o:
                        M.Add(t[o.name] >= t[p.name] + u.lat).OnlyEnforceIf(a)
                        if p.name in um and S.vals[v][0] in ("cl", "cw"): M.Add(t[o.name] >= t[p.name] + 3).OnlyEnforceIf([a, um[p.name]])
                        if "b" in r: M.Add(t[o.name] >= t[p.name] + 5).OnlyEnforceIf(r["b"])
        for f in "rsnm":
            rl = [ru[(o.name, i)][f] for i in range(len(o.reads)) if f in ru[(o.name, i)]]
            if f == "m" and o.lmt is not None: rl.append(TRUE)
            rd[(o.name, f)] = OR(rl, f"rd_{o.name}_{f}")
            wl = [st[v][f] for v, form in o.writes if f in st[v]]
            if f == "m" and any(special_file(s) == "m" for s in o.special): wl.append(TRUE)
            wr[(o.name, f)] = OR(wl, f"wr_{o.name}_{f}")
        ml = [st[v][f] for v, form in o.writes if S.vals[v][0] in ("cl", "cw") for f in GRF if f in st[v]]
        mk0 = OR(ml, f"mk0_{o.name}")
        if o.name in um and mk0 is not FALSE:
            b = M.NewBoolVar(f"mk_{o.name}")                      # masked GRF constant write on this op
            M.AddBoolAnd([mk0, um[o.name].Not()]).OnlyEnforceIf(b)
            M.AddBoolOr([b, mk0.Not(), um[o.name]])
            mk[o.name] = b
        else: mk[o.name] = FALSE
        # within-op rules
        for i in range(len(o.reads)):
            for j in range(i + 1, len(o.reads)):
                if o.reads[i].key == o.reads[j].key: continue
                for f in ru[(o.name, i)]:
                    if f in ru[(o.name, j)]: M.AddBoolOr([ru[(o.name, i)][f].Not(), ru[(o.name, j)][f].Not()])
            if o.lmt is not None and "m" in ru[(o.name, i)]: M.Add(ru[(o.name, i)]["m"] == 0)
        wv = [v for v, form in o.writes]
        for i in range(len(wv)):
            for j in range(i + 1, len(wv)):
                for f in st[wv[i]]:
                    if f in st[wv[j]]: M.AddBoolOr([st[wv[i]][f].Not(), st[wv[j]][f].Not()])
        for f in LMF:
            if rd[(o.name, f)] is not FALSE and wr[(o.name, f)] is not FALSE:
                M.AddBoolOr([rd[(o.name, f)].Not(), wr[(o.name, f)].Not()])
        if o.unit == "imm":
            for v, form in o.writes:
                if "m" in st[v]: M.Add(st[v]["m"] == 0)
        if any(special_file(s) == "m" for s in o.special):          # table write: no LM0 lane variable written by the same op
            for v, form in o.writes:
                if "m" in st[v]: M.Add(st[v]["m"] == 0)
        for p, c in o.fwd: M.Add(t[o.name] == t[p] + 1).OnlyEnforceIf(lit(c))
        for p, lat, c in o.deps: M.Add(t[o.name] >= t[p] + lat).OnlyEnforceIf(lit(c))
    # a stored value needs a reader (keeps the solution tidy), every value written needs no storage unless read
    for v in S.vals:
        for f in st[v]:
            readers = [ru[(o.name, i)][f] for o in ops for i, u in enumerate(o.reads) if f in ru[(o.name, i)] and any(x == v for x, _ in u.vals)]
            if readers: M.AddBoolOr(readers).OnlyEnforceIf(st[v][f])
            else: M.Add(st[v][f] == 0)
    M.Add(sum(st[v]["m"] for v in S.vals if S.vals[v][0] == "lv" and "m" in st[v]) <= 15)
    # T register: one tenant at a time (constants before the token address is loaded)
    tiv = []
    for v in S.vals:
        if "t" not in st[v]: continue
        (w,) = writers[v]
        end = M.NewIntVar(1, H, f"tend_{v}"); size = M.NewIntVar(1, H, f"tsize_{v}")
        M.Add(size == end - t[w.name] + 1)
        tiv.append(M.NewOptionalIntervalVar(t[w.name], size, end + 1, st[v]["t"], f"tiv_{v}"))
        for o in ops:
            for i, u in enumerate(o.reads):
                if "t" in ru[(o.name, i)] and u.vals[0][0] == v: M.Add(end >= t[o.name]).OnlyEnforceIf(ru[(o.name, i)]["t"])
    if tiv:
        size = M.NewIntVar(1, H + 1, "tsize_token")
        M.Add(size == H + 1 - t["T"])
        tiv.append(M.NewIntervalVar(t["T"], size, H + 1, "tiv_token"))
        M.AddNoOverlap(tiv)
    # capacities
    cls = {"imm": 0, "alu": 0, "mau": 1, "l1": 2}
    groups = {0: [], 1: [], 2: []}
    for o in ops: groups[cls[o.unit]].append(o)
    for k, g in groups.items():
        if k != 2: M.AddAllDifferent([t[o.name] for o in g])
    # L1 unit: fixed ops, L1BM stores (line after the writer) and loads (line before the reader)
    l1iv = [M.NewIntervalVar(t[o.name], 1, t[o.name] + 1, "l1_" + o.name) for o in groups[2]]
    bstores = [(t["LB"], TRUE)]; bloads = [(t["RA"], TRUE), (t["RB"], TRUE)]       # (line expression, presence)
    for v in S.vals:
        if "b" not in st[v]: continue
        (w,) = writers[v]
        l1iv.append(M.NewOptionalIntervalVar(t[w.name] + 1, 1, t[w.name] + 2, st[v]["b"], f"l1s_{v}"))
        M.Add(t[w.name] + 1 <= H).OnlyEnforceIf(st[v]["b"])
        bstores.append((t[w.name] + 1, st[v]["b"]))
    for o in ops:
        for i, u in enumerate(o.reads):
            if "b" in ru[(o.name, i)]:
                l1iv.append(M.NewOptionalIntervalVar(t[o.name] - 1, 1, t[o.name], ru[(o.name, i)]["b"], f"l1r_{o.name}_{i}"))
                bloads.append((t[o.name] - 1, ru[(o.name, i)]["b"]))
    M.AddNoOverlap(l1iv)
    bdom = cp_model.Domain.FromIntervals([[-H - 2, 0], [3, H + 2]])     # an L1BM store blocks loads on the next two lines
    for k, (ts, ps) in enumerate(bstores):
        for j, (tl, pl) in enumerate(bloads):
            if ps is TRUE and pl is TRUE:
                M.AddLinearExpressionInDomain(tl - ts, bdom); continue
            nb = M.NewBoolVar(f"bnb_{k}_{j}")
            M.AddLinearExpressionInDomain(tl - ts, bdom).OnlyEnforceIf(nb)
            M.AddBoolOr([nb] + [x.Not() for x in (ps, pl) if x is not TRUE])
    # same-line conflicts
    nsame = 0
    for i, a in enumerate(ops):
        for b in ops[i + 1:]:
            if cls[a.unit] == cls[b.unit]: continue
            clauses = []
            for f in "rsnm":
                for x in range(len(a.reads)):
                    for y in range(len(b.reads)):
                        if a.reads[x].key == b.reads[y].key: continue
                        if f in ru[(a.name, x)] and f in ru[(b.name, y)] and "rd" not in relax and "rd" + f not in relax:
                            clauses.append([ru[(a.name, x)][f], ru[(b.name, y)][f]])
                if f == "m":                                       # T-indirect reads against any other LM0 read
                    for p, q in ((a, b), (b, a)):
                        if p.lmt is not None:
                            if q.lmt is not None and q.lmt != p.lmt: clauses.append([])
                            for y in range(len(q.reads)):
                                if "m" in ru[(q.name, y)]: clauses.append([ru[(q.name, y)]["m"]])
                wa, wb = wr[(a.name, f)], wr[(b.name, f)]
                if wa is not FALSE and wb is not FALSE and "wr" not in relax and "wr" + f not in relax: clauses.append([wa, wb])
                if f in LMF:
                    for p, q in ((a, b), (b, a)):
                        if rd[(p.name, f)] is not FALSE and wr[(q.name, f)] is not FALSE and "lmrw" not in relax and "lmrw" + f not in relax:
                            clauses.append([rd[(p.name, f)], wr[(q.name, f)]])
            for p, q in ((a, b), (b, a)):
                if p.unit == "imm" and "immlm0" not in relax:
                    for x in (rd[(q.name, "m")], wr[(q.name, "m")]):
                        if x is not FALSE: clauses.append([x])
                if q.flush is not None and mk[p.name] is not FALSE and "mask" not in relax: clauses.append([mk[p.name]])
            sa = {special_file(s) for s in a.special} & {special_file(s) for s in b.special} & {"o", "t"}
            if sa: clauses.append([])
            if not clauses: continue
            hard = any(all(x is TRUE for x in c) for c in clauses)
            if hard:
                M.Add(t[a.name] != t[b.name]); continue
            same = M.NewBoolVar(f"same_{a.name}_{b.name}"); nsame += 1
            M.Add(t[a.name] != t[b.name]).OnlyEnforceIf(same.Not())
            for c in clauses:
                M.AddBoolOr([same.Not()] + [x.Not() for x in c if x is not TRUE])
    # LM write blocks reads on the next two lines (any address)
    nblk = 0
    dom = cp_model.Domain.FromIntervals([[-H, 0], [3, H]])
    for a in ops:
        for b in ops:
            if a is b: continue
            for f in LMF:
                w, r = wr[(a.name, f)], rd[(b.name, f)]
                if w is FALSE or r is FALSE or "blk" in relax or "blk" + f in relax: continue
                if w is TRUE and r is TRUE:
                    M.AddLinearExpressionInDomain(t[b.name] - t[a.name], dom); continue
                nb = M.NewBoolVar(f"nb_{a.name}_{b.name}_{f}"); nblk += 1
                M.AddLinearExpressionInDomain(t[b.name] - t[a.name], dom).OnlyEnforceIf(nb)
                M.AddBoolOr([nb] + [x.Not() for x in (w, r) if x is not TRUE])
    M.Add(t["OUT"] >= lb)
    M.Minimize(t["OUT"])
    if hint:
        for k, v in hint.items():
            if k in t: M.AddHint(t[k], v)
    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = timeout
    sol.parameters.num_workers = workers
    sol.parameters.log_search_progress = log
    r = sol.Solve(M)
    info = dict(status=sol.StatusName(r), bound=sol.BestObjectiveBound(), nsame=nsame, nblk=nblk)
    if r not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None, info
    V = sol.Value
    res = dict(lines=V(t["OUT"]), t={k: V(x) for k, x in t.items()}, opt={k: V(x) for k, x in opt.items()},
               st={v: [f for f in st[v] if V(st[v][f])] for v in st},
               ru={f"{k[0]}:{k[1]}": next((f for f in r_ if V(r_[f])), None) for k, r_ in ru.items()},
               um={k: V(x) for k, x in um.items()})
    return res, info

def render(S, res):
    """allocate addresses and produce the program text (list of lines)"""
    nxt = {"r": 0, "s": 0, "n": 0, "m": 8}; addr = {}
    order = sorted(S.vals, key=lambda v: {"lv": 0, "cl": 1, "cw": 2}[S.vals[v][0]])
    for v in order:
        kind = S.vals[v][0]
        for f in res["st"][v]:
            if f in "tb": continue
            if kind == "lv": a = (nxt[f] + 7) // 8 * 8; nxt[f] = a + 8
            elif kind == "cl": a = (nxt[f] + 1) // 2 * 2; nxt[f] = a + 2
            else: a = nxt[f]; nxt[f] += 1
            addr[(v, f)] = a
    assert nxt["m"] <= 128, nxt
    def on(c): return c is None or (res["opt"][c[1:]] == 0 if c.startswith("!") else res["opt"][c] == 1)
    def rtext(o, i):
        u = o.reads[i]; f = res["ru"][f"{o.name}:{i}"]
        if f is None: return "?"
        if f == "t": return "$t"
        if f == "b": return "$lbfe" if u.form == "E" else "$lbf"
        if u.form == "PAT": return f"$l{f}[" + ",".join(str(addr[(v, f)] + off) for v, off in u.vals) + "]"
        v, off = u.vals[0]; a = addr[(v, f)] + off
        return {"L": f"$l{f}{a}", "E": f"${f}{a}e", "LV": f"$l{f}{a}v", "W0": f"${f}{a}v2", "W1": f"${f}{a + 1}v2"}[u.form]
    def dtext(o):
        d = []
        for v, form in o.writes:
            kind = S.vals[v][0]
            for f in res["st"][v]:
                if f == "t": d.append("$t"); continue
                if f == "b": continue
                a = addr[(v, f)]; msk = "/1000" if (kind in ("cl", "cw") and f in GRF and not res["um"].get(o.name)) else ""
                d.append({"L": f"$l{f}{a}", "W": f"${f}{a}", "W+1": f"${f}{a + 1}", "LV": f"$l{f}{a}v", "W0": f"${f}{a}v2", "W1": f"${f}{a + 1}v2"}[form] + msk)
        d += o.special
        return " ".join(d) if d else "$nowrite"
    lines = {}
    bst = sorted((v for v in S.vals if "b" in res["st"][v]), key=lambda v: res["t"][next(o.name for o in S.ops if any(x == v for x, _ in o.writes))])
    baddr = {v: 256 + 64 * k for k, v in enumerate(bst)}
    for v in bst:
        w = next(o for o in S.ops if any(x == v for x, _ in o.writes))
        lines.setdefault(res["t"][w.name] + 1, []).append(("l1", f"l1bmd {'$mauf' if w.unit == 'mau' else '$aluf'} $lb{baddr[v]}"))
    for o in S.ops:
        for i, u in enumerate(o.reads):
            if res["ru"].get(f"{o.name}:{i}") == "b":
                lines.setdefault(res["t"][o.name] - 1, []).append(("l1", f"l1bmm4 $lb{baddr[u.vals[0][0]]} $nowrite"))
    for o in S.ops:
        txt = o.text
        if isinstance(txt, dict): txt = next(x for c, x in txt.items() if on(c))
        txt = txt.format(*[rtext(o, i) for i in range(len(o.reads))], d=dtext(o)) if "{" in txt else txt
        lines.setdefault(res["t"][o.name], []).append((o.unit, txt))
    order_u = {"imm": 0, "alu": 0, "mau": 1, "l1": 2}
    out = []
    for k in range(1, res["lines"] + 1):
        ops_k = sorted(lines.get(k, []), key=lambda x: order_u[x[0]])
        out.append("; ".join(x[1] for x in ops_k) if ops_k else "nop")
    return out

if __name__ == "__main__":
    H = int(sys.argv[1]); timeout = float(sys.argv[2])
    kv = dict(a.split("=") for a in sys.argv[3:])
    bopts = {k: bool(int(kv.pop(k, d))) for k, d in (("k1d", 1), ("xd", 0), ("dyd", 0), ("hd", 0), ("h8d", 0), ("xcw", 0), ("ta1", 0), ("ta2", 0), ("treg", 0), ("bm", 0))}
    workers = int(kv.pop("workers", 12)); out = kv.pop("out", "/tmp/j.vsm")
    log = int(kv.pop("log", 0)); lb = int(kv.pop("lb", 1)); relax = tuple(x for x in kv.pop("relax", "").split(",") if x)
    fixed = {k: int(v) for k, v in kv.items()}
    S = build(**bopts)
    t0 = time.time()
    res, info = solve(S, H, timeout, workers, fixed, log=bool(log), lb=lb, relax=relax)
    print("status", info, "time %.0fs" % (time.time() - t0), flush=True)
    if res:
        print("lines", res["lines"], "total", res["lines"] + 7, "opts", res["opt"], "build", {k: int(v) for k, v in bopts.items() if v})
        prog = render(S, res)
        open(out, "w").write("\n".join(prog + TAIL) + "\n")
        json.dump(res, open(out.replace(".vsm", ".json"), "w"), indent=0, sort_keys=True)
