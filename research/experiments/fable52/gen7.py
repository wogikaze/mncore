#!/usr/bin/env python3
"""v7 generator (math = model7).  build: G(cfg).OPS for sched3.

cfg maps value names to register files (r=GRF0, s=GRF1, n=LM1) plus options:
  o_tabalu  text table written by ALU lpassa from pre-negated constants (else MAU fvadd)
Differences from gen5: n = floor(15(m+1)/16); digit flags from R1' and from the first delta fmax;
position sum as the pair [-s, s] with one flushed op for both shift amounts; T and 4m-8B in one op;
the cross-word fmin of the estimator reads line 2 straight from L23.
"""
import struct, sys
import numpy as np
from f32util import hpair
from sched3 import op
import model3, model7

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
MGV = 1.5 * 2.0 ** 23
TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]

DEFAULT = dict(
    o_tabalu=0,
    MG="rs", MP="r", ML="n",
    H8="n", K1="s", KBc1="s", KBc2="n", A23="n", A4="n", H1516="n",
    CP="n", XC="s", X="s", P_A="n", P_B="n", cUB="s", NLc="n",
    DX="n", IX="s", DY="s", TF="r", TBH="s", D="n", TC0="s",
    SL="s", RW="r", RA="r", RB="s", Bv="r", KBv="s", AT="n",
    L23="s", Z="s", Y1="r", mS="s", mR="r", Wv="s",
    nR="r", N0="s", us="s",
    R1v="s", S1s="s", S2r="r", N1v="r", UAv="s", Rv="r",
    DA="r", DMn="r", DMs="s", Za="r", Zb="s", Spv="r", XA="s",
)
P7 = dict(model7.DEFAULT)

class G:
    def __init__(self, cfg=None):
        self.cfg = dict(DEFAULT); self.cfg.update(cfg or {})
        c = self.cfg
        c["B23"] = c["B4"] = c["C10"] = c["MP"]          # hosts of the peid masks
        c["IY"] = c["C_N"] = c["ML"]                     # hosts of the l1bid masks
        self.P = P7
        self.next = {"r": 0, "s": 0, "n": 0}
        self.OPS = []; self.VAL = {}; self.viol = 0
        self.build()
        import sched3
        for o in self.OPS:
            if not sched3.fits({}, 0, o): self.viol += 1
    def ck(self, cond, msg=""):
        if not cond: self.viol += 1
    def F(self, name): return self.cfg[name]
    def var(self, name):
        f = self.F(name); a = (self.next[f] + 7) // 8 * 8; self.next[f] = a + 8
        self.VAL[name] = (f, a); return name
    def along(self, f):
        a = (self.next[f] + 1) // 2 * 2; self.next[f] = a + 2; return a
    def aword(self, f):
        a = self.next[f]; self.next[f] += 1; return a
    def A(self, text, dst=(), src=(), fwd=(), unit="alu", prio=0):
        self.OPS.append(op(text, unit, dst, src, fwd, prio))
    def M(self, text, dst=(), src=(), fwd=(), prio=0): self.A(text, dst, src, fwd, "mau", prio)
    def LV(self, n): f, a = self.VAL[n]; return f"$l{f}{a}v"
    def W0(self, n): f, a = self.VAL[n]; return f"${f}{a}v2"
    def W1(self, n): f, a = self.VAL[n]; return f"${f}{a + 1}v2"
    def CL(self, n): f, a = self.VAL[n]; return f"$l{f}{a}"
    def CE(self, n): f, a = self.VAL[n]; return f"${f}{a}e"
    def AD(self, n): return self.VAL[n][1]
    def FI(self, n): return self.VAL[n][0]
    def S(self, *names): return [(n, self.VAL[n][0]) for n in names]
    def H(self, name, a, b, long=False):
        """half-pair constant; long=True stores the same 32-bit word twice (usable as a mask long)."""
        f = self.F(name)
        if long:
            ad = self.along(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >$l{f}{ad}', [name], unit="imm")
        else:
            ad = self.aword(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >${f}{ad}', [name], unit="imm")
        return hpair(a, b)
    def mg(self, *avoid, need=None):
        c = [g for g in ("MG", "MG@r", "MG@s", "MG@n") if g in self.VAL and self.VAL[g][0] not in avoid
             and (need is None or self.VAL[g][0] == need)]
        if not c:
            self.viol += 1
            c = [g for g in ("MG", "MG@r", "MG@s", "MG@n") if g in self.VAL]
        return c[0]
    def pick(self, names, *avoid):
        c = [n for n in names if self.VAL[n][0] not in avoid]
        if not c:
            self.viol += 1; c = list(names)
        return c[0]

    def build(self):
        A, M, LV, W0, W1, CL, CE, AD, S, FI = self.A, self.M, self.LV, self.W0, self.W1, self.CL, self.CE, self.AD, self.S, self.FI
        P, c = self.P, self.cfg
        (a2, b2), (a3, b3), (a4, b4) = P["lines"]
        A4 = float(np.float32(a4)) * 8.0
        C10 = float(np.float32(P["c10"]))
        (ys0, yi0), (ys1, yi1) = P["Y"]; (xs0, xi0), (xs1, xi1) = P["X"]
        # ---------------- lane variables that constants refer to ----------------
        for n in ("SL", "RW", "RA", "RB", "Bv", "KBv", "AT"): self.var(n)
        # ---------------- constants ----------------
        files = list(self.F("MG")); fat = FI("AT")
        addrs = {f: self.along(f) for f in files}
        self.VAL["MG"] = (files[0], addrs[files[0]])
        for f in files[1:]: self.VAL["MG@" + f] = (f, addrs[f])
        mgdst = " ".join(f">$l{f}{a}" for f, a in addrs.items()); mgnames = ["MG"] + ["MG@" + f for f in files[1:]]
        if fat not in files:
            mgdst += f" >{W1('AT')}"; mgnames.append("AT#1")
        A(f'imm ui"0x4b400000" {mgdst}', mgnames, unit="imm")
        self.H("H8", 8, 8); self.H("K1", -73 * MGV / 8, -73 * MGV / 8)
        self.H("KBc1", 0.25, 65536); self.H("KBc2", 4, 256)
        self.H("A23", a3 * 8, a2 * 8)
        w = self.H("B23", b3, b2, long=True); assert w & 0x3f == 0x38, "B23 does not host mask 0x38"
        fa4 = self.F("A4"); a_a4 = self.along(fa4); self.VAL["A4"] = (fa4, a_a4)
        A(f'imm ui"0x{fb(A4):08x}" >${fa4}{a_a4}', ["A4"], unit="imm")      # [a4', 0]
        w = self.H("B4", b4, 16384 * (1 + 7 / 512), long=True); assert w & 0x3f == 0x07
        self.H("H1516", 15 / 16, 15 / 16)
        fc, fp = self.F("C10"), self.F("CP")
        self.ck(fc != fp); assert fb(C10) & 0x3f == 0x0c
        a_c10 = self.along(fc); a_cp = self.along(fp)
        self.VAL["C10"] = (fc, a_c10); self.VAL["CP"] = (fp, a_cp)
        A(f'imm ui"0x{fb(C10):08x}" >$l{fc}{a_c10} >$l{fp}{a_cp}', ["C10", "CP#0"], unit="imm")
        M(f"fvmul {CL('C10')} {CL('C10')} >${fp}{a_cp}", ["CP"], [("C10", fc), ("CP#0", fp)])
        self.H("X", 1, 0)
        fx = self.F("XC"); a_xc = self.along(fx); self.VAL["XC"] = (fx, a_xc)
        self.ck(FI("X") != fc)
        M(f"fvmul {CE('X')} {CL('C10')} >$l{fx}{a_xc}", ["XC"], S("X", "C10"))
        self.H("P_A", 984, -2560); self.H("P_B", 4, 246); self.H("cUB", 49152, 12288)
        w = self.H("C_N", 196, 48.0625, long=True); assert w & 7 == 1
        self.H("NLc", 0, 1536)
        self.H("DX", xs0 / 16, xs1 / 16); self.H("IX", xi0, xi1)
        self.H("DY", ys0 / 16, ys1 / 16)
        w = self.H("IY", yi0, yi1, long=True); assert w & 7 == 6, "IY does not host mask 6"
        MP = ["B23", "B4", "C10"]; ML = ["IY", "C_N"]
        THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
        tab = c["o_tabalu"]
        if tab: tvals = (-(TLO + 1536.0), -float(THI_F), -float(THI_B), -(TLO_H + 1536.0))
        else: tvals = (float(TLO), float(THI_F), float(THI_B), float(TLO_H))
        ftf, ftb = self.F("TF"), self.F("TBH")
        self.ck(ftf != ftb)
        a_tf = self.along(ftf); a_tb = self.along(ftb); a_th = self.along(ftb)
        self.VAL["TF"] = (ftf, a_tf); self.VAL["TB"] = (ftb, a_tb); self.VAL["TH"] = (ftb, a_th)
        A(f'imm ui"0x{fb(tvals[0]):08x}" >$l{ftf}{a_tf} >$l{ftb}{a_tb}', ["TF#lo", "TB#lo"], unit="imm")
        A(f'imm ui"0x{fb(tvals[1]):08x}" >${ftf}{a_tf} >${ftb}{a_th}', ["TF", "TH#hi"], [("TF#lo", ftf)], unit="imm")
        A(f'imm ui"0x{fb(tvals[2]):08x}" >${ftb}{a_tb}', ["TB"], [("TB#lo", ftb)], unit="imm")
        A(f'imm ui"0x{fb(tvals[3]):08x}" >${ftb}{a_th + 1}', ["TH"], unit="imm")
        # D = [0.75 MG, x]
        fd = self.F("D"); a_d = self.along(fd); self.VAL["D"] = (fd, a_d)
        gd = self.mg(FI("KBc1"))
        M(f"fvfma {CL(gd)} -{CE('KBc1')} {CL(gd)} >$l{fd}{a_d}", ["D"], S(gd, "KBc1"))

        # ---------------- coordinates ----------------
        fsl = FI("SL"); assert fsl != "n", "SL must live in a GRF"
        mgsl = self.mg(need=fsl)
        a_tc0 = self.along(fsl); self.VAL["TC0"] = (fsl, a_tc0)
        g0 = self.mg()
        A(f"iadd $l2bid {CL(g0)} >$nowrite", ["o5"], S(g0))
        A(f"iadd $l2bid $aluf >$l{fsl}{a_tc0}", ["TC0"], fwd="o5")
        fl = FI(ML[0]); assert all(FI(m) == fl for m in ML)
        A(f"iand $l1bid $l{fl}[{AD(ML[0])},{AD(ML[1])},{AD(ML[1])},{AD(ML[1])}] >$nowrite", ["o1"], S(*ML))
        mga = AD(mgsl)
        A(f"ior $aluf $l{fsl}[{mga},{a_tc0},{a_tc0},{a_tc0}] >{LV('SL')}", ["SL"], S(mgsl, "TC0"), fwd="o1")
        fpm = FI(MP[0]); assert all(FI(m) == fpm for m in MP)
        A(f"iand $peid $l{fpm}[{AD(MP[0])},{AD(MP[1])},{AD(MP[2])},{AD(MP[2])}] >$nowrite", ["o3"], S(*MP))
        A(f"ior $aluf $l{fsl}[{AD('SL')},{mga},{mga},{mga}] >{LV('RW')}", ["RW"], S("SL", mgsl), fwd="o3")
        A("l1bmd $aluf $lb0", ["LB"], fwd="RW", unit="l1")
        A(f"l1bmm4 $lb0 >{LV('RA')}", ["RA"], [("LB", "b", 3)], unit="l1")
        A(f"l1bmm4 $lb64 >{LV('RB')}", ["RB"], [("LB", "b", 3)], unit="l1")
        self.ck(FI("H8") != FI("K1"))
        M(f"fvfma $lbf {CE('H8')} {CE('K1')} >$nowrite", ["acc1"], S("H8", "K1"), fwd="RA")
        M(f"fvadd $mauf $l{fsl}{AD('SL') + 2} >$nowrite", ["acc2"], S("SL"), fwd="acc1")
        self.ck(FI("H8") != FI("RB"))
        M(f"fvfma $mauf {CE('H8')} {LV('RB')} >{LV('Bv')}", ["Bv"], S("H8", "RB"), fwd="acc2")
        frw = FI("RW")
        kb4 = f"$l{frw}{AD('RW') + 4}"
        self.ck(len({frw, FI("KBc1"), fd}) == 3)
        M(f"fvfma {kb4} {CE('KBc1')} {CL('D')} >{W0('KBv')}", ["KB#0"], S("RW", "KBc1", "D"))
        M(f"fvfma {kb4} {CE('KBc1')} {CL('D')} >{W1('KBv')}", ["KB#1"], S("RW", "KBc1", "D"))
        self.ck(FI("Bv") != FI("H8"))
        M(f"fvmul -{LV('Bv')} {CE('H8')} >{W0('AT')}", ["AT#0"], S("Bv", "H8"))
        if fat in files:
            ga = self.mg(fat)
            M(f"fvpassa {CL(ga)} >{W1('AT')}", ["AT#1"], S(ga))

        # ---------------- estimator ----------------
        for n in ("L23", "Z", "Y1", "mS", "mR"): self.var(n)
        fz, fy = FI("Z"), FI("Y1"); assert fz != fy
        mgp = self.mg()
        M(f"fvpassa -{CL(mgp)} >{W1('Z')} >{W0('Y1')}", ["PRE"], S(mgp))
        self.ck(FI("A23") != FI("B23"))
        M(f"fvfma $mauf {CE('A23')} {CE('B23')} >{LV('L23')}", ["L23"], S("A23", "B23"), fwd="Bv")
        self.ck(len({FI("Bv"), FI("A4"), FI("B4")}) == 3)
        M(f"fvfma {LV('Bv')} {CL('A4')} {CE('B4')} >$nowrite", ["L4"], S("Bv", "A4", "B4"))
        A(f"fmin {LV('L23')} $mauf >$nowrite", ["mn1"], S("L23"), fwd="L4")
        A(f"fmin {W1('L23')} $aluf >{W0('Z')} >{W1('Y1')}", ["Zy"], S("L23"), fwd="mn1")
        M(f"fvadd {LV('Z')} {LV('Y1')} >$nowrite", ["yr"], [("Zy", fz), ("Zy", fy), ("PRE", fz), ("PRE", fy)])
        fkb = FI("KBv")
        self.ck(FI("mS") != FI("mR"))
        M(f"fvadd $mauf {LV('KBv')} >{LV('mS')} >{LV('mR')}", ["mS", "mR"], [("KB#0", fkb), ("KB#1", fkb)], fwd="yr")

        # ---------------- token ----------------
        TT, TE = 0, 2
        for n in ("Wv", "nR", "N0", "us"): self.var(n)
        cands = [m_ for m_ in ("mS", "mR") if len({FI(m_), FI("KBc2"), fat}) == 3]
        self.ck(cands)
        tm = (cands or ["mS"])[0]
        M(f"fvfma {LV(tm)} {CE('KBc2')} {LV('AT')} >$t >{LV('Wv')}", ["T", "W"], S(tm, "KBc2") + [("AT#0", fat), ("AT#1", fat)])
        nm = self.pick(("mS", "mR"), FI("H1516"))
        M(f"fvfma {LV(nm)} {CE('H1516')} {CE('H1516')} >$nowrite", ["nF"], S(nm, "H1516"))
        self.ck(FI("nR") != FI("N0"))
        A(f"ffloor $mauf >{LV('nR')} >{W1('N0')}", ["n", "N0"], fwd="nF")
        um = self.pick(("mS", "mR"), FI("H8"))
        M(f"fvfma {LV(um)} {CE('H8')} $lmt{TE} >{LV('us')}", ["us"],
          S(um, "H8") + [("T", "t"), ("tE1", "m", 3), ("tE2", "m", 3)])

        # ---------------- digits ----------------
        for n in ("R1v", "S1s", "S2r", "N1v", "UAv", "Rv"): self.var(n)
        self.ck(fp != FI("X"))
        M(f"fvfma $aluf {CL('CP')} -{CE('X')} >{LV('R1v')} >$omr1", ["R1"], S("CP", "X"), fwd="n")
        A(f"ffloor $mauf >{LV('S1s')}", ["S1s"], fwd="R1")
        self.ck(fc != fx)
        M(f"fvfma $aluf {CL('C10')} {CL('XC')} >$nowrite", ["R2"], S("C10", "XC"), fwd="S1s")
        A(f"ffloor $mauf >{LV('S2r')}", ["S2r"], fwd="R2")
        self.ck(FI("N0") != FI("C_N"))
        M(f"fvadd {LV('N0')} {CE('C_N')} >{LV('N1v')}", ["N1"], S("N0", "C_N"))
        self.ck(len({FI("S1s"), FI("P_B"), FI("N1v")}) == 3)
        M(f"fvfma/$imr1 {LV('S1s')} {CE('P_B')} {LV('N1v')} >{LV('UAv')}", ["UA"],
          S("S1s", "P_B") + [("N1", FI("N1v")), ("R1", "o", 1)])
        self.ck(len({FI("S2r"), FI("P_A"), FI("cUB")}) == 3)
        M(f"fvfma/$imr2 {LV('S2r')} {CE('P_A')} {CE('cUB')} >$nowrite", ["UB"], S("S2r", "P_A", "cUB") + [("DMn", "o", 1)])
        # ---------------- text ----------------
        frv = FI("Rv")
        M(f"fvadd $lmt{TT} {CE('NLc')} >{LV('Rv')} >$omr5", ["R"], S("NLc") + [("T", "t"), ("tT1", "m", 3), ("tT2", "m", 3)])
        M(f"fvadd/$imr5 $mauf {LV('UAv')} >$nowrite", ["Ys"], [("UA", FI("UAv")), ("R", "o", 1)], fwd="UB")
        self.ck(FI("KBc1") != frv)
        M(f"fvfma $mauf {CE('KBc1')} -{LV('Rv')} >$nowrite", ["V2"], S("KBc1") + [("R", frv)], fwd="Ys")
        A("fftoi $mauf >$nowrite", ["V"], fwd="V2")

        # ---------------- position ----------------
        for n in ("DA", "DMn", "DMs", "Za", "Zb", "Spv", "XA"): self.var(n)
        self.ck(len({FI("us"), FI("DX"), FI("IX")}) == 3 and len({FI("us"), FI("DY"), FI("IY")}) == 3)
        M(f"fvfma {LV('us')} {CE('DX')} {CE('IX')} >{LV('DA')}", ["DA"], S("us", "DX", "IX"))
        M(f"fvfma {LV('us')} {CE('DY')} {CE('IY')} >$nowrite", ["DB"], S("us", "DY", "IY"))
        self.ck(FI("DMn") != FI("DMs"))
        A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')} >$omr2", ["DMn", "DMs"], S("DA"), fwd="DB")
        fza, fzb = FI("Za"), FI("Zb"); assert fza != fzb
        A(f"fmax {W1('DMn')} {LV('DMs')} >{W0('Za')} >{W1('Zb')}", ["Dw"], S("DMn", "DMs"))
        self.ck(FI("nR") != FI("Wv"))
        M(f"fvadd -{LV('nR')} -{LV('Wv')} >{W1('Za')} >{W0('Zb')}", ["NR"], [("n", FI("nR")), ("W", FI("Wv"))])
        M(f"fvadd -{LV('Za')} {LV('Zb')} >{LV('Spv')} >$omr3", ["S"], [("Dw", fza), ("Dw", fzb), ("NR", fza), ("NR", fzb)])
        g3 = self.mg(FI("H8"), FI("Spv"))
        self.ck(FI("H8") != FI("Spv"))
        M(f"fvfma/$imr3 {LV('Spv')} {CE('H8')} {CL(g3)} >{W1('XA')}", ["AM"], S("H8", g3) + [("S", FI("Spv")), ("S", "o", 1)])
        A("ullsr $aluf $mauf >$nowrite", ["F1x"], fwd=["V", "AM"])
        A(f"llsl $aluf {LV('XA')} >$nowrite", ["FO"], [("AM", FI("XA"))], fwd="F1x")
        A("l1bmr4lbor $aluf $lb0", ["OUT"], fwd="FO", unit="l1")

        # ---------------- tables ----------------
        def ad(ids, base): return "[" + ",".join(str(256 * i + base) for i in ids) + "]"
        tb, th = AD("TB"), AD("TH")
        if tab:
            A(f"lpassa {CL('TF')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF"))
            A(f"lpassa $l{ftb}[{tb},{tb},{tb},{th}] >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [("TB", ftb), ("TH", ftb), ("TH#hi", ftb)])
        else:
            self.ck(ftf != FI("NLc") and ftb != FI("NLc"))
            M(f"fvadd -{CL('TF')} -{CE('NLc')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF", "NLc"))
            M(f"fvadd -$l{ftb}[{tb},{tb},{tb},{th}] -{CE('NLc')} >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [("TB", ftb), ("TH", ftb), ("TH#hi", ftb)] + S("NLc"))
        M(f"fvpassa -{CE('H8')} >$lm{ad([0, 6, 10, 12], TE)}", ["tE1"], S("H8"))
        M(f"fvpassa {CE('H8')} >$lm{ad([2, 4, 8, 14], TE)}", ["tE2"], S("H8"))

def valid(ops):
    import sched3
    for o in ops:
        if not sched3.fits({}, 0, o): return False, o["text"]
    return True, None

def violations(cfg):
    try:
        return G(cfg).viol
    except (AssertionError, IndexError, KeyError):
        return 99

if __name__ == "__main__":
    import sched3, json
    from collections import Counter
    cfg = json.load(open(sys.argv[3])) if len(sys.argv) > 3 else None
    g = G(cfg)
    print(Counter(o["unit"] for o in g.OPS), valid(g.OPS))
    tries = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    lines, line_of, seed = sched3.best_schedule(g.OPS, tries=tries)
    text = sched3.render(lines) + "\n".join(TAIL) + "\n"
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v7.vsm"
    open(out, "w").write(text)
    print("compute lines", len(lines), "total", len(lines) + len(TAIL), "seed", seed)
