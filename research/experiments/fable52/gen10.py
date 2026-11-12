#!/usr/bin/env python3
"""v10 generator (math = model10).  build: G(cfg).OPS for sched3.

cfg maps value names to register files (r=GRF0, s=GRF1, n=LM1) plus options:
  o_tabalu  text table written by ALU lpassa from pre-negated constants (else MAU fvadd)
  o_vreg    V goes through a register and the shift-amount op is forwarded from the position sum
  o_ubf     UB takes S2 by forwarding from its floor (needs a scheduler without the group-DAG limit)
  o_tf      T is forwarded from m          o_nff   nF is forwarded from m (ignored when o_tf)
  o_daf     DA is forwarded from us
  o_k1l     the l1bid high bits enter through the acc1 addend (K1 xor bits) instead of the L1BM row,
            so the peid chain does not wait for the l1bid chain; the bias constant becomes MG + 384
  o_xd      X = [1, -1] is derived by two MAU word writes (0.25 * 4) instead of an imm
  o_dyd     DY = [-1/16, -3/16] is derived by two MAU word writes instead of an imm
On top of gen9: no KBc1 constant: hi digit scale 1/16, KK = KBc2*KBc2 = [16, 65536], Q = P_B*KBc2 = [0.25, .],
N0 word0 = 4 - 15/16.
"""
import struct, sys
import numpy as np
from f32util import hpair
from sched3 import op
import model3, model8, model10

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]
BIGV = 16384 * (1 + 56 / 512)

DEFAULT = dict(
    o_tabalu=0, o_vreg=1, o_ubf=0, o_tf=0, o_nff=0, o_daf=0, o_k1l=0, o_xd=0, o_dyd=0,
    MG="rs", MP="r", ML="n",
    H8="n", K1="s", KK="s", Q="r", KBc2="n", B23="n", H1516="n",
    CP="n", XC="s", X="s", P_A="n", P_B="n", cUB="s", NLc="n",
    DX="n", IX="s", DY="s", TF="r", TBH="s", D="n", N23="s", N4="s",
    SL="s", RW="r", RA="r", RB="s", Bv="r", AT="n",
    L23="s", Z="s", Y1="r", mS="s", mR="r", Wv="s",
    nR="r", N0="s", us="s",
    R1v="s", S1s="s", S2r="r", UAv="s", Rv="r", Vreg="r",
    DA="r", DMn="r", DMs="s", Za="r", Zb="s", Spv="r", XA="s",
)
P9 = dict(model10.DEFAULT)

class G:
    SLOW = {"TC0", "CP", "XC", "D", "N23", "N4", "KK", "Q", "X#0", "X#1", "DY#0", "DY#1"}      # written at one address in all 4 cycles: readable 3 lines later
    def __init__(self, cfg=None):
        self.cfg = dict(DEFAULT); self.cfg.update(cfg or {})
        c = self.cfg
        c["B4"] = c["C10"] = c["A4"] = c["MP"]           # hosts of the peid masks 0x38, 0x07, 0x0c
        c["IY"] = c["A23"] = c["ML"]                     # hosts of the l1bid masks 6, 1
        self.P = P9
        self.MGB = 0x4b400180 if c["o_k1l"] else 0x4b400000
        self.MGV = float(np.array([self.MGB], ">u4").view(">f4")[0])
        self.next = {"r": 0, "s": 0, "n": 0, "m": 8}     # LM0 words 8.. are free for lane variables (tables sit at 256*i + off)
        self.OPS = []; self.VAL = {}; self.viol = 0
        self.build()
        self.ck(self.next["m"] <= 128)
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
    def A(self, text, dst=(), src=(), fwd=(), unit="alu", prio=0, at=()):
        self.OPS.append(op(text, unit, dst, src, fwd, prio, at))
    def M(self, text, dst=(), src=(), fwd=(), prio=0, at=()): self.A(text, dst, src, fwd, "mau", prio, at)
    def LV(self, n): f, a = self.VAL[n]; return f"$l{f}{a}v"
    def W0(self, n): f, a = self.VAL[n]; return f"${f}{a}v2"
    def W1(self, n): f, a = self.VAL[n]; return f"${f}{a + 1}v2"
    def CL(self, n): f, a = self.VAL[n]; return f"$l{f}{a}"
    def CE(self, n): f, a = self.VAL[n]; return f"${f}{a}e"
    def AD(self, n): return self.VAL[n][1]
    def FI(self, n): return self.VAL[n][0]
    def S(self, *names): return [(n, self.VAL[n][0], 3) if n in self.SLOW else (n, self.VAL[n][0]) for n in names]
    def H(self, name, a, b, long=False):
        f = self.F(name)
        if long:
            ad = self.along(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >$l{f}{ad}', [name], unit="imm")
        else:
            ad = self.aword(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >${f}{ad}', [name], unit="imm")
        return hpair(a, b)
    def reg(self, name):
        f = self.F(name); a = self.along(f); self.VAL[name] = (f, a); return f"$l{f}{a}"
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
        MGV = self.MGV; k1l = c["o_k1l"]
        (a2, b2), (a3, b3), (a4, b4) = P["lines"]
        A4 = float(np.float32(a4)) * 8.0
        C10 = float(np.float32(P["c10"]))
        (ys0, yi0), (ys1, yi1) = P["Y"]; (xs0, xi0), (xs1, xi1) = P["X"]
        for n in ("SL", "RW", "RA", "RB", "Bv", "AT", "L23", "Z", "Y1", "mS", "mR", "Wv", "nR", "N0", "us"): self.var(n)
        # ---------------- constants ----------------
        files = list(self.F("MG")); fat = FI("AT")
        addrs = {f: self.along(f) for f in files}
        self.VAL["MG"] = (files[0], addrs[files[0]])
        for f in files[1:]: self.VAL["MG@" + f] = (f, addrs[f])
        mgdst = " ".join(f">$l{f}{a}" for f, a in addrs.items()); mgnames = ["MG"] + ["MG@" + f for f in files[1:]]
        if fat not in files:
            mgdst += f" >{W1('AT')}"; mgnames.append("AT#1")
        A(f'imm ui"0x{self.MGB:08x}" {mgdst}', mgnames, unit="imm")
        self.H("H8", 8, 8)
        K1V = -73 * MGV / 8
        if k1l:
            fk = self.F("K1"); a_k1 = self.along(fk); self.VAL["K1"] = (fk, a_k1)
            assert fb(K1V) & 7 == 6 and float(np.float32(K1V)) == K1V
            A(f'imm ui"0x{fb(K1V):08x}" >$l{fk}{a_k1}', ["K1"], unit="imm")
        else:
            self.H("K1", K1V, K1V)
        self.H("KBc2", 4, 256)
        w = self.H("A23", a3 * 8, a2 * 8, long=True); assert w & 7 == 1, "A23 does not host mask 1"
        self.H("B23", b3, b2)
        fa4 = self.F("A4"); a_a4 = self.along(fa4); self.VAL["A4"] = (fa4, a_a4)
        assert fb(A4) & 0x3f == 0x0c, "A4 does not host mask 0x0c"
        A(f'imm ui"0x{fb(A4):08x}" >${fa4}{a_a4}', ["A4"], unit="imm")      # [a4', 0]
        w = self.H("B4", b4, BIGV, long=True); assert w & 0x3f == 0x38
        self.H("H1516", 15 / 16, 15 / 16)
        fc, fp = self.F("C10"), self.F("CP")
        self.ck(fc != fp); assert fb(C10) & 0x3f == 0x07
        a_c10 = self.along(fc); a_cp = self.along(fp)
        self.VAL["C10"] = (fc, a_c10); self.VAL["CP"] = (fp, a_cp)
        A(f'imm ui"0x{fb(C10):08x}" >$l{fc}{a_c10} >$l{fp}{a_cp}', ["C10", "CP#0"], unit="imm")
        M(f"fvmul {CL('C10')} {CL('C10')} >${fp}{a_cp}", ["CP"], [("C10", fc), ("CP#0", fp)])
        self.H("P_A", 15.375, -2560); self.H("P_B", 1 / 16, 246); self.H("cUB", 768, 12288)
        kk = self.reg("KK")
        M(f"fvmul {CE('KBc2')} {CE('KBc2')} >{kk}", ["KK"], S("KBc2"))                    # [16, 65536]
        q = self.reg("Q")
        self.ck(FI("P_B") != FI("KBc2"))
        M(f"fvmul {CE('P_B')} {CE('KBc2')} >{q}", ["Q"], S("P_B", "KBc2"))                # [0.25, .]
        if c["o_xd"]:
            fxr = self.F("X"); a_x = self.along(fxr); self.VAL["X"] = (fxr, a_x)
            self.ck(FI("Q") != FI("KBc2"))
            M(f"fvmul {CL('Q')} {CE('KBc2')} >${fxr}{a_x}", ["X#0"], S("Q", "KBc2"))       # 1
            M(f"fvmul -{CL('Q')} {CE('KBc2')} >${fxr}{a_x + 1}", ["X#1"], S("Q", "KBc2"))  # -1
            XOP = CL("X"); XSRC = [("X#0", fxr, 3), ("X#1", fxr, 3)]
        else:
            self.H("X", 1, -1)
            XOP = CE("X"); XSRC = S("X")
        xc = self.reg("XC"); fx = FI("XC")
        self.ck(FI("X") != fc)
        M(f"fvmul {XOP} {CL('C10')} >{xc}", ["XC"], XSRC + S("C10"))
        fnl = self.F("NLc"); a_nl = self.along(fnl); self.VAL["NLc"] = (fnl, a_nl)
        A(f'imm ui"0x{fb(model8.NLV):08x}" >${fnl}{a_nl + 1}', ["NLc"], unit="imm")      # [0, NLV]
        self.H("DX", xs0 / 16, xs1 / 16); self.H("IX", xi0, xi1)
        if c["o_dyd"]:
            assert (ys0 / 16, ys1 / 16) == (-1 / 16, -3 / 16)
            fdy = self.F("DY"); a_dy = self.along(fdy); self.VAL["DY"] = (fdy, a_dy)
            M(f"fvpassa -{CE('P_B')} >${fdy}{a_dy}", ["DY#0"], S("P_B"))                       # -1/16
            self.ck(FI("Q") != FI("P_B"))
            M(f"fvadd -{CL('Q')} {CE('P_B')} >${fdy}{a_dy + 1}", ["DY#1"], S("Q", "P_B"))       # -3/16
            DYOP = CL("DY"); DYSRC = [("DY#0", fdy, 3), ("DY#1", fdy, 3)]
        else:
            self.H("DY", ys0 / 16, ys1 / 16)
            DYOP = CE("DY"); DYSRC = S("DY")
        w = self.H("IY", yi0, yi1, long=True); assert w & 7 == 6, "IY does not host mask 6"
        MP = ["B4", "C10", "A4"]; ML = ["IY", "A23"]         # masks 0x38, 0x07, 0x0c ; 6, 1
        THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
        tab = c["o_tabalu"]
        if tab: tvals = (-(TLO + model8.NLV), -float(THI_F), -float(THI_B), -(TLO_H + model8.NLV))
        else: tvals = (float(TLO), float(THI_F), float(THI_B), float(TLO_H))
        ftf, ftb = self.F("TF"), self.F("TBH")
        self.ck(ftf != ftb)
        a_tf = self.along(ftf); a_tb = self.along(ftb); a_th = self.along(ftb)
        self.VAL["TF"] = (ftf, a_tf); self.VAL["TB"] = (ftb, a_tb); self.VAL["TH"] = (ftb, a_th)
        A(f'imm ui"0x{fb(tvals[0]):08x}" >$l{ftf}{a_tf} >$l{ftb}{a_tb}', ["TF#lo", "TB#lo"], unit="imm")
        A(f'imm ui"0x{fb(tvals[1]):08x}" >${ftf}{a_tf} >${ftb}{a_th}', ["TF", "TH#hi"], [("TF#lo", ftf)], unit="imm")
        A(f'imm ui"0x{fb(tvals[2]):08x}" >${ftb}{a_tb}', ["TB"], [("TB#lo", ftb)], unit="imm")
        A(f'imm ui"0x{fb(tvals[3]):08x}" >${ftb}{a_th + 1}', ["TH"], unit="imm")
        # derived constants
        d = self.reg("D"); fd = FI("D")
        gd = self.mg(FI("Q"))
        M(f"fvfma {CL(gd)} -{CL('Q')} {CL(gd)} >{d}", ["D"], S(gd, "Q"))              # [0.75 MG, x]
        n23 = self.reg("N23"); g23 = self.mg(FI("B23"))
        M(f"fvadd {CE('B23')} -{CL(g23)} >{n23}", ["N23"], S("B23", g23))
        n4 = self.reg("N4"); g4 = self.mg(FI("B4"))
        M(f"fvadd {CE('B4')} -{CL(g4)} >{n4}", ["N4"], S("B4", g4))
        self.ck(FI("KBc2") != FI("H1516"))
        M(f"fvadd {CE('KBc2')} -{CE('H1516')} >{W0('N0')}", ["N0#0"], S("KBc2", "H1516"))   # 49/16

        # ---------------- coordinates ----------------
        fsl = FI("SL"); assert fsl != "n", "SL must live in a GRF"
        g0 = self.mg()
        fl = FI(ML[0]); assert all(FI(m) == fl for m in ML)
        fpm = FI(MP[0]); assert all(FI(m) == fpm for m in MP)
        if k1l:
            fk = FI("K1")
            a_tc0 = self.along(fk); self.VAL["TC0"] = (fk, a_tc0)
            A(f"iadd $l2bid {CL(g0)} >$nowrite", ["o5"], S(g0))
            A(f"iadd $l2bid $aluf >$l{fk}{a_tc0}", ["TC0"], fwd="o5")
            A(f"iand $l1bid $l{fl}[{AD(ML[0])},{AD(ML[1])},{AD(ML[1])},{AD(ML[1])}] >$nowrite", ["o1"], S(*ML))
            self.ck(not (fk == "n" and fsl == "n"))
            A(f"ixor $aluf $l{fk}[{AD('K1')},{a_tc0},{a_tc0},{a_tc0}] >{LV('SL')}", ["SL"], S("K1", "TC0"), fwd="o1")
            A(f"iand $peid $l{fpm}[{AD(MP[0])},{AD(MP[1])},{AD(MP[2])},{AD(MP[2])}] >$nowrite", ["o3"], S(*MP))
            gr = self.mg()
            A(f"ior $aluf {CL(gr)} >{LV('RW')}", ["RW"], S(gr), fwd="o3")
        else:
            mgsl = self.mg(need=fsl)
            a_tc0 = self.along(fsl); self.VAL["TC0"] = (fsl, a_tc0)
            A(f"iadd $l2bid {CL(g0)} >$nowrite", ["o5"], S(g0))
            A(f"iadd $l2bid $aluf >$l{fsl}{a_tc0}", ["TC0"], fwd="o5")
            A(f"iand $l1bid $l{fl}[{AD(ML[0])},{AD(ML[1])},{AD(ML[1])},{AD(ML[1])}] >$nowrite", ["o1"], S(*ML))
            mga = AD(mgsl)
            A(f"ior $aluf $l{fsl}[{mga},{a_tc0},{a_tc0},{a_tc0}] >{LV('SL')}", ["SL"], S(mgsl, "TC0"), fwd="o1")
            A(f"iand $peid $l{fpm}[{AD(MP[0])},{AD(MP[1])},{AD(MP[2])},{AD(MP[2])}] >$nowrite", ["o3"], S(*MP))
            A(f"ior $aluf $l{fsl}[{AD('SL')},{mga},{mga},{mga}] >{LV('RW')}", ["RW"], S("SL", mgsl), fwd="o3")
        A("l1bmd $aluf $lb0", ["LB"], fwd="RW", unit="l1")
        A(f"l1bmm4 $lb0 >{LV('RA')}", ["RA"], [("LB", "b", 3)], unit="l1")
        A(f"l1bmm4 $lb64 >{LV('RB')}", ["RB"], [("LB", "b", 3)], unit="l1")
        if k1l:
            self.ck(FI("H8") != fsl)
            M(f"fvfma $lbf {CE('H8')} $l{fsl}{AD('SL')} >$nowrite", ["acc1"], S("H8", "SL"), fwd="RA")
        else:
            self.ck(FI("H8") != FI("K1"))
            M(f"fvfma $lbf {CE('H8')} {CE('K1')} >$nowrite", ["acc1"], S("H8", "K1"), fwd="RA")
        M(f"fvadd $mauf $l{fsl}{AD('SL') + 2} >$nowrite", ["acc2"], S("SL"), fwd="acc1")
        self.ck(FI("H8") != FI("RB"))
        M(f"fvfma $mauf {CE('H8')} {LV('RB')} >{LV('Bv')}", ["Bv"], S("H8", "RB"), fwd="acc2")
        frw = FI("RW")
        kb4 = f"$l{frw}{AD('RW') + 4}"
        fz, fy = FI("Z"), FI("Y1"); assert fz != fy
        self.ck(len({frw, FI("Q"), fd}) == 3)
        M(f"fvfma {kb4} {CL('Q')} {CL('D')} >{W1('Z')} >{W0('Y1')}", ["KB"], [("RW", frw, 3)] + S("Q", "D"))
        self.ck(FI("Bv") != FI("H8"))
        M(f"fvmul -{LV('Bv')} {CE('H8')} >{W0('AT')}", ["AT#0"], S("Bv", "H8"))
        if fat in files:
            ga = self.mg(need=fat)
            M(f"fvpassa {CL(ga)} >{W1('AT')}", ["AT#1"], S(ga))

        # ---------------- estimator (individually rounded lines) ----------------
        self.ck(FI("A23") != FI("N23"))
        M(f"fvfma $mauf {CE('A23')} {CL('N23')} >{LV('L23')}", ["L23"], S("A23", "N23"), fwd="Bv")
        self.ck(len({FI("Bv"), FI("A4"), FI("N4")}) == 3)
        M(f"fvfma {LV('Bv')} {CL('A4')} {CL('N4')} >$nowrite", ["L4"], S("Bv", "A4", "N4"))
        A(f"fmin {LV('L23')} $mauf >$nowrite", ["mn1"], S("L23"), fwd="L4")
        A(f"fmin {W1('L23')} $aluf >{W0('Z')} >{W1('Y1')}", ["Zy"], S("L23"), fwd="mn1")
        self.ck(FI("mS") != FI("mR"))
        M(f"fvadd {LV('Z')} {LV('Y1')} >{LV('mS')} >{LV('mR')}", ["mS", "mR"], [("Zy", fz), ("Zy", fy), ("KB", fz), ("KB", fy)])

        # ---------------- token ----------------
        TT, TE = 0, 2
        toff = self.MGB & 0xfff                       # table addresses follow the low bits of the bias
        if c["o_tf"]:
            self.ck(FI("KBc2") != fat)
            M(f"fvfma $mauf {CE('KBc2')} {LV('AT')} >$t >{LV('Wv')}", ["T", "W"], S("KBc2") + [("AT#0", fat), ("AT#1", fat)], fwd="mS")
        else:
            cands = [m_ for m_ in ("mS", "mR") if len({FI(m_), FI("KBc2"), fat}) == 3]
            self.ck(cands)
            tm = (cands or ["mS"])[0]
            M(f"fvfma {LV(tm)} {CE('KBc2')} {LV('AT')} >$t >{LV('Wv')}", ["T", "W"], S(tm, "KBc2") + [("AT#0", fat), ("AT#1", fat)])
        if c["o_nff"] and not c["o_tf"]:
            M(f"fvfma $mauf {CE('H1516')} {CE('H1516')} >$nowrite", ["nF"], S("H1516"), fwd="mS")
        else:
            nm = self.pick(("mS", "mR"), FI("H1516"))
            M(f"fvfma {LV(nm)} {CE('H1516')} {CE('H1516')} >$nowrite", ["nF"], S(nm, "H1516"))
        self.ck(FI("nR") != FI("N0"))
        A(f"ffloor $mauf >{LV('nR')} >{W1('N0')}", ["n", "N0"], fwd="nF")
        um = self.pick(("mS", "mR"), FI("H8"))
        M(f"fvfma {LV(um)} {CE('H8')} $lmt{TE} >{LV('us')}", ["us"],
          S(um, "H8") + [("T", "t"), ("tE1", "m", 3), ("tE2", "m", 3)])

        # ---------------- digits ----------------
        for n in ("R1v", "S1s", "S2r", "UAv", "Rv", "Vreg"): self.var(n)
        self.ck(fp != FI("X"))
        M(f"fvfma $aluf {CL('CP')} -{XOP} >{LV('R1v')} >$omr1", ["R1"], S("CP") + XSRC, fwd="n")
        A(f"ffloor $mauf >{LV('S1s')}", ["S1s"], fwd="R1")
        self.ck(fc != fx)
        M(f"fvfma $aluf {CL('C10')} {CL('XC')} >$nowrite", ["R2"], S("C10", "XC"), fwd="S1s")
        A(f"ffloor $mauf >{LV('S2r')}", ["S2r"], fwd="R2")
        self.ck(len({FI("S1s"), FI("P_B"), FI("N0")}) == 3)
        M(f"fvfma/$imr1 {LV('S1s')} {CE('P_B')} {LV('N0')} >{LV('UAv')}", ["UA"],
          S("S1s", "P_B") + [("N0", FI("N0")), ("N0#0", FI("N0")), ("R1", "o", 1)],
          at=[("S2r", 0)] if c["o_ubf"] else ())            # with UB forwarded, UA shares the line of the S2 floor
        if c["o_ubf"]:
            self.ck(FI("P_A") != FI("cUB"))
            M(f"fvfma/$imr2 $aluf {CE('P_A')} {CE('cUB')} >$nowrite", ["UB"], S("P_A", "cUB") + [("DMn", "o", 1)], fwd="S2r")
        else:
            self.ck(len({FI("S2r"), FI("P_A"), FI("cUB")}) == 3)
            M(f"fvfma/$imr2 {LV('S2r')} {CE('P_A')} {CE('cUB')} >$nowrite", ["UB"], S("S2r", "P_A", "cUB") + [("DMn", "o", 1)])
        # ---------------- text ----------------
        frv = FI("Rv")
        M(f"fvadd $lmt{TT} {CL('NLc')} >{LV('Rv')} >$omr5", ["R"], S("NLc") + [("T", "t"), ("tT1", "m", 3), ("tT2", "m", 3)])
        M(f"fvadd/$imr5 $mauf {LV('UAv')} >$nowrite", ["Ys"], [("UA", FI("UAv")), ("R", "o", 1)], fwd="UB")
        self.ck(FI("KK") != frv)
        M(f"fvfma $mauf {CL('KK')} -{LV('Rv')} >$nowrite", ["V2"], S("KK") + [("R", frv)], fwd="Ys")

        # ---------------- position ----------------
        for n in ("DA", "DMn", "DMs", "Za", "Zb", "Spv", "XA"): self.var(n)
        self.ck(len({FI("us"), FI("DY"), FI("IY")}) == 3)
        DYOP_, DYSRC_ = DYOP, DYSRC
        if c["o_daf"]:
            self.ck(FI("DX") != FI("IX"))
            M(f"fvfma $mauf {CE('DX')} {CE('IX')} >{LV('DA')}", ["DA"], S("DX", "IX"), fwd="us")
        else:
            self.ck(len({FI("us"), FI("DX"), FI("IX")}) == 3)
            M(f"fvfma {LV('us')} {CE('DX')} {CE('IX')} >{LV('DA')}", ["DA"], S("us", "DX", "IX"))
        M(f"fvfma {LV('us')} {DYOP_} {CE('IY')} >$nowrite", ["DB"], S("us", "IY") + DYSRC_)
        self.ck(FI("DMn") != FI("DMs"))
        A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')} >$omr2", ["DMn", "DMs"], S("DA"), fwd="DB")
        fza, fzb = FI("Za"), FI("Zb"); assert fza != fzb
        A(f"fmax {W1('DMn')} {LV('DMs')} >{W0('Za')} >{W1('Zb')}", ["Dw"], S("DMn", "DMs"))
        self.ck(FI("nR") != FI("Wv"))
        M(f"fvadd -{LV('nR')} -{LV('Wv')} >{W1('Za')} >{W0('Zb')}", ["NR"], [("n", FI("nR")), ("W", FI("Wv"))])
        M(f"fvadd -{LV('Za')} {LV('Zb')} >{LV('Spv')} >$omr3", ["S"], [("Dw", fza), ("Dw", fzb), ("NR", fza), ("NR", fzb)])
        if c["o_vreg"]:
            g3 = self.mg(FI("H8"))
            M(f"fvfma/$imr3 $mauf {CE('H8')} {CL(g3)} >{W1('XA')}", ["AM"], S("H8", g3) + [("S", "o", 1)], fwd="S")
            A(f"fftoi $mauf >{LV('Vreg')}", ["V"], fwd="V2")
            A(f"ullsr {LV('Vreg')} $mauf >$nowrite", ["F1x"], [("V", FI("Vreg"))], fwd="AM")
        else:
            g3 = self.mg(FI("H8"), FI("Spv"))
            self.ck(FI("H8") != FI("Spv"))
            M(f"fvfma/$imr3 {LV('Spv')} {CE('H8')} {CL(g3)} >{W1('XA')}", ["AM"], S("H8", g3) + [("S", FI("Spv")), ("S", "o", 1)])
            A("fftoi $mauf >$nowrite", ["V"], fwd="V2")
            A("ullsr $aluf $mauf >$nowrite", ["F1x"], fwd=["V", "AM"])
        A(f"llsl $aluf {LV('XA')} >$nowrite", ["FO"], [("AM", FI("XA"))], fwd="F1x")
        A("l1bmr4lbor $aluf $lb0", ["OUT"], fwd="FO", unit="l1")

        # ---------------- tables ----------------
        def ad(ids, base): return "[" + ",".join(str((256 * i + toff) % 4096 + base) for i in ids) + "]"
        tb, th = AD("TB"), AD("TH")
        if tab:
            A(f"lpassa {CL('TF')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF"))
            A(f"lpassa $l{ftb}[{tb},{tb},{tb},{th}] >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [("TB", ftb), ("TH", ftb), ("TH#hi", ftb)])
        else:
            self.ck(ftf != FI("NLc") and ftb != FI("NLc"))
            M(f"fvadd -{CL('TF')} -{CL('NLc')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF", "NLc"))
            M(f"fvadd -$l{ftb}[{tb},{tb},{tb},{th}] -{CL('NLc')} >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
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
    print(Counter(o["unit"] for o in g.OPS), "violations", g.viol)
    tries = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    lines, line_of, seed = sched3.best_schedule(g.OPS, tries=tries)
    text = sched3.render(lines) + "\n".join(TAIL) + "\n"
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v9.vsm"
    open(out, "w").write(text)
    print("compute lines", len(lines), "total", len(lines) + len(TAIL), "seed", seed)
