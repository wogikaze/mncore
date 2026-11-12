#!/usr/bin/env python3
"""v13 generator (math = model9).  build: G(cfg).OPS for sched3.

cfg maps value names to register files (r=GRF0, s=GRF1, n=LM1, m=LM0 words 8..127 for lane variables) plus options:
  o_tabalu  text table written by ALU lpassa        o_mtab  all LM0 tables written through the matrix registers
  o_vreg    V goes through a register and the shift-amount op is forwarded from the position sum
  o_ubf     UB takes S2 by forwarding from its floor (UA then shares the line of the S2 floor)
  o_tf      T is forwarded from m        o_nff  nF is forwarded from m (ignored when o_tf)       o_daf  DA forwarded from us
  o_xd      X = [1, -1] derived (0.25 * 4)          o_dyd   DY = [-1/16, -3/16] derived from 0.25
  o_hd      [15/16]^2 derived (1 - 1/16)            o_h8d   [8, 8] derived (4 + 4)
  o_lhd     FizzH low word derived from the Fizz one (needs o_mtab)
  o_wm      constants in GRF are written in the first cycle only (/1000) so that they are readable 2 lines later
Fixed design: l1bid high bits through the acc1 addend (K1 xor bits, bias MG + 384); masks hosted in B4, C10, A4
(peid) and K1, A23 (l1bid); hi digit scale 0.25; KB = 0.25 * (kb4 - MG) + MG; individually rounded estimator lines.
"""
import struct, sys
import numpy as np
from f32util import hpair
from sched3 import op
import model3, model8, model9

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]
BIGV = 16384 * (1 + 56 / 512)
MGB = 0x4b400180
MGV = float(np.array([MGB], ">u4").view(">f4")[0])
OPTS = ("o_tabalu", "o_mtab", "o_vreg", "o_ubf", "o_tf", "o_nff", "o_daf", "o_xd", "o_dyd", "o_hd", "o_h8d", "o_lhd", "o_wm")

DEFAULT = dict(
    o_tabalu=0, o_mtab=0, o_vreg=1, o_ubf=0, o_tf=1, o_nff=0, o_daf=1, o_xd=0, o_dyd=0, o_hd=0, o_h8d=0, o_lhd=0, o_wm=1,
    MG="rs", MP="r", ML="s",
    H8="n", KBc1="s", KBc2="n", B23="n", H1516="n",
    CP="n", XC="s", X="s", P_A="n", P_B="n", cUB="s", NLc="n",
    DX="n", IX="s", DY="s", IY="r", TF="r", TBH="s", N23="s", N4="s",
    SL="s", RW="r", RA="r", RB="s", Bv="r", AT="n", KBU="s",
    L23="s", Z="s", Y1="r", mS="s", mR="r", Wv="s",
    nR="r", N0="s", us="s",
    R1v="s", S1s="s", S2r="r", UAv="s", Rv="r", Vreg="r",
    DA="r", DMn="r", DMs="s", Za="r", Zb="s", Spv="r", XA="s",
)
P9 = dict(model9.DEFAULT)

class G:
    def __init__(self, cfg=None):
        self.cfg = dict(DEFAULT); self.cfg.update(cfg or {})
        c = self.cfg
        c["B4"] = c["C10"] = c["A4"] = c["MP"]           # hosts of the peid masks 0x38, 0x07, 0x0c
        c["K1"] = c["A23"] = c["ML"]                     # hosts of the l1bid masks 6, 1 (TC0 lives there too)
        self.P = P9
        self.next = {"r": 0, "s": 0, "n": 0, "m": 8}
        self.OPS = []; self.VAL = {}; self.LAT = {}; self.viol = 0
        self.build()
        self.ck(self.next["m"] <= 128)
        import sched3
        for o in self.OPS:
            if not sched3.fits({}, 0, o): self.viol += 1
    # ---- helpers ----
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
    def S(self, *names):
        return [(n, self.VAL[n][0], self.LAT[n]) if n in self.LAT else (n, self.VAL[n][0]) for n in names]
    def wm(self, f):
        """write-mask suffix and resulting latency for a register written at one address in all cycles"""
        if self.cfg["o_wm"] and f in "rs": return "/1000", 2
        return "", 3
    def H(self, name, a, b, long=False):
        """half-pair imm constant (long=True: same word twice, usable as a mask long)"""
        f = self.F(name); sfx, lat = self.wm(f)
        ad = self.along(f) if long else self.aword(f)
        self.VAL[name] = (f, ad); self.LAT[name] = lat
        self.A(f'imm ui"0x{hpair(a, b):08x}" >${"l" if long else ""}{f}{ad}{sfx}', [name], unit="imm")
        return hpair(a, b)
    def immf(self, name, value, long=True, hi_only=False):
        """float imm: long dup, or (hi_only) word 0 of a fresh zero long"""
        f = self.F(name); sfx, lat = self.wm(f)
        ad = self.along(f); self.VAL[name] = (f, ad); self.LAT[name] = lat
        self.A(f'imm ui"0x{fb(value):08x}" >${"" if hi_only else "l"}{f}{ad}{sfx}', [name], unit="imm")
        return fb(value)
    def dreg(self, name, parts=1):
        """derived constant register (written by MAU/ALU ops at one address): returns (file, addr, suffix)"""
        f = self.F(name); sfx, lat = self.wm(f)
        a = self.along(f); self.VAL[name] = (f, a)
        if parts == 1: self.LAT[name] = lat
        self.DLAT = lat
        return f, a, sfx
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
        for n in ("SL", "RW", "RA", "RB", "Bv", "AT", "KBU", "L23", "Z", "Y1", "mS", "mR", "Wv", "nR", "N0", "us"): self.var(n)
        # ---------------- constants ----------------
        files = list(self.F("MG")); fat = FI("AT")
        addrs = {f: self.along(f) for f in files}
        self.VAL["MG"] = (files[0], addrs[files[0]])
        for f in files[1:]: self.VAL["MG@" + f] = (f, addrs[f])
        mgnames = ["MG"] + ["MG@" + f for f in files[1:]]
        for nm in mgnames: self.LAT[nm] = self.wm(self.VAL[nm][0])[1]
        mgdst = " ".join(f">$l{f}{a}{self.wm(f)[0]}" for f, a in addrs.items())
        if fat not in files:
            mgdst += f" >{W1('AT')}"; mgnames.append("AT#1")
        A(f'imm ui"0x{MGB:08x}" {mgdst}', mgnames, unit="imm")
        K1V = -73 * MGV / 8
        assert fb(K1V) & 7 == 6 and float(np.float32(K1V)) == K1V
        self.immf("K1", K1V)                                          # also the l1bid mask 6
        self.H("KBc2", 4, 256)
        if c["o_h8d"]:
            fh8, a_h8, sfx = self.dreg("H8", 2)
            self.ck(fh8 != FI("KBc2"))
            M(f"fvadd {CE('KBc2')} {CE('KBc2')} >${fh8}{a_h8}{sfx}", ["H8#0"], S("KBc2"))          # 8
            M(f"fvadd {CE('KBc2')} {CE('KBc2')} >${fh8}{a_h8 + 1}{sfx}", ["H8#1"], S("KBc2"))
            H8 = CL("H8"); H8S = [("H8#0", fh8, self.DLAT), ("H8#1", fh8, self.DLAT)]
        else:
            self.H("H8", 8, 8)
            H8 = CE("H8"); H8S = S("H8")
        w = self.H("A23", a3 * 8, a2 * 8, long=True); assert w & 7 == 1, "A23 does not host mask 1"
        self.H("B23", b3, b2)
        assert fb(A4) & 0x3f == 0x0c, "A4 does not host mask 0x0c"
        self.immf("A4", A4, hi_only=True)                             # [a4', 0]
        w = self.H("B4", b4, BIGV, long=True); assert w & 0x3f == 0x38
        fc, fp = self.F("C10"), self.F("CP")
        self.ck(fc != fp); assert fb(C10) & 0x3f == 0x07
        a_c10 = self.along(fc); a_cp = self.along(fp)
        self.VAL["C10"] = (fc, a_c10); self.VAL["CP"] = (fp, a_cp)
        s1, l1 = self.wm(fc); s2, l2 = self.wm(fp)
        self.LAT["C10"] = l1; self.LAT["CP#0"] = l2
        A(f'imm ui"0x{fb(C10):08x}" >$l{fc}{a_c10}{s1} >$l{fp}{a_cp}{s2}', ["C10", "CP#0"], unit="imm")
        M(f"fvmul {CL('C10')} {CL('C10')} >${fp}{a_cp}{s2}", ["CP"], [("C10", fc, l1), ("CP#0", fp, l2)])
        self.LAT["CP"] = l2
        self.H("P_A", 61.5, -2560); self.H("P_B", 0.25, 246); self.H("cUB", 3072, 12288)
        self.H("KBc1", 4, 65536)
        if c["o_xd"]:
            fxr, a_x, sfx = self.dreg("X", 2)
            self.ck(FI("P_B") != FI("KBc2"))
            M(f"fvmul {CE('P_B')} {CE('KBc2')} >${fxr}{a_x}{sfx}", ["X#0"], S("P_B", "KBc2"))       # 1
            M(f"fvmul -{CE('P_B')} {CE('KBc2')} >${fxr}{a_x + 1}{sfx}", ["X#1"], S("P_B", "KBc2"))  # -1
            XOP = CL("X"); XSRC = [("X#0", fxr, self.DLAT), ("X#1", fxr, self.DLAT)]
        else:
            self.H("X", 1, -1)
            XOP = CE("X"); XSRC = S("X")
        if c["o_dyd"]:
            assert (ys0 / 16, ys1 / 16) == (-1 / 16, -3 / 16)
            fdy, a_dy, sfx = self.dreg("DY", 2)
            M(f"fvmul -{CE('P_B')} {CE('P_B')} >${fdy}{a_dy}{sfx}", ["DY#0"], S("P_B"))                # -1/16
            M(f"fvfma {CE('P_B')} {CE('P_B')} -{CE('P_B')} >${fdy}{a_dy + 1}{sfx}", ["DY#1"], S("P_B"))  # -3/16
            DYOP = CL("DY"); DYSRC = [("DY#0", fdy, self.DLAT), ("DY#1", fdy, self.DLAT)]
        else:
            self.H("DY", ys0 / 16, ys1 / 16)
            DYOP = CE("DY"); DYSRC = S("DY")
        if c["o_hd"]:
            fhh, a_hh, sfx = self.dreg("H1516", 2)
            self.ck(len({FI("P_B"), FI("KBc2"), FI("DY")}) == 3)
            M(f"fvfma {CE('P_B')} {CE('KBc2')} {DYOP} >${fhh}{a_hh}{sfx}", ["H#0"], S("P_B", "KBc2") + DYSRC)      # 1 - 1/16
            M(f"fvfma {CE('P_B')} {CE('KBc2')} {DYOP} >${fhh}{a_hh + 1}{sfx}", ["H#1"], S("P_B", "KBc2") + DYSRC)
            HH = CL("H1516"); HHS = [("H#0", fhh, self.DLAT), ("H#1", fhh, self.DLAT)]
        else:
            self.H("H1516", 15 / 16, 15 / 16)
            HH = CE("H1516"); HHS = S("H1516")
        fx, a_xc, sfx = self.dreg("XC")
        self.ck(FI("X") != fc)
        M(f"fvmul {XOP} {CL('C10')} >$l{fx}{a_xc}{sfx}", ["XC"], XSRC + S("C10"))                    # [c10, -c10]
        fnl = self.F("NLc"); a_nl = self.along(fnl); self.VAL["NLc"] = (fnl, a_nl)
        sfx, self.LAT["NLc"] = self.wm(fnl)
        A(f'imm ui"0x{fb(model8.NLV):08x}" >${fnl}{a_nl + 1}{sfx}', ["NLc"], unit="imm")            # [0, NLV]
        self.H("DX", xs0 / 16, xs1 / 16); self.H("IX", xi0, xi1); self.H("IY", yi0, yi1)
        MP = ["B4", "C10", "A4"]; ML = ["K1", "A23"]         # masks 0x38, 0x07, 0x0c ; 6, 1
        THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
        tab = c["o_tabalu"]; mtab = c["o_mtab"]
        ftf, ftb = self.F("TF"), self.F("TBH")
        if mtab:
            a_hbf = self.along(ftf); a_lo = self.along(ftf); a_lh = self.along(ftf)
            self.VAL["HBF"] = (ftf, a_hbf); self.VAL["LOd"] = (ftf, a_lo); self.VAL["LHd"] = (ftf, a_lh)
            sfx, lat = self.wm(ftf)
            A(f'imm ui"0x{fb(-float(THI_B)):08x}" >${ftf}{a_hbf}{sfx}', ["HBF#0"], unit="imm")
            A(f'imm ui"0x{fb(-float(THI_F)):08x}" >${ftf}{a_hbf + 1}{sfx}', ["HBF#1"], unit="imm")
            A(f'imm ui"0x{fb(-(TLO + model8.NLV)):08x}" >$l{ftf}{a_lo}{sfx}', ["LOd"], unit="imm")
            for nm in ("HBF#0", "HBF#1", "LOd"): self.LAT[nm] = lat
            if c["o_lhd"]:
                self.ck(ftf != FI("P_A"))
                M(f"fvadd {CL('LOd')} -{CE('P_A')} >$l{ftf}{a_lh}{sfx}", ["LHd"], [("LOd", ftf, lat)] + S("P_A"))
            else:
                A(f'imm ui"0x{fb(-(TLO_H + model8.NLV)):08x}" >$l{ftf}{a_lh}{sfx}', ["LHd"], unit="imm")
            self.LAT["LHd"] = lat
        else:
            if tab: tvals = (-(TLO + model8.NLV), -float(THI_F), -float(THI_B), -(TLO_H + model8.NLV))
            else: tvals = (float(TLO), float(THI_F), float(THI_B), float(TLO_H))
            self.ck(ftf != ftb)
            a_tf = self.along(ftf); a_tb = self.along(ftb); a_th = self.along(ftb)
            self.VAL["TF"] = (ftf, a_tf); self.VAL["TB"] = (ftb, a_tb); self.VAL["TH"] = (ftb, a_th)
            sf, lf = self.wm(ftf); sb, lb = self.wm(ftb)
            A(f'imm ui"0x{fb(tvals[0]):08x}" >$l{ftf}{a_tf}{sf} >$l{ftb}{a_tb}{sb}', ["TF#lo", "TB#lo"], unit="imm")
            A(f'imm ui"0x{fb(tvals[1]):08x}" >${ftf}{a_tf}{sf} >${ftb}{a_th}{sb}', ["TF", "TH#hi"], [("TF#lo", ftf, lf)], unit="imm")
            A(f'imm ui"0x{fb(tvals[2]):08x}" >${ftb}{a_tb}{sb}', ["TB"], [("TB#lo", ftb, lb)], unit="imm")
            A(f'imm ui"0x{fb(tvals[3]):08x}" >${ftb}{a_th + 1}{sb}', ["TH"], unit="imm")
            self.LAT.update({"TF#lo": lf, "TF": lf, "TB#lo": lb, "TB": lb, "TH": lb, "TH#hi": lb})
        # derived estimator intercepts and the constant word of N0
        f23, a23r, sfx = self.dreg("N23"); g23 = self.mg(FI("B23"))
        M(f"fvadd {CE('B23')} -{CL(g23)} >$l{f23}{a23r}{sfx}", ["N23"], S("B23", g23))
        f4, a4r, sfx = self.dreg("N4"); g4 = self.mg(FI("B4"))
        M(f"fvadd {CE('B4')} -{CL(g4)} >$l{f4}{a4r}{sfx}", ["N4"], S("B4", g4))
        self.ck(len({FI("B23"), FI("H1516"), FI("DY")}) == 3)
        M(f"fvfma {CE('B23')} {HH} -{DYOP} >{W0('N0')}", ["N0#0"], S("B23") + HHS + DYSRC)           # 13*15/16 + 1/16 = 12.25

        # ---------------- coordinates ----------------
        fsl = FI("SL"); self.ck(fsl in "rs")
        fk = FI("K1"); assert FI("A23") == fk
        fpm = FI(MP[0]); assert all(FI(m) == fpm for m in MP)
        g0 = self.mg()
        sfx, lat0 = self.wm(fk)
        a_tc0 = self.along(fk); self.VAL["TC0"] = (fk, a_tc0); self.LAT["TC0"] = lat0
        A(f"iadd $l2bid {CL(g0)} >$nowrite", ["o5"], S(g0))
        A(f"iadd $l2bid $aluf >$l{fk}{a_tc0}{sfx}", ["TC0"], fwd="o5")
        A(f"iand $l1bid $l{fk}[{AD('K1')},{AD('A23')},{AD('A23')},{AD('A23')}] >$nowrite", ["o1"], S("K1", "A23"))
        self.ck(not (fk == "n" and fsl == "n"))
        A(f"ixor $aluf $l{fk}[{AD('K1')},{a_tc0},{a_tc0},{a_tc0}] >{LV('SL')}", ["SL"], S("K1", "TC0"), fwd="o1")
        A(f"iand $peid $l{fpm}[{AD(MP[0])},{AD(MP[1])},{AD(MP[2])},{AD(MP[2])}] >$nowrite", ["o3"], S(*MP))
        gr = self.mg()
        A(f"ior $aluf {CL(gr)} >{LV('RW')}", ["RW"], S(gr), fwd="o3")
        A("l1bmd $aluf $lb0", ["LB"], fwd="RW", unit="l1")
        A(f"l1bmm4 $lb0 >{LV('RA')}", ["RA"], [("LB", "b", 3)], unit="l1")
        A(f"l1bmm4 $lb64 >{LV('RB')}", ["RB"], [("LB", "b", 3)], unit="l1")
        self.ck(FI("H8") != fsl)
        M(f"fvfma $lbf {H8} $l{fsl}{AD('SL')} >$nowrite", ["acc1"], H8S + S("SL"), fwd="RA")
        M(f"fvadd $mauf $l{fsl}{AD('SL') + 2} >$nowrite", ["acc2"], S("SL"), fwd="acc1")
        self.ck(FI("H8") != FI("RB"))
        M(f"fvfma $mauf {H8} {LV('RB')} >{LV('Bv')}", ["Bv"], H8S + S("RB"), fwd="acc2")
        frw = FI("RW")
        kb4 = f"$l{frw}{AD('RW') + 4}"
        fz, fy = FI("Z"), FI("Y1"); assert fz != fy
        gk = self.mg(frw)
        M(f"fvadd {kb4} -{CL(gk)} >{LV('KBU')}", ["KBU"], [("RW", frw, 3)] + S(gk))             # 4k
        gq = self.mg(FI("KBU"), FI("P_B"))
        self.ck(FI("KBU") != FI("P_B"))
        M(f"fvfma {LV('KBU')} {CE('P_B')} {CL(gq)} >{W1('Z')} >{W0('Y1')}", ["KB"], S("KBU", "P_B", gq))   # MG + k
        self.ck(FI("Bv") != FI("H8"))
        M(f"fvmul -{LV('Bv')} {H8} >{W0('AT')}", ["AT#0"], S("Bv") + H8S)
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
        toff = MGB & 0xfff
        if c["o_tf"]:
            self.ck(FI("KBc2") != fat)
            M(f"fvfma $mauf {CE('KBc2')} {LV('AT')} >$t >{LV('Wv')}", ["T", "W"], S("KBc2") + [("AT#0", fat), ("AT#1", fat)], fwd="mS")
        else:
            cands = [m_ for m_ in ("mS", "mR") if len({FI(m_), FI("KBc2"), fat}) == 3]
            self.ck(cands)
            tm = (cands or ["mS"])[0]
            M(f"fvfma {LV(tm)} {CE('KBc2')} {LV('AT')} >$t >{LV('Wv')}", ["T", "W"], S(tm, "KBc2") + [("AT#0", fat), ("AT#1", fat)])
        if c["o_nff"] and not c["o_tf"]:
            M(f"fvfma $mauf {HH} {HH} >$nowrite", ["nF"], HHS, fwd="mS")
        else:
            nm = self.pick(("mS", "mR"), FI("H1516"))
            M(f"fvfma {LV(nm)} {HH} {HH} >$nowrite", ["nF"], S(nm) + HHS)
        self.ck(FI("nR") != FI("N0"))
        A(f"ffloor $mauf >{LV('nR')} >{W1('N0')}", ["n", "N0"], fwd="nF")
        um = self.pick(("mS", "mR"), FI("H8"))
        M(f"fvfma {LV(um)} {H8} $lmt{TE} >{LV('us')}", ["us"],
          S(um) + H8S + [("T", "t"), ("tE1", "m", 3), ("tE2", "m", 3)])
        TXT = [("tT1", "m", 3), ("tT2", "m", 3)] + ([("tT3", "m", 3)] if mtab else [])

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
          at=[("S2r", 0)] if c["o_ubf"] else ())
        if c["o_ubf"]:
            self.ck(FI("P_A") != FI("cUB"))
            M(f"fvfma/$imr2 $aluf {CE('P_A')} {CE('cUB')} >$nowrite", ["UB"], S("P_A", "cUB") + [("DMn", "o", 1)], fwd="S2r")
        else:
            self.ck(len({FI("S2r"), FI("P_A"), FI("cUB")}) == 3)
            M(f"fvfma/$imr2 {LV('S2r')} {CE('P_A')} {CE('cUB')} >$nowrite", ["UB"], S("S2r", "P_A", "cUB") + [("DMn", "o", 1)])
        # ---------------- text ----------------
        frv = FI("Rv")
        M(f"fvadd $lmt{TT} {CL('NLc')} >{LV('Rv')} >$omr5", ["R"], S("NLc") + [("T", "t")] + TXT)
        M(f"fvadd/$imr5 $mauf {LV('UAv')} >$nowrite", ["Ys"], [("UA", FI("UAv")), ("R", "o", 1)], fwd="UB")
        self.ck(FI("KBc1") != frv)
        M(f"fvfma $mauf {CE('KBc1')} -{LV('Rv')} >$nowrite", ["V2"], S("KBc1") + [("R", frv)], fwd="Ys")

        # ---------------- position ----------------
        for n in ("DA", "DMn", "DMs", "Za", "Zb", "Spv", "XA"): self.var(n)
        self.ck(len({FI("us"), FI("DY"), FI("IY")}) == 3)
        if c["o_daf"]:
            self.ck(FI("DX") != FI("IX"))
            M(f"fvfma $mauf {CE('DX')} {CE('IX')} >{LV('DA')}", ["DA"], S("DX", "IX"), fwd="us")
        else:
            self.ck(len({FI("us"), FI("DX"), FI("IX")}) == 3)
            M(f"fvfma {LV('us')} {CE('DX')} {CE('IX')} >{LV('DA')}", ["DA"], S("us", "DX", "IX"))
        M(f"fvfma {LV('us')} {DYOP} {CE('IY')} >$nowrite", ["DB"], S("us", "IY") + DYSRC)
        self.ck(FI("DMn") != FI("DMs"))
        A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')} >$omr2", ["DMn", "DMs"], S("DA"), fwd="DB")
        fza, fzb = FI("Za"), FI("Zb"); assert fza != fzb
        A(f"fmax {W1('DMn')} {LV('DMs')} >{W0('Za')} >{W1('Zb')}", ["Dw"], S("DMn", "DMs"))
        self.ck(FI("nR") != FI("Wv"))
        M(f"fvadd -{LV('nR')} -{LV('Wv')} >{W1('Za')} >{W0('Zb')}", ["NR"], [("n", FI("nR")), ("W", FI("Wv"))])
        M(f"fvadd -{LV('Za')} {LV('Zb')} >{LV('Spv')} >$omr3", ["S"], [("Dw", fza), ("Dw", fzb), ("NR", fza), ("NR", fzb)])
        if c["o_vreg"]:
            g3 = self.mg(FI("H8"))
            M(f"fvfma/$imr3 $mauf {H8} {CL(g3)} >{W1('XA')}", ["AM"], H8S + S(g3) + [("S", "o", 1)], fwd="S")
            A(f"fftoi $mauf >{LV('Vreg')}", ["V"], fwd="V2")
            A(f"ullsr {LV('Vreg')} $mauf >$nowrite", ["F1x"], [("V", FI("Vreg"))], fwd="AM")
        else:
            g3 = self.mg(FI("H8"), FI("Spv"))
            self.ck(FI("H8") != FI("Spv"))
            M(f"fvfma/$imr3 {LV('Spv')} {H8} {CL(g3)} >{W1('XA')}", ["AM"], H8S + S(g3) + [("S", FI("Spv")), ("S", "o", 1)])
            A("fftoi $mauf >$nowrite", ["V"], fwd="V2")
            A("ullsr $aluf $mauf >$nowrite", ["F1x"], fwd=["V", "AM"])
        A(f"llsl $aluf {LV('XA')} >$nowrite", ["FO"], [("AM", FI("XA"))], fwd="F1x")
        A("l1bmr4lbor $aluf $lb0", ["OUT"], fwd="FO", unit="l1")

        # ---------------- tables ----------------
        def ad(ids, base): return "[" + ",".join(str((256 * i + toff) % 4096 + base) for i in ids) + "]"
        if mtab:
            U = lambda text, unit, dst, src: self.OPS.append(op(text, unit, dst, src))
            U(f"fmwrite {H8} $lx0", "mw", ["xE#0"], H8S)
            U(f"fmwrite {H8} $lx4", "mw", ["xE#1"], H8S)
            U(f"fmread $lx0 >$lm{ad([2, 4, 8, 14], TE)}", "mr", ["tE2"], [("xE#0", "x", 1), ("xE#1", "x", 1)])
            U(f"fmwrite -{H8} $ly0", "mw", ["yE#0"], H8S)
            U(f"fmwrite -{H8} $ly4", "mw", ["yE#1"], H8S)
            U(f"fmread $ly0 >$lm{ad([0, 6, 10, 12], TE)}", "mr", ["tE1"], [("yE#0", "y", 1), ("yE#1", "y", 1)])
            hb, lo_, lh = AD("HBF"), AD("LOd"), AD("LHd")
            lt = self.LAT["LOd"]
            tsrc = [("HBF#0", ftf, lt), ("HBF#1", ftf, lt), ("LOd", ftf, lt)]
            U(f"fmwrite $l{ftf}[{hb},{lo_},{hb},{lo_}] $lx0", "mw", ["xT#0"], tsrc + [("tE2", "x", 1)])
            U(f"fmwrite $l{ftf}[{hb},{lo_},{hb},{lo_}] $lx4", "mw", ["xT#1"], tsrc + [("tE2", "x", 1)])
            U(f"fmread $lx0 >$lm{ad([0, 3, 5, 6], TT)}", "mr", ["tT1"], [("xT#0", "x", 1), ("xT#1", "x", 1)])
            U(f"fmread $lx0 >$lm{ad([10, 9, 10, 12], TT)}", "mr", ["tT2"], [("xT#0", "x", 1), ("xT#1", "x", 1)])
            hsrc = [("HBF#0", ftf, lt), ("HBF#1", ftf, lt), ("LHd", ftf, lt)]
            U(f"fmwrite $l{ftf}[{hb},{lh},{hb},{lh}] $ly0", "mw", ["yT#0"], hsrc + [("tE1", "y", 1)])
            U(f"fmwrite $l{ftf}[{hb},{lh},{hb},{lh}] $ly4", "mw", ["yT#1"], hsrc + [("tE1", "y", 1)])
            e15 = (256 * 15 + toff) % 4096
            U(f"fmread $ly0 >$lm[{e15 + 4},{e15 + TT},{e15 + 4},{e15 + TT}]", "mr", ["tT3"], [("yT#0", "y", 1), ("yT#1", "y", 1)])
            return
        tb, th = AD("TB"), AD("TH")
        if tab:
            A(f"lpassa {CL('TF')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF"))
            A(f"lpassa $l{ftb}[{tb},{tb},{tb},{th}] >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [(x, ftb, self.LAT[x]) for x in ("TB", "TH", "TH#hi")])
        else:
            self.ck(ftf != FI("NLc") and ftb != FI("NLc"))
            M(f"fvadd -{CL('TF')} -{CL('NLc')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF", "NLc"))
            M(f"fvadd -$l{ftb}[{tb},{tb},{tb},{th}] -{CL('NLc')} >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [(x, ftb, self.LAT[x]) for x in ("TB", "TH", "TH#hi")] + S("NLc"))
        M(f"fvpassa -{H8} >$lm{ad([0, 6, 10, 12], TE)}", ["tE1"], H8S)
        M(f"fvpassa {H8} >$lm{ad([2, 4, 8, 14], TE)}", ["tE2"], H8S)

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
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v13.vsm"
    open(out, "w").write(text)
    print("compute lines", len(lines), "total", len(lines) + len(TAIL), "seed", seed)
