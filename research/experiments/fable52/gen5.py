#!/usr/bin/env python3
"""v3 generator with a configurable register-file assignment and op variants.

build: G(cfg).OPS for sched3.  cfg maps value names to register files (r=GRF0, s=GRF1, n=LM1)
and option switches (keys starting with "o_"):
  o_host   masks for the id field extraction are the low bits of other constants (no extra imm)
  o_f1alu  digit flags [n>=100, n>=10] from an ALU fmax instead of a MAU op
  o_f2alu  digit flags [n>=1000, 1] from an ALU fmax against [c10, -MG]
  o_nsalu  flag [s<=0] from an ALU fmin instead of a MAU op
  o_tabalu text table written by ALU lpassa from pre-negated constants
  o_c100   c100 as its own imm instead of a MAU product
"""
import struct, sys
import numpy as np
from f32util import hpair
from sched3 import op
import model3

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
def bf(b): return float(np.array([b], ">u4").view(">f4")[0])
MGV = 1.5 * 2.0 ** 23
TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]

DEFAULT = dict(
    o_host=1, o_f1alu=0, o_f2alu=0, o_nsalu=0, o_tabalu=0, o_c100=0,
    MG="rs", MP="r", ML="r",          # MP: file of the peid masks, ML: file of the l1bid masks
    H8="n", K1="r", KBc1="s", KBc2="n", A23="n", B23="s", A4="n", B4="s", H16="s",
    C10="r", CP="n", P_A="n", P_B="n", c_B="r", C_N="n", NLc="n", P15="n",
    D1="n", D2="r", D3="n", D4="r", TF="r", TBH="s", CX="s", ZERO="s",
    SL="s", RW="r", TC="s", RA="r", RB="s", Bv="r", KBv="s",
    L23="s", mnR="r", mnS="s", Z="s", Y1="r", mS="s", mR="r",
    q="s", nR="r", N0="s", us="s",
    R1v="s", S1s="s", S2r="r", FX1="r", FX2="r", N1v="s", TBv="s", Rv="r",
    DA="r", DMn="r", DMs="s", Dw="r", R1s="s", Sv="r", NSv="s",
)
PARAMS = dict(model3.DEFAULT)
PARAMS_HOST = dict(model3.DEFAULT); PARAMS_HOST["c10"] = bf(0x3DCCCD07)

class G:
    def __init__(self, cfg=None):
        self.cfg = dict(DEFAULT); self.cfg.update(cfg or {})
        c = self.cfg
        if c["o_host"]:          # hosted masks live with their mask group
            c["B23"] = c["B4"] = c["D2"] = c["MP"]
            c["D4"] = c["C_N"] = c["ML"]
        self.P = PARAMS_HOST if c["o_host"] else PARAMS
        self.next = {"r": 0, "s": 0, "n": 0}
        self.OPS = []; self.VAL = {}
        self.build()
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
    def S(self, *names): return [(n, self.VAL[n][0]) for n in names]
    def imm_long(self, name, bits):
        files = list(self.F(name))
        addrs = {f: self.along(f) for f in files}
        self.VAL[name] = (files[0], addrs[files[0]])
        for f in files[1:]: self.VAL[name + "@" + f] = (f, addrs[f])
        self.A(f'imm ui"0x{bits & 0xffffffff:08x}" ' + " ".join(f">$l{f}{a}" for f, a in addrs.items()),
               [name] + [name + "@" + f for f in files[1:]], unit="imm")
    def H(self, name, a, b, long=False):
        """half-pair constant; long=True stores the same 32-bit word twice (usable as a mask long)."""
        f = self.F(name)
        if long:
            ad = self.along(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >$l{f}{ad}', [name], unit="imm")
        else:
            ad = self.aword(f); self.VAL[name] = (f, ad)
            self.A(f'imm ui"0x{hpair(a, b):08x}" >${f}{ad}', [name], unit="imm")
    def mg(self, *avoid):
        c = [g for g in ("MG", "MG@r", "MG@s", "MG@n") if g in self.VAL and self.VAL[g][0] not in avoid]
        assert c, "no MG copy available"
        return c[0]

    def build(self):
        A, M, LV, W0, W1, CL, CE, AD, S = self.A, self.M, self.LV, self.W0, self.W1, self.CL, self.CE, self.AD, self.S
        P, c = self.P, self.cfg
        host = c["o_host"]
        (a2, b2), (a3, b3), (a4, b4) = P["lines"]
        A4 = float(np.float32(a4)) * 8.0
        C10 = float(np.float32(P["c10"])); C100 = float(np.float32(C10 * C10))
        (s1, i1), (s2, i2), (s3, i3), (s4, i4) = P["D"]
        self.imm_long("MG", 0x4b400000)
        self.H("H8", 8, 8); self.H("K1", -73 * MGV / 8, -73 * MGV / 8)
        self.H("KBc1", 0.25, 65536); self.H("KBc2", 0.75 * MGV, 256)
        # estimator constants: pair order (line3, line2) so that the B word ends in ...111000
        self.H("A23", a3 * 8, a2 * 8); self.H("B23", b3, b2, long=host)
        fa4 = self.F("A4"); a_a4 = self.along(fa4); self.VAL["A4"] = (fa4, a_a4)
        A(f'imm ui"0x{fb(A4):08x}" >${fa4}{a_a4}', ["A4"], unit="imm")      # [a4', 0]
        self.H("B4", b4, 16384 * (1 + 7 / 512), long=host)                  # second half: BIG, low bits ...000111
        self.H("H16", 1 / 16, 1 / 16)
        fc, fp = self.F("C10"), self.F("CP")
        a_c10 = self.along(fc); a_cp = self.along(fp)
        self.VAL["C10"] = (fc, a_c10); self.VAL["CP"] = (fp, a_cp)
        f2alu = c["o_f2alu"]
        dsts = {fc: f">$l{fc}{a_c10}"}
        names = ["C10"]
        if fp != fc: dsts[fp] = f">$l{fp}{a_cp}"; names.append("CP#0")
        if f2alu:
            fx = self.F("CX")
            assert fx not in dsts
            a_cx = self.along(fx); self.VAL["CX"] = (fx, a_cx); dsts[fx] = f">$l{fx}{a_cx}"; names.append("CX#0")
        A(f'imm ui"0x{fb(C10):08x}" ' + " ".join(dsts.values()), names, unit="imm")
        if fp == fc: A(f'imm ui"0x{fb(C10):08x}" >$l{fp}{a_cp}', ["CP#0"], unit="imm")
        if c["o_c100"]:
            A(f'imm ui"0x{fb(C100):08x}" >${fp}{a_cp}', ["CP"], [("CP#0", fp)], unit="imm")
        else:
            M(f"fvmul {CL('C10')} {CL('C10')} >${fp}{a_cp}", ["CP"], [("C10", fc), ("CP#0", fp)])
        self.H("P_A", 984, -2560); self.H("P_B", 4, 246); self.H("c_B", 192, 12288)
        self.H("C_N", 49152, 48.0625, long=host); self.H("NLc", 0, 1536)
        self.H("P15", 10, -5)
        FIVE = "P15"
        # delta lines: pair order (line2, line3) and (line1, line4) so that D2 ends in ...001100
        self.H("D1", s2 / 16, s1 / 16); self.H("D2", i2, i1, long=host)
        self.H("D3", s3 / 16, s4 / 16); self.H("D4", i3, i4, long=host)
        if host:
            MP = ["B23", "B4", "D2"]; ML = ["D4", "C_N"]
        else:
            for nm, v, grp in (("M38", 0x38, "MP"), ("M7", 7, "MP"), ("M0C", 0x0C, "MP"), ("M6", 6, "ML"), ("M1", 1, "ML")):
                self.cfg[nm] = c[grp]; self.imm_long(nm, v)
            MP = ["M38", "M7", "M0C"]; ML = ["M6", "M1"]
        THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
        tab = c["o_tabalu"]
        if tab: tvals = (-(TLO + 1536.0), -float(THI_F), -float(THI_B), -(TLO_H + 1536.0))
        else: tvals = (float(TLO), float(THI_F), float(THI_B), float(TLO_H))
        ftf, ftb = self.F("TF"), self.F("TBH")
        assert ftf != ftb
        a_tf = self.along(ftf); a_tb = self.along(ftb); a_th = self.along(ftb)
        self.VAL["TF"] = (ftf, a_tf); self.VAL["TB"] = (ftb, a_tb); self.VAL["TH"] = (ftb, a_th)
        A(f'imm ui"0x{fb(tvals[0]):08x}" >$l{ftf}{a_tf} >$l{ftb}{a_tb}', ["TF#lo", "TB#lo"], unit="imm")
        A(f'imm ui"0x{fb(tvals[1]):08x}" >${ftf}{a_tf} >${ftb}{a_th}', ["TF", "TH#hi"], [("TF#lo", ftf)], unit="imm")
        A(f'imm ui"0x{fb(tvals[2]):08x}" >${ftb}{a_tb}', ["TB"], [("TB#lo", ftb)], unit="imm")
        A(f'imm ui"0x{fb(tvals[3]):08x}" >${ftb}{a_th + 1}', ["TH"], unit="imm")

        # ---------------- coordinates ----------------
        for n in ("SL", "RW", "TC", "RA", "RB", "Bv", "KBv"): self.var(n)
        fl = self.VAL[ML[0]][0]; assert all(self.VAL[m][0] == fl for m in ML)
        A(f"iand $l1bid $l{fl}[{AD(ML[0])},{AD(ML[1])},{AD(ML[1])},{AD(ML[1])}] >$nowrite", ["o1"], S(*ML))
        fsl = self.VAL["SL"][0]
        mgo = self.mg(fsl)
        mgsl = [g for g in ("MG", "MG@r", "MG@s", "MG@n") if g in self.VAL and self.VAL[g][0] == fsl][0]
        A(f"ior $aluf {CL(mgo)} >{LV('SL')}", ["SL"], S(mgo), fwd="o1")
        fpm = self.VAL[MP[0]][0]; assert all(self.VAL[m][0] == fpm for m in MP)
        A(f"iand $peid $l{fpm}[{AD(MP[0])},{AD(MP[1])},{AD(MP[2])},{AD(MP[2])}] >$nowrite", ["o3"], S(*MP))
        mga = AD(mgsl)
        A(f"ior $aluf $l{fsl}[{AD('SL')},{mga},{mga},{mga}] >{LV('RW')}", ["RW"], S("SL", mgsl), fwd="o3")
        A("l1bmd $aluf $lb0", ["LB"], fwd="RW", unit="l1")
        A(f"iadd $l2bid $l{fsl}{AD('SL') + 2} >$nowrite", ["o5"], S("SL"))
        A(f"iadd $l2bid $aluf >{LV('TC')}", ["TC"], fwd="o5")
        A(f"l1bmm4 $lb0 >{LV('RA')}", ["RA"], [("LB", "b", 3)], unit="l1")
        A(f"l1bmm4 $lb64 >{LV('RB')}", ["RB"], [("LB", "b", 3)], unit="l1")
        M(f"fvfma $lbf {CE('H8')} {CE('K1')} >$nowrite", ["acc1"], S("H8", "K1"), fwd="RA")
        M(f"fvadd $mauf {LV('TC')} >$nowrite", ["acc2"], S("TC"), fwd="acc1")
        M(f"fvfma $mauf {CE('H8')} {LV('RB')} >{LV('Bv')}", ["Bv"], S("H8", "RB"), fwd="acc2")
        frw = self.VAL["RW"][0]
        kb4 = f"$l{frw}{AD('RW') + 4}"
        M(f"fvfma {kb4} {CE('KBc1')} {CE('KBc2')} >{W0('KBv')}", ["KB#0"], S("RW", "KBc1", "KBc2"))
        M(f"fvfma {kb4} {CE('KBc1')} {CE('KBc2')} >{W1('KBv')}", ["KB#1"], S("RW", "KBc1", "KBc2"))

        # ---------------- estimator ----------------
        for n in ("L23", "mnR", "mnS", "Z", "Y1", "mS", "mR"): self.var(n)
        fz, fy = self.VAL["Z"][0], self.VAL["Y1"][0]; assert fz != fy
        pre_dst = f">{W1('Z')} >{W0('Y1')}"
        pre_names = ["PRE"]
        if f2alu:
            fx, a_cx = self.VAL["CX"]
            if fx not in (fz, fy): pre_dst += f" >${fx}{a_cx + 1}"; pre_names.append("CX")
            else: M(f"fvpassa -{CL(self.mg(fx))} >${fx}{a_cx + 1}", ["CX"], S(self.mg(fx)) + [("CX#0", fx)])
        mgp = self.mg()
        M(f"fvpassa -{CL(mgp)} {pre_dst}", pre_names, S(mgp) + ([("CX#0", self.VAL['CX'][0])] if "CX" in pre_names else []))
        M(f"fvfma $mauf {CE('A23')} {CE('B23')} >{LV('L23')}", ["L23"], S("A23", "B23"), fwd="Bv")
        M(f"fvfma {LV('Bv')} {CL('A4')} {CE('B4')} >$nowrite", ["L4"], S("Bv", "A4", "B4"))
        assert self.VAL["mnR"][0] != self.VAL["mnS"][0]
        A(f"fmin {LV('L23')} $mauf >{LV('mnR')} >{LV('mnS')}", ["mnR", "mnS"], S("L23"), fwd="L4")
        A(f"fmin {W1('mnR')} {LV('mnS')} >{W0('Z')} >{W1('Y1')}", ["Zy"], S("mnR", "mnS"))
        M(f"fvadd {LV('Z')} {LV('Y1')} >$nowrite", ["yr"], [("Zy", fz), ("Zy", fy), ("PRE", fz), ("PRE", fy)])
        fkb = self.VAL["KBv"][0]
        M(f"fvadd $mauf {LV('KBv')} >{LV('mS')} >{LV('mR')}", ["mS", "mR"], [("KB#0", fkb), ("KB#1", fkb)], fwd="yr")

        # ---------------- token ----------------
        TT, TE = 0, 2
        for n in ("q", "nR", "N0", "us"): self.var(n)
        fh16 = self.VAL["H16"][0]
        msrc = "mR" if self.VAL["mR"][0] != fh16 else "mS"
        M(f"fvmul {LV(msrc)} {CE('H16')} >$nowrite", ["MQ"], S(msrc, "H16"))
        A(f"ffloor $mauf >{LV('q')}", ["q"], fwd="MQ")
        M(f"fvadd -$aluf {LV('mR')} >{LV('nR')} >{W1('N0')}", ["nR", "N0"], S("mR"), fwd="q")
        fk2 = self.VAL["KBc2"][0]
        cands = [(m_, g_) for m_ in ("mS", "mR") for g_ in ("MG", "MG@r", "MG@s", "MG@n") if g_ in self.VAL
                 and len({self.VAL[m_][0], self.VAL[g_][0], fk2}) == 3]
        assert cands, "T: no file combination"
        tm, tg = cands[0]
        M(f"fvfma {LV(tm)} {CE('KBc2')} {CL(tg)} >$t", ["T"], S(tm, "KBc2", tg))
        fh8 = self.VAL["H8"][0]
        um = "mS" if self.VAL["mS"][0] != fh8 else "mR"
        M(f"fvfma {LV(um)} {CE('H8')} $lmt{TE} >{LV('us')}", ["us"],
          S(um, "H8") + [("T", "t"), ("tE1", "m", 3), ("tE2", "m", 3)])

        # ---------------- digits ----------------
        for n in ("R1v", "S1s", "S2r", "FX1", "FX2", "N1v", "TBv", "Rv"): self.var(n)
        M(f"fvmul $mauf {CL('CP')} >{LV('R1v')}", ["R1"], S("CP"), fwd="nR")
        A(f"ffloor $mauf >{LV('S1s')}", ["S1s"], fwd="R1")
        M(f"fvmul $aluf {CL('C10')} >$nowrite", ["R2"], S("C10"), fwd="S1s")
        A(f"ffloor $mauf >{LV('S2r')}", ["S2r"], fwd="R2")
        fr1 = self.VAL["R1v"][0]
        if c["o_f1alu"]:
            A(f"fmax {LV('S1s')} {CL('C10')} >{LV('FX1')} >$omr1", ["F1"], S("S1s", "C10"))
        else:
            M(f"fvfma {LV('R1v')} {CE('H8')} -{CE('H8')} >{LV('FX1')} >$omr1", ["F1"], [("R1", fr1)] + S("H8"))
        if f2alu:
            A(f"fmax {LV('S2r')} {CL('CX')} >{LV('FX2')} >$omr2", ["F2"], S("S2r", "CX"))
        else:
            M(f"fvadd $mauf -{CE('P15')} >{LV('FX2')} >$omr2", ["F2"], S("P15"), fwd="R1")
        M(f"fvadd {LV('N0')} {CE('C_N')} >{LV('N1v')}", ["N1"], S("N0", "C_N"))
        fn1 = self.VAL["N1v"][0]
        M(f"fvfma/$imr2 {LV('S2r')} {CE('P_A')} {LV('N1v')} >$nowrite", ["TA"], S("S2r", "P_A") + [("N1", fn1), ("F2", "o", 1)])
        ftbv = self.VAL["TBv"][0]
        M(f"fvfma/$imr1 {LV('S1s')} {CE('P_B')} {CE('c_B')} >{LV('TBv')}", ["TBd"], S("S1s", "P_B", "c_B") + [("F1", "o", 1)])
        # ---------------- text ----------------
        frv = self.VAL["Rv"][0]
        M(f"fvadd $lmt{TT} {CE('NLc')} >{LV('Rv')} >$omr5", ["R"], S("NLc") + [("T", "t"), ("tT1", "m", 3), ("tT2", "m", 3)])
        M(f"fvadd/$imr5 $mauf {LV('TBv')} >$nowrite", ["Ys"], [("TBd", ftbv), ("R", "o", 1)], fwd="TA")
        M(f"fvfma $mauf {CE('KBc1')} -{LV('Rv')} >$nowrite", ["V2"], S("KBc1") + [("R", frv)], fwd="Ys")
        A("fftoi $mauf >$nowrite", ["V"], fwd="V2")

        # ---------------- position ----------------
        for n in ("DA", "DMn", "DMs", "Dw", "R1s", "Sv", "NSv"): self.var(n)
        M(f"fvfma {LV('us')} {CE('D1')} {CE('D2')} >{LV('DA')}", ["DA"], S("us", "D1", "D2"))
        M(f"fvfma {LV('us')} {CE('D3')} {CE('D4')} >$nowrite", ["DB"], S("us", "D3", "D4"))
        assert self.VAL["DMn"][0] != self.VAL["DMs"][0]
        A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')}", ["DMn", "DMs"], S("DA"), fwd="DB")
        A(f"fmax {W1('DMn')} {LV('DMs')} >{W1('Dw')}", ["Dw"], S("DMn", "DMs"))
        M(f"fvfma {LV('Bv')} -{CE('H8')} -{LV('q')} >$nowrite", ["R0"], S("Bv", "H8", "q"))
        fp15 = self.VAL[FIVE][0]
        msrc3 = "mS" if self.VAL["mS"][0] != fp15 else "mR"
        M(f"fvfma {LV(msrc3)} -{CE(FIVE)} $mauf >{LV('R1s')}", ["R1s"], S(msrc3, FIVE), fwd="R0")
        fsv, fns = self.VAL["Sv"][0], self.VAL["NSv"][0]
        M(f"fvadd {LV('Dw')} {LV('R1s')} >{LV('Sv')} >$omr3", ["S"], S("Dw", "R1s"))
        g3 = self.mg(fsv, fh8)
        M(f"fvfma/$imr3 {LV('Sv')} {CE('H8')} {CL(g3)} >$nowrite", ["AMR"], S("H8", g3) + [("S", fsv), ("S", "o", 1)])
        if c["o_nsalu"]:
            fzr = self.F("ZERO"); a_z = self.along(fzr)
            A(f"fmin {LV('Sv')} $l{fzr}{a_z} >{LV('NSv')} >$omr4", ["NS"], [("S", fsv)])
            M(f"fvfma/$imr4 {LV('Sv')} -{CE('H8')} {CL(g3)} >$nowrite", ["AML"], S("H8", g3) + [("S", fsv), ("NS", "o", 1)])
        else:
            M(f"fvadd -{LV('Dw')} -{LV('R1s')} >{LV('NSv')} >$omr4", ["NS"], S("Dw", "R1s"))
            g4 = self.mg(fns, fh8)
            M(f"fvfma/$imr4 {LV('NSv')} {CE('H8')} {CL(g4)} >$nowrite", ["AML"], S("H8", g4) + [("NS", fns), ("NS", "o", 1)])
        A("ullsr $aluf $mauf >$nowrite", ["F1x"], fwd=["V", "AMR"])
        A("llsl $aluf $mauf >$nowrite", ["FO"], fwd=["F1x", "AML"])
        A("l1bmr4lbor $aluf $lb0", ["OUT"], fwd="FO", unit="l1")

        # ---------------- tables ----------------
        def ad(ids, base): return "[" + ",".join(str(256 * i + base) for i in ids) + "]"
        tb, th = AD("TB"), AD("TH")
        if tab:
            A(f"lpassa {CL('TF')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], S("TF"))
            A(f"lpassa $l{ftb}[{tb},{tb},{tb},{th}] >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
              [("TB", ftb), ("TH", ftb), ("TH#hi", ftb)])
        else:
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

if __name__ == "__main__":
    import sched3, json
    from collections import Counter
    cfg = json.load(open(sys.argv[3])) if len(sys.argv) > 3 else None
    g = G(cfg)
    print(Counter(o["unit"] for o in g.OPS), valid(g.OPS))
    tries = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    lines, line_of, seed = sched3.best_schedule(g.OPS, tries=tries)
    text = sched3.render(lines) + "\n".join(TAIL) + "\n"
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v4.vsm"
    open(out, "w").write(text)
    print("compute lines", len(lines), "total", len(lines) + len(TAIL), "seed", seed)
