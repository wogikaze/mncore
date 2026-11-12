#!/usr/bin/env python3
"""v3 generator: L1BM round-trip coordinates, 3-line estimator, flushed digit terms,
flag-selected text, relu'd two-shift placement.  Scheduled by sched3 (backward list scheduling)."""
import struct, sys
import numpy as np
from f32util import hpair, half_bits
from sched3 import op, best_schedule, render
import model3

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
MGV = 1.5 * 2.0 ** 23
P = model3.DEFAULT

class Alloc:
    def __init__(self):
        self.next = {"r": 0, "s": 0, "n": 0}
        self.top = {"r": 512, "s": 512, "n": 2048}
    def var(self, f):
        a = (self.next[f] + 7) // 8 * 8; self.next[f] = a + 8
        assert a + 8 <= self.top[f], f"{f} full"
        return a
    def long(self, f):
        a = (self.next[f] + 1) // 2 * 2; self.next[f] = a + 2; return a
    def word(self, f):
        a = self.next[f]; self.next[f] += 1; return a
AL = Alloc()
OPS = []
VAL = {}

def A(text, dst=(), src=(), fwd=(), unit="alu", prio=0):
    OPS.append(op(text, unit, dst, src, fwd, prio)); return len(OPS) - 1
def M(text, dst=(), src=(), fwd=(), prio=0): return A(text, dst, src, fwd, "mau", prio)
def LV(name):  k, f, a = VAL[name]; return f"$l{f}{a}v"
def W0(name):  k, f, a = VAL[name]; return f"${f}{a}v2"
def W1(name):  k, f, a = VAL[name]; return f"${f}{a + 1}v2"
def CL(name):  k, f, a = VAL[name]; return f"$l{f}{a}"
def CE(name):  k, f, a = VAL[name]; return f"${f}{a}e"
def AD(name):  return VAL[name][2]
def SRC(*names): return [(n, VAL[n][1]) for n in names]
def newvar(name, f): VAL[name] = ("var", f, AL.var(f)); return name

# ---------------- constants ----------------
def imm_long(name, bits, files):
    addrs = {f: AL.long(f) for f in files}
    VAL[name] = ("long", files[0], addrs[files[0]])
    for f in files[1:]: VAL[name + "@" + f] = ("long", f, addrs[f])
    A(f'imm ui"0x{bits & 0xffffffff:08x}" ' + " ".join(f">$l{f}{a}" for f, a in addrs.items()),
      [name] + [name + "@" + f for f in files[1:]], unit="imm")
def imm_word(name, bits, f):
    a = AL.word(f); VAL[name] = ("word", f, a)
    A(f'imm ui"0x{bits & 0xffffffff:08x}" >${f}{a}', [name], unit="imm")
def H(name, a, b, f): imm_word(name, hpair(a, b), f)

(a2, b2), (a3, b3), (a4, b4) = P["lines"]
A4 = float(np.float32(a4)) * 8.0
C10 = float(np.float32(P["c10"]))

imm_long("MG", 0x4b400000, ["r", "s"])
for nm, v in (("M6", 6), ("M1", 1), ("M38", 0x38), ("M7", 7), ("M0C", 0x0C)):
    imm_long(nm, v, ["r"])
H("H8", 8, 8, "n")
H("K1", -73 * MGV / 8, -73 * MGV / 8, "r")
H("KBc1", 0.25, 65536, "s")
H("KBc2", 0.75 * MGV, 256, "n")
H("A23", a2 * 8, a3 * 8, "n"); H("B23", b2, b3, "s")
imm_long("A4", fb(A4), ["n"]); H("B4", b4, b4, "s")
H("H16", 1 / 16, 1 / 16, "s")
# C10 long in r, and the pair [c100, c10] in n (c100 = c10*c10 by MAU)
a_c10 = AL.long("r"); a_cp = AL.long("n")
VAL["C10"] = ("long", "r", a_c10); VAL["CP"] = ("long", "n", a_cp)
A(f'imm ui"0x{fb(C10):08x}" >$lr{a_c10} >$ln{a_cp}', ["C10", "CP#0"], unit="imm")
M(f"fvmul $lr{a_c10} $lr{a_c10} >$n{a_cp}", ["CP"], [("C10", "r"), ("CP#0", "n")])
H("P_A", 984, -2560, "n"); H("P_B", 4, 246, "n"); H("c_B", 192, 12288, "r")
H("C_N", 49152, 48.0625, "n"); H("NLc", 0, 1536, "n"); H("P15", 10, -5, "n")
(s1, i1), (s2, i2), (s3, i3), (s4, i4) = P["D"]
H("D1", s1, s2, "n"); H("D2", i1, i2, "r"); H("D3", s3, s4, "n"); H("D4", i3, i4, "r")
# text longs: TF in r, TB and TH in s
THI_F, TLO = model3.TXT6[3]; THI_B = model3.TXT6[0][0]; TLO_H = model3.TXT6[15][1]
a_tf = AL.long("r"); a_tb = AL.long("s"); a_th = AL.long("s")
VAL["TF"] = ("long", "r", a_tf); VAL["TB"] = ("long", "s", a_tb); VAL["TH"] = ("long", "s", a_th)
A(f'imm ui"0x{fb(TLO):08x}" >$lr{a_tf} >$ls{a_tb}', ["TF#lo", "TB#lo"], unit="imm")
A(f'imm ui"0x{fb(THI_F):08x}" >$r{a_tf} >$s{a_th}', ["TF", "TH#hi"], [("TF#lo", "r")], unit="imm")
A(f'imm ui"0x{fb(THI_B):08x}" >$s{a_tb}', ["TB"], [("TB#lo", "s")], unit="imm")
A(f'imm ui"0x{fb(TLO_H):08x}" >$s{a_th + 1}', ["TH"], unit="imm")

# ---------------- coordinates ----------------
newvar("SL", "s"); newvar("RW", "r"); newvar("TC", "s"); newvar("RA", "r"); newvar("RB", "s"); newvar("Bv", "r")
A(f"iand $l1bid $lr[{AD('M6')},{AD('M1')},{AD('M1')},{AD('M1')}] >$nowrite", ["o1"], SRC("M6", "M1"))
A(f"ior $aluf {CL('MG')} >{LV('SL')}", ["SL"], SRC("MG"), fwd="o1")
A(f"iand $peid $lr[{AD('M38')},{AD('M7')},{AD('M0C')},{AD('M0C')}] >$nowrite", ["o3"], SRC("M38", "M7", "M0C"))
mgs = AD("MG@s")
A(f"ior $aluf $ls[{AD('SL')},{mgs},{mgs},{mgs}] >{LV('RW')}", ["RW"], SRC("SL", "MG@s"), fwd="o3")
A("l1bmd $aluf $lb0", ["LB"], fwd="RW", unit="l1")
A(f"iadd $l2bid $ls{AD('SL') + 2} >$nowrite", ["o5"], SRC("SL"))
A(f"iadd $l2bid $aluf >{LV('TC')}", ["TC"], fwd="o5")
A(f"l1bmm4 $lb0 >{LV('RA')}", ["RA"], [("LB", "b", 3)], unit="l1")
A(f"l1bmm4 $lb64 >{LV('RB')}", ["RB"], [("LB", "b", 3)], unit="l1")
M(f"fvfma $lbf {CE('H8')} {CE('K1')} >$nowrite", ["acc1"], SRC("H8", "K1"), fwd="RA")
M(f"fvadd $mauf {LV('TC')} >$nowrite", ["acc2"], SRC("TC"), fwd="acc1")
M(f"fvfma $mauf {CE('H8')} {LV('RB')} >{LV('Bv')}", ["Bv"], SRC("H8", "RB"), fwd="acc2")
# KB = MG + k (both words, two word writes)
newvar("KBv", "s")
kb4 = f"$lr{AD('RW') + 4}"
M(f"fvfma {kb4} {CE('KBc1')} {CE('KBc2')} >{W0('KBv')}", ["KB#0"], SRC("RW", "KBc1", "KBc2"))
M(f"fvfma {kb4} {CE('KBc1')} {CE('KBc2')} >{W1('KBv')}", ["KB#1"], SRC("RW", "KBc1", "KBc2"))

# ---------------- estimator ----------------
newvar("L23", "s"); newvar("mnR", "r"); newvar("mnS", "s"); newvar("Z", "s"); newvar("Y1", "r")
newvar("mS", "s"); newvar("mR", "r")
M(f"fvpassa -{CL('MG')} >{W1('Z')} >{W0('Y1')}", ["PRE"], SRC("MG"))
M(f"fvfma {LV('Bv')} {CE('A23')} {CE('B23')} >{LV('L23')}", ["L23"], SRC("Bv", "A23", "B23"))
M(f"fvfma {LV('Bv')} {CL('A4')} {CE('B4')} >$nowrite", ["L4"], SRC("Bv", "A4", "B4"))
A(f"fmin {LV('L23')} $mauf >{LV('mnR')} >{LV('mnS')}", ["mnR", "mnS"], SRC("L23"), fwd="L4")
A(f"fmin {W1('mnR')} {LV('mnS')} >{W0('Z')} >{W1('Y1')}", ["Zy"], SRC("mnR", "mnS"))
M(f"fvadd {LV('Z')} {LV('Y1')} >$nowrite", ["yr"], [("Zy", "s"), ("Zy", "r"), ("PRE", "s"), ("PRE", "r")])
M(f"fvadd $mauf {LV('KBv')} >{LV('mS')} >{LV('mR')}", ["mS", "mR"], [("KB#0", "s"), ("KB#1", "s")], fwd="yr")

# ---------------- token ----------------
TT, TE = 0, 2
newvar("MQ", "r"); newvar("q", "s"); newvar("nR", "r"); newvar("N0", "s"); newvar("us", "s")
M(f"fvmul {LV('mR')} {CE('H16')} >{LV('MQ')}", ["MQ"], SRC("mR", "H16"))
A(f"ffloor $mauf >{LV('q')}", ["q"], fwd="MQ")
M(f"fvadd -$aluf {LV('mR')} >{LV('nR')} >{W1('N0')}", ["nR", "N0"], SRC("mR"), fwd="q")
M(f"fvfma {LV('mS')} {CE('KBc2')} {CL('MG')} >$t", ["T"], SRC("mS", "KBc2", "MG"))
M(f"fvfma {LV('MQ')} {CE('H8')} $lmt{TE} >{LV('us')}", ["us"],
  SRC("MQ", "H8") + [("T", "t"), ("tE1", "m", 3), ("tE2", "m", 3)])

# ---------------- digits ----------------
newvar("R1v", "s"); newvar("S1s", "s"); newvar("S1r", "r"); newvar("S2r", "r")
newvar("FX1", "r"); newvar("FX2", "r"); newvar("N1v", "s"); newvar("TBv", "s")
M(f"fvmul $mauf {CL('CP')} >{LV('R1v')}", ["R1"], SRC("CP"), fwd="nR")
A(f"ffloor $mauf >{LV('S1s')}", ["S1s"], fwd="R1")
M(f"fvmul $aluf {CL('C10')} >$nowrite", ["R2"], SRC("C10"), fwd="S1s")
A(f"ffloor $mauf >{LV('S2r')}", ["S2r"], fwd="R2")
M(f"fvfma {LV('R1v')} {CE('H8')} -{CE('H8')} >{LV('FX1')} >$omr1", ["F1"], [("R1", "s"), ("H8", "n")])
M(f"fvadd $mauf -{CE('P15')} >{LV('FX2')} >$omr2", ["F2"], SRC("P15"), fwd="R1")
M(f"fvadd {LV('N0')} {CE('C_N')} >{LV('N1v')}", ["N1"], SRC("N0", "C_N"))
M(f"fvfma/$imr2 {LV('S2r')} {CE('P_A')} {LV('N1v')} >$nowrite", ["TA"], SRC("S2r", "P_A") + [("N1", "s"), ("F2", "o", 1)])
M(f"fvfma/$imr1 {LV('S1s')} {CE('P_B')} {CE('c_B')} >{LV('TBv')}", ["TBd"], SRC("S1s", "P_B", "c_B") + [("F1", "o", 1)])
# ---------------- text ----------------
newvar("Rv", "r")
M(f"fvadd $lmt{TT} {CE('NLc')} >{LV('Rv')} >$omr5", ["R"], SRC("NLc") + [("T", "t"), ("tT1", "m", 3), ("tT2", "m", 3)])
M(f"fvadd/$imr5 $mauf {LV('TBv')} >$nowrite", ["Ys"], [("TBd", "s"), ("R", "o", 1)], fwd="TA")
M(f"fvfma $mauf {CE('KBc1')} -{LV('Rv')} >$nowrite", ["V2"], SRC("KBc1") + [("R", "r")], fwd="Ys")
A("fftoi $mauf >$nowrite", ["V"], fwd="V2")

# ---------------- position ----------------
newvar("DA", "r"); newvar("DMn", "r"); newvar("DMs", "s"); newvar("Dw", "r"); newvar("R1s", "s")
newvar("Sv", "r"); newvar("NSv", "s")
M(f"fvfma {LV('us')} {CE('D1')} {CE('D2')} >{LV('DA')}", ["DA"], SRC("us", "D1", "D2"))
M(f"fvfma {LV('us')} {CE('D3')} {CE('D4')} >$nowrite", ["DB"], SRC("us", "D3", "D4"))
A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')}", ["DMn", "DMs"], SRC("DA"), fwd="DB")
A(f"fmax {W1('DMn')} {LV('DMs')} >{W1('Dw')}", ["Dw"], SRC("DMn", "DMs"))
M(f"fvfma {LV('Bv')} -{CE('H8')} -{LV('q')} >$nowrite", ["R0"], SRC("Bv", "H8", "q"))
M(f"fvfma {LV('mS')} -{CE('P15')} $mauf >{LV('R1s')}", ["R1s"], SRC("mS", "P15"), fwd="R0")
M(f"fvadd {LV('Dw')} {LV('R1s')} >{LV('Sv')} >$omr3", ["S"], SRC("Dw", "R1s"))
M(f"fvadd -{LV('Dw')} -{LV('R1s')} >{LV('NSv')} >$omr4", ["NS"], SRC("Dw", "R1s"))
M(f"fvfma/$imr3 {LV('Sv')} {CE('H8')} {CL('MG@s')} >$nowrite", ["AMR"], SRC("H8", "MG@s") + [("S", "r"), ("S", "o", 1)])
M(f"fvfma/$imr4 {LV('NSv')} {CE('H8')} {CL('MG')} >$nowrite", ["AML"], SRC("H8", "MG") + [("NS", "s"), ("NS", "o", 1)])
A("ullsr $aluf $mauf >$nowrite", ["F1x"], fwd=["V", "AMR"])
A("llsl $aluf $mauf >$nowrite", ["FO"], fwd=["F1x", "AML"])
A("l1bmr4lbor $aluf $lb0", ["OUT"], fwd="FO", unit="l1")

# ---------------- tables ----------------
def ad(ids, base): return "[" + ",".join(str(256 * i + base) for i in ids) + "]"
M(f"fvadd -{CL('TF')} -{CE('NLc')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], SRC("TF", "NLc"))
tb, th = AD("TB"), AD("TH")
M(f"fvadd -$ls[{tb},{tb},{tb},{th}] -{CE('NLc')} >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"],
  [("TB", "s"), ("TH", "s"), ("TH#hi", "s"), ("NLc", "n")])
M(f"fvmul -{CE('H16')} {CE('H8')} >$lm{ad([0, 6, 10, 12], TE)}", ["tE1"], SRC("H16", "H8"))
M(f"fvmul {CE('H16')} {CE('H8')} >$lm{ad([2, 4, 8, 14], TE)}", ["tE2"], SRC("H16", "H8"))

TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]

if __name__ == "__main__":
    from collections import Counter
    print(Counter(o["unit"] for o in OPS))
    tries = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    best = best_schedule(OPS, tries=tries, verbose=False)
    lines, line_of, seed = best
    text = render(lines) + "\n".join(TAIL) + "\n"
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v3.vsm"
    open(out, "w").write(text)
    print("compute lines", len(lines), "total", len(lines) + len(TAIL), "seed", seed)
