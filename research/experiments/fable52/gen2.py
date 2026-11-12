#!/usr/bin/env python3
"""v2 generator: table-driven text/u, pair digits, g-bias; scheduled by sched.py."""
import struct, sys
from f32util import hpair
from sched import op, schedule, render
from model2 import LINES, TXT6, C10, C100

def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
M23 = 2.0 ** 23

class Alloc:
    def __init__(self):
        self.next = {"r": 16, "s": 0, "n": 0}
        self.top = {"r": 512, "s": 512, "n": 2048}
    def var(self, f):          # lane variable: 8 words (v-stride long words)
        a = (self.next[f] + 7) // 8 * 8; self.next[f] = a + 8
        assert a + 8 <= self.top[f], f"{f} full"
        return a
    def long(self, f):         # constant long word
        a = (self.next[f] + 1) // 2 * 2; self.next[f] = a + 2; return a
    def word(self, f):
        a = self.next[f]; self.next[f] += 1; return a
AL = Alloc()
OPS = []
VAL = {}        # value name -> (kind, file, addr)

def A(text, dst=(), src=(), fwd=None, unit="alu", prio=0):
    OPS.append(op(text, unit, dst, src, fwd, prio)); return len(OPS) - 1
def M(text, dst=(), src=(), fwd=None, prio=0): return A(text, dst, src, fwd, "mau", prio)

# operand helpers
def LV(name):  k, f, a = VAL[name]; return f"$l{f}{a}v"
def W0(name):  k, f, a = VAL[name]; return f"${f}{a}v2"
def W1(name):  k, f, a = VAL[name]; return f"${f}{a + 1}v2"
def CL(name):  k, f, a = VAL[name]; return f"$l{f}{a}"
def CE(name):  k, f, a = VAL[name]; return f"${f}{a}e"
def SRC(*names): return [(n, VAL[n][1]) for n in names]
def newvar(name, f): VAL[name] = ("var", f, AL.var(f)); return name

# ---------------- constants ----------------
def imm_long(name, bits, files):
    addrs = {f: AL.long(f) for f in files}
    VAL[name] = ("long", files[0], addrs[files[0]])
    for f in files[1:]: VAL[name + "@" + f] = ("long", f, addrs[f])
    A(f'imm ui"0x{bits & 0xffffffff:08x}" ' + " ".join(f">$l{f}{a}" for f, a in addrs.items()),
      [name] + [name + "@" + f for f in files[1:]], unit="imm")
def imm_pair_long(name, b0, b1, f):
    a = AL.long(f); VAL[name] = ("long", f, a)
    A(f'imm ui"0x{b0 & 0xffffffff:08x}" >$l{f}{a}', [name + "#0"], unit="imm")
    A(f'imm ui"0x{b1 & 0xffffffff:08x}" >${f}{a + 1}', [name], src=[(name + "#0", f)], unit="imm")
def imm_w1(name, b1, f):
    """long word [0, b1]: word imm into word1 of a fresh (zero) long."""
    a = AL.long(f); VAL[name] = ("long", f, a)
    A(f'imm ui"0x{b1 & 0xffffffff:08x}" >${f}{a + 1}', [name], unit="imm")
def imm_word(name, bits, files):
    addrs = {f: AL.word(f) for f in files}
    VAL[name] = ("word", files[0], addrs[files[0]])
    for f in files[1:]: VAL[name + "@" + f] = ("word", f, addrs[f])
    A(f'imm ui"0x{bits & 0xffffffff:08x}" ' + " ".join(f">${f}{a}" for f, a in addrs.items()),
      [name] + [name + "@" + f for f in files[1:]], unit="imm")
def H(name, a, b, files): imm_word(name, hpair(a, b), files)

imm_long("MG", 0x4b400000, ["r", "s"])           # 1.5*2^23
imm_long("K8", 8, ["r"])
H("H8192", 8192, 8192, ["n"])
imm_long("ZC", fb(-1.5 * 2.0 ** 36 - 1.5 * 2.0 ** 26), ["r"])
H("H8", 8, 8, ["n"])
(a1, b1), (a2, b2), (a3, b3), (a4, b4) = ((0.28125, 0.703125), (0.251953125, 1.359375), (0.225341796875, 13.21875), (0.20253394544124603, 119.375))
H("A13", a1, a3, ["n"]); H("B13", b1, b3, ["s"])
imm_pair_long("A24", fb(a2), fb(a4), "n"); H("B24", b2, b4, ["s"])
H("H16", 1 / 16, 1 / 16, ["n"]); H("H256", 256, 256, ["n"])
H("HHALF", 0.5, 0.5, ["n"])
# C10 broadcast long in r, and [C100, C10] long in n (c10 long write shared, then C100 word)
a_c10r = AL.long("r"); a_c10n = AL.long("n")
VAL["C10_10"] = ("long", "r", a_c10r); VAL["C100_10"] = ("long", "n", a_c10n)
A(f'imm ui"0x{fb(C10):08x}" >$lr{a_c10r} >$ln{a_c10n}', ["C10_10", "C10n#0"], unit="imm")
A(f'imm ui"0x{fb(C100):08x}" >$n{a_c10n}', ["C100_10"], src=[("C10n#0", "n")], unit="imm")
H("P1", 246, -2560, ["n"]); H("P2", 1, 246, ["r"]); H("P3", 12288, 0, ["s"])
H("P4", 48, 12288, ["r"]); H("P5", 1, 256, ["s"])
imm_w1("B12298", fb(12298.0), "r")
H("D1", -1, -2, ["n"]); H("D2", -65.5, -13, ["r"]); H("D3", -3, 0, ["n"]); H("D4", -8.5, -598, ["r"])
H("H5", 5, 5, ["n"])
TF, TB, TH = TXT6[3], TXT6[0], TXT6[15]
imm_pair_long("TF", fb(TF[0]), fb(TF[1]), "r")
imm_word("TBh", fb(TB[0]), ["r"]); imm_word("THl", fb(TH[1]), ["r"])

# ---------------- coordinates ----------------
# ramp: GRF0 word w = floor(w/2), w = 0..15  (baseline prologue)
A("ipackbit $subpeid $t >$nowrite", ["rp1"])
A("dmwrite $aluf $lx0", ["rp2"], fwd="rp1", unit="mw")
A("dmread $lx0 >$lr0v4", ["rp3"], [("rp2", "x")], unit="mr")
A("iinc $mreadf >$lr2v4", ["RAMP"], fwd="rp3")
RAMP = [("RAMP", "r"), ("rp3", "r")]
_, _, k8 = VAL["K8"]
for nm in ("PA", "PC", "Bpe"): newvar(nm, "s")
A("iand $l1bid $lr[12,2,0,0] >$nowrite", ["o1"], RAMP)
A(f"ilsl $aluf $lr[12,6,0,0] >{LV('PA')}", ["PA"], RAMP, fwd="o1")
A(f"iand $mabid $lr[{k8},8,6,0] >$nowrite", ["o3"], RAMP + SRC("K8"))
A(f"ilsl $aluf $lr[12,0,0,0] >$nowrite", ["o4"], RAMP, fwd="o3")
_, _, apa = VAL["PA"]; _, _, amgs = VAL["MG@s"]
A(f"ior $aluf $ls[{apa},{apa + 2},{amgs},{amgs}] >{LV('PC')}", ["PC", "KB"], SRC("PA", "MG@s"), fwd="o4")
_, _, apc = VAL["PC"]
VAL["KB"] = ("long", "s", apc + 4)
A("ilsl $l2bid $lr8 >$nowrite", ["o6"], RAMP)
A(f"ior $aluf $ls{apc} >$nowrite", ["o7"], SRC("PC"), fwd="o6")
A(f"ior $aluf $ls{apc + 2} >$nowrite", ["o8"], SRC("PC"), fwd="o7")
A("ior $subpeid $aluf >$nowrite", ["o9"], fwd="o8")
newvar("F", "s"); newvar("Fc", "s")
A(f"ior $aluf {CL('MG')} >{LV('F')}", ["F"], SRC("MG"), fwd="o9")
A(f"ior $lr[0,2,4,6] {CL('MG@s')} >{LV('Fc')}", ["Fc"], RAMP + SRC("MG@s"))
newvar("Zc", "r"); newvar("X", "r")
M(f"fvfma {LV('Fc')} {CE('H8192')} {CL('ZC')} >{LV('Zc')}", ["Zc"], SRC("Fc", "H8192", "ZC"))
M(f"fvfma {LV('F')} {CE('H8')} {LV('Zc')} >{LV('X')}", ["X"], SRC("F", "H8", "Zc"))
# ---------------- estimator ----------------
newvar("L13", "s"); newvar("L24", "r")
M(f"fvfma {LV('X')} {CE('A13')} {CE('B13')} >{LV('L13')}", ["L13"], SRC("X", "A13", "B13"))
M(f"fvfma {LV('X')} {CL('A24')} {CE('B24')} >{LV('L24')}", ["L24"], SRC("X", "A24", "B24"))
newvar("mnR", "r"); newvar("mnS", "s")
A(f"fmin {LV('L13')} $mauf >{LV('mnR')} >{LV('mnS')}", ["mnR", "mnS"], SRC("L13"), fwd="L24")
newvar("Y0", "s"); newvar("Y1", "r")
A(f"fmin {W1('mnR')} {LV('mnS')} >{W0('Y0')} >{W1('Y1')}", ["Y0", "Y1"], SRC("mnR", "mnS"))
M(f"fvadd {W0('Y0')} {LV('Y1')} >$nowrite", ["yb"], SRC("Y0", "Y1"))
M(f"fvadd $mauf -{CL('MG')} >$nowrite", ["yr"], SRC("MG"), fwd="yb")
newvar("mS", "s"); newvar("mR", "r")
M(f"fvadd $mauf {CL('KB')} >{LV('mS')} >{LV('mR')}", ["mS", "mR"], SRC("KB"), fwd="yr")
# ---------------- token ----------------
newvar("q", "s")
M(f"fvmul {LV('mS')} {CE('H16')} >$nowrite", ["mq"], SRC("mS", "H16"))
A(f"ffloor $mauf >{LV('q')}", ["q"], fwd="mq")
newvar("nR", "r"); newvar("N0", "s")
M(f"fvadd -$aluf {LV('mR')} >{LV('nR')} >{W1('N0')}", ["nR", "N0"], SRC("mR"), fwd="q")
M(f"fvfma {LV('mS')} {CE('H256')} {CL('MG')} >$t", ["T"], SRC("mS", "H256", "MG"))
TS, TT, TE = 0, 2, 4
newvar("u", "s")
M(f"fvfma {LV('mR')} {CE('HHALF')} $lmt{TE} >{LV('u')}", ["u"], SRC("mR", "HHALF") + [("T", "t"), ("tE1", "m"), ("tE2", "m")])
# ---------------- digits ----------------
newvar("S1s", "s"); newvar("S1r", "r")
M(f"fvmul $mauf {CL('C100_10')} >$nowrite", ["R1"], SRC("C100_10"), fwd="nR")
A(f"ffloor $mauf >{LV('S1s')} >{LV('S1r')}", ["S1s", "S1r"], fwd="R1")
newvar("S2r", "r"); newvar("S2s", "s")
M(f"fvmul $aluf {CL('C10_10')} >$nowrite", ["R2"], SRC("C10_10"), fwd="S1s")
A(f"ffloor $mauf >{LV('S2r')} >{LV('S2s')}", ["S2r", "S2s"], fwd="R2")
# leading-zero bias via MAU sign flags + masked adds (no ALU fmin)
newvar("FX1", "r"); newvar("FX2", "s")
M(f"fvadd {LV('S1s')} -{CE('HHALF')} >{LV('FX1')} $omr1", ["F1"], SRC("S1s", "HHALF"))
M(f"fvadd {LV('S2r')} -{CE('HHALF')} >{LV('FX2')} $omr2", ["F2"], SRC("S2r", "HHALF"))
M(f"fvfma {LV('S2r')} {CE('P1')} {LV('N0')} >$nowrite", ["Pb"], SRC("S2r", "P1", "N0"))
newvar("T1", "s"); newvar("T2", "n")
M(f"fvpassa/$imr1 {CE('P4')} >{LV('T1')}", ["T1"], SRC("P4") + [("F1", "o")])
M(f"fvpassa/$imr2 {CE('P3')} >{LV('T2')}", ["T2"], SRC("P3") + [("F2", "o")])
M(f"fvfma {LV('S1s')} {CE('P2')} $mauf >$nowrite", ["P"], SRC("S1s", "P2"), fwd="Pb")
M(f"fvadd $mauf {LV('T1')} >$nowrite", ["Pp1"], SRC("T1"), fwd="P")
M(f"fvadd $mauf {LV('T2')} >$nowrite", ["Pp2"], SRC("T2"), fwd="Pp1")
M(f"fvfma $mauf {CE('P5')} {CL('B12298')} >$nowrite", ["Yv"], SRC("P5", "B12298"), fwd="Pp2")

TAB_S = [("tS1", "m"), ("tS2", "m")]; TAB_T = [("tT1", "m"), ("tT2", "m"), ("tT3", "m")]
M(f"fvmul $mauf $lmt{TS} >$nowrite", ["V1"], [("T", "t")] + TAB_S, fwd="Yv")
M(f"fvadd $mauf $lmt{TT} >$nowrite", ["V2"], [("T", "t")] + TAB_T, fwd="V1")
newvar("V", "s")
A(f"fftoi $mauf >{LV('V')}", ["V"], fwd="V2")
# ---------------- delta / shift ----------------
newvar("DA", "r")
M(f"fvfma $mauf {CE('D1')} {CE('D2')} >{LV('DA')}", ["DA"], SRC("D1", "D2"), fwd="u")
M(f"fvfma {LV('u')} {CE('D3')} {CE('D4')} >$nowrite", ["DB"], SRC("u", "D3", "D4"))
newvar("DMn", "r"); newvar("DMs", "s")
A(f"fmax {LV('DA')} $mauf >{LV('DMn')} >{LV('DMs')}", ["DMn", "DMs"], SRC("DA"), fwd="DB")
newvar("Dw", "r")
A(f"fmax {W1('DMn')} {LV('DMs')} >{W1('Dw')}", ["Dw"], SRC("DMn", "DMs"))
newvar("R1s", "s"); newvar("S", "s")
M(f"fvadd -{LV('X')} -{LV('q')} >$nowrite", ["R0"], SRC("X", "q"))
M(f"fvfma {LV('mS')} {CE('H5')} $mauf >{LV('R1s')}", ["R1s"], SRC("mS", "H5"), fwd="R0")
M(f"fvadd {LV('Dw')} {LV('R1s')} >{LV('S')}", ["S"], SRC("Dw", "R1s"))
newvar("AMR", "r"); newvar("AML", "r")
M(f"fvfma $mauf {CE('H8')} {CL('MG')} >{LV('AMR')}", ["AMR"], SRC("H8", "MG"), fwd="S")
M(f"fvfma -{LV('S')} {CE('H8')} {CL('MG')} >{LV('AML')}", ["AML"], SRC("S", "H8", "MG"))
newvar("FR", "r")
A(f"ullsr {LV('V')} {LV('AMR')} >{LV('FR')}", ["FR"], SRC("V", "AMR"))
A(f"llsl {LV('V')} {LV('AML')} >$nowrite", ["FL"], SRC("V", "AML"))
A(f"lor $aluf {LV('FR')} >$nowrite", ["FO"], SRC("FR"), fwd="FL")
A("l1bmr4lbor $aluf $lb0", ["L1"], fwd="FO", unit="l1")
# ---------------- tables ----------------
NUM = [1, 2, 4, 7, 8, 11, 13, 14]
def ad(ids, base, off=0): return "[" + ",".join(str(256 * i + base + off) for i in ids) + "]"
M(f"fvpassa {CE('P5')} >$lm{ad(NUM[:4], TS)}", ["tS1"], SRC("P5"))
M(f"fvpassa {CE('P5')} >$lm{ad(NUM[4:], TS)}", ["tS2"], SRC("P5"))
M(f"fvpassa {CL('TF')} >$lm{ad([3, 6, 9, 12], TT)}", ["tT1"], SRC("TF"))
M(f"fvpassa {CL('TF')} >$lm{ad([0, 5, 10, 15], TT)}", ["tT2"], SRC("TF"))
# Buzz HI words (0,5,10) and FH LO word (15): word writes
_, ftb, atb = VAL["TBh"]; _, fth, ath = VAL["THl"]
M(f"fvpassa $r[{atb},{atb},{atb},{ath}] >$m[{TT},{256*5+TT},{256*10+TT},{256*15+TT+1}]", ["tT3"], [("TBh", "r"), ("THl", "r"), ("tT2", "m")])
M(f"fvpassa -{CE('HHALF')} >$lm{ad([0, 6, 10, 12], TE)}", ["tE1"], SRC("HHALF"))
M(f"fvpassa {CE('HHALF')} >$lm{ad([2, 4, 8, 14], TE)}", ["tE2"], SRC("HHALF"))

TAIL = ["nop", "nop", "l2bmd $lb0 $lc0", "l2bmd $lb32 $lc256", "nop", "mvd/n512 $lc0 $p0@0", "mvp/n4096 $p0@0 $d0@0"]

def build():
    lines, line_of = schedule(OPS)
    # the l1bmr4lbor must be the last line
    return render(lines) + "\n".join(TAIL) + "\n", lines

if __name__ == "__main__":
    prog, lines = build()
    out = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2.vsm"
    open(out, "w").write(prog)
    from collections import Counter
    c = Counter(o["unit"] for o in OPS)
    print("ops", dict(c), "lines", len(lines), "total", len(lines) + len(TAIL))
