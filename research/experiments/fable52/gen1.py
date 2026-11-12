#!/usr/bin/env python3
"""v1 generator: correctness-first VSM for the trailing/end-aligned token design.

Stages are written with generous spacing; lane variables use v-stride (4 long words).
"""
import struct
from f32util import hpair, half_bits
def fb(x):  # float32 bits
    return struct.unpack(">I", struct.pack(">f", float(x)))[0]
def immf(x, dst):
    return f'imm ui"0x{fb(x):08x}" {dst}'
def immh(a, b, dst):
    return f'imm ui"0x{hpair(a, b):08x}" {dst}'
def immu(v, dst):
    return f'imm ui"0x{v & 0xffffffff:08x}" {dst}'

LINES = ((0.28125, 0.703125), (0.251953125, 1.359375), (0.225341796875, 13.21875),
         (0.20253221690654755, 119.396484375))
M23 = 2.0 ** 23

def coords():
    """-> lane vars: X at $lr0v (both words = X); KB at $lr8v (both words = 2^23 + k)."""
    L = []
    # constants
    L.append('imm ui"0x4b000000" $t $lr200 $ls200')                   # T, lr200=ls200=[2^23,2^23] bits
    # B = 1024c + 512 m3 + 128 h1 + 16 L2 + 8 h0 + 4 m2 + pe ; integer pieces
    L.append(immu(8, '$lr202'))                                         # 8
    L.append(immu(4, '$lr204'))                                         # 4
    L.append(immu(6, '$lr206'))                                         # 6
    L.append(immu(1, '$lr208'))                                         # 1
    L.append(immu(3, '$lr210'))                                         # 3
    L.append(immu(9, '$lr212'))                                         # 9 (shift for 512 = 8<<6? we use mab&8 << 6)
    L.append('nop')
    L.append('iand $mabid $lr202 $nowrite')                             # 8 m3
    L.append('ilsl $aluf $lr206 $ls202')                                # 512 m3   (<<6)
    L.append('iand $mabid $lr204 $ls204')                               # 4 m2
    L.append('iand $l1bid $lr206 $nowrite')                             # 2 h1
    L.append('ilsl $aluf $lr206 $ls206')                                # 128 h1  (<<6)
    L.append('iand $l1bid $lr208 $nowrite')                             # h0
    L.append('ilsl $aluf $lr210 $ls208')                                # 8 h0  (<<3)
    L.append('ilsl $l2bid $lr204 $ls210')                               # 16 L2 (<<4)
    L.append('ior $subpeid $ls202 $nowrite')                            # pe | 512 m3
    L.append('ior $aluf $ls204 $nowrite')
    L.append('ior $aluf $ls206 $nowrite')
    L.append('ior $aluf $ls208 $nowrite')
    L.append('ior $aluf $ls210 $nowrite')
    L.append('ior $aluf $t $ls212')                                     # B0_b = 2^23 + B0 (float bits) both words
    # cycle via transposition: source 1024*pe as float minus 2^23 handled below
    L.append('ior $subpeid $t $nowrite')                                # [2^23+pe]
    L.append('dmwrite $aluf $lx0')
    L.append('dmread $lx0 $lr16v')                                      # lane: [2^23+c, 2^23+c]
    L.append(immf(1024.0, '$ln200'))
    L.append(immf(-(1024.0 * M23 + M23), '$ls220'))
    L.append('nop')
    L.append('nop')
    # Bc = 1024*c + B0 : fma(C_b, 1024, B0_b - 1024*2^23 - 2^23)  -> do in two steps for exactness
    L.append('fvfma $lr16v $ln200 $ls220 $lr24v')                       # 1024c - 2^23   (exact)
    L.append('nop')
    L.append('fvadd $lr24v $ls212 $lr32v')                              # 1024c + B0  = B (unbiased float)
    L.append(immf(8.0, '$ln204'))
    L.append('nop')
    L.append('nop')
    L.append('fvmul $lr32v $ln204 $lr0v')                               # X = 8B
    # k = mab & 3 -> KB = 2^23 + k
    L.append(immu(3, '$lr214'))
    L.append('nop')
    L.append('iand $mabid $lr214 $nowrite')
    L.append('ior $aluf $t $lr8v')                                      # [2^23+k] both words, all cycles
    L.append(immh(-M23, -M23, '$n254'))
    L.append('nop'); L.append('nop')
    L.append('fvadd $lr8v $n254e $ls8v')                               # k (unbiased float)
    return L

if __name__ == "__main__":
    from chk import check
    prog = "\n".join(coords()) + "\n"
    ok, words = check(prog, [
        ("r", 0, lambda B, k: (fb(8 * B) << 32) | fb(8 * B), (1 << 64) - 1),
        ("r", 8, lambda B, k: (fb(M23 + k) << 32) | fb(M23 + k), (1 << 64) - 1),
    ])
    print("words", words, "ok", ok)

def estimator():
    """X at $lr0v, KB at $lr8v -> m_b at $lr72v (both words = 2^23 + m)."""
    (a1, b1), (a2, b2), (a3, b3), (a4, b4) = LINES
    L = []
    L.append(immh(a1, a3, '$n208'))                                    # [a1, a3] half-pair (e-read)
    L.append(immh(b1, b3, '$s222'))                                    # [b1, b3] half-pair
    L.append(immf(a2, '$n210'))                                        # a2 (word)
    L.append(immf(a4, '$n211'))                                        # a4 (word)  -> ln210 = [a2, a4]
    L.append(immf(b2, '$s224'))
    L.append(immf(b4, '$s225'))                                        # ls224 = [b2, b4]
    L.append('nop')
    L.append('nop')
    L.append('fvfma $lr0v $n208e $s222e $lr40v')                       # [l1, l3]
    L.append('fvfma $lr0v $ln210 $ls224 $ls40v')                       # [l2, l4]
    L.append('nop')
    L.append('fmin $lr40v $ls40v $lr48v $ls48v')                       # [min12, min34]
    L.append('nop')
    L.append('fmin $r49v2 $ls48v $ls56v $r65v2')                       # sub0 = y ; also word 65+2c = y -> lr64v=[0,y]
    L.append(immh(1.0, 1.0, '$n212'))
    L.append('nop')
    L.append('fvfma $s56v2 $n212e $lr64v $ls64v')                      # [y, y]
    L.append('nop')
    L.append(immh(M23, M23, '$n252'))
    L.append('nop')
    L.append('fvadd $ls64v $n252e $lr72v')                             # m_b0 = 2^23 + round(y)
    L.append('nop')
    L.append('fvadd $lr72v $ls8v $lr72v')                              # + k (exact)
    return L

def ref_m(B, k):
    import numpy as np
    X = np.float64(8 * B)
    ys = [np.float64(np.float32(np.float64(np.float32(a)) * X + np.float64(np.float32(b)))) for a, b in LINES]
    y = min(ys)
    mb0 = np.float32(y + M23)
    return float(mb0) + k

if __name__ == "__main__" and True:
    from chk import check
    prog = "\n".join(coords() + estimator()) + "\n"
    ok, words = check(prog, [
        ("r", 72, lambda B, k: (fb(ref_m(B, k)) << 32) | fb(ref_m(B, k)), (1 << 64) - 1),
    ])
    print("words", words, "ok", ok)

# ---------------- token decomposition ----------------
def token():
    """m_b at $lr72v -> q at $ls88v ([q,q]); n_b,i_b at $lr96v ([n_b,i_b]); n at $lr104v ([n,n]); m at $ls104v."""
    L = []
    L.append(immh(1 / 16, 1 / 16, '$n214'))
    L.append(immh(-2.0 ** 19, -2.0 ** 19, '$s226'))
    L.append(immh(-1.0, -16.0, '$n216'))
    L.append(immh(-M23, -M23, '$s228'))
    L.append('nop'); L.append('nop')
    L.append('fvfma $lr72v $n214e $s226e $lr80v')                    # m/16
    L.append('nop')
    L.append('ffloor $lr80v $ls88v')                                  # q
    L.append('nop')
    L.append('fvfma $ls88v $n216e $lr72v $lr96v')                    # [n_b, i_b]
    L.append('fvadd $lr72v $s228e $ln104v')                          # m (unbiased) -> LM1
    L.append('nop'); L.append('nop')
    L.append('fvadd $ln104v -$ls88v $lr104v')                        # n = m - q (unbiased) both words
    return L

if __name__ == "__main__":
    from chk import check
    def exp_m(B, k):
        return int(ref_m(B, k) - M23)
    def both(x): return (fb(x) << 32) | fb(x)
    prog = "\n".join(coords() + estimator() + token()) + "\n"
    ok, words = check(prog, [
        ("s", 88, lambda B, k: both(exp_m(B, k) // 16), (1 << 64) - 1),
        ("r", 96, lambda B, k: (fb(M23 + exp_m(B, k) - exp_m(B, k) // 16) << 32) | fb(M23 + exp_m(B, k) % 16), (1 << 64) - 1),
        ("r", 104, lambda B, k: both(exp_m(B, k) - exp_m(B, k) // 16), (1 << 64) - 1),
    ])
    print("words", words, "ok", ok)

# ---------------- digits, region bias, text, shift ----------------
from masks import M_W1, M_W2, M_Z
C10, C100, C1000 = 0x3DCCCCCD, 0x3C23D70B, 0x3A83126F
def render():
    """n at $lr104v, [n_b,i_b] at $lr96v, m (unbiased) at $ln104v, m_b at $lr72v, q at $ls88v, X at $lr0v
       -> F at $lr160v (64-bit placed token)."""
    L = []
    # --- constants ---
    L.append(immu(C100, '$s230')); L.append(immu(C10, '$s231'))          # ls230 = [C100, C10]
    L.append(immu(C1000, '$s232'))                                       # ls232 = [C1000, 0]
    L.append(immh(246.0, -10.0 * 2 ** 24, '$n218'))                      # [246, -167772160]
    L.append(immh(62976.0, 0.0, '$n220'))
    L.append(immh(1.0, 0.0, '$n222'))
    L.append(immh(0.0, 2.0 ** 24, '$n224'))
    L.append(immh(-32.0, -32.0, '$s234')); L.append(immh(-408.0, -408.0, '$s236')); L.append(immh(-4672.0, -4672.0, '$s238'))
    L.append(immu(M_W1 >> 32, '$n240')); L.append(immu(M_W1, '$n241'))
    L.append(immu(M_W2 >> 32, '$n242')); L.append(immu(M_W2, '$n243'))
    L.append(immu(M_Z >> 32, '$n244')); L.append(immu(M_Z, '$n245'))
    L.append(immu(0x0046697A, '$r222')); L.append(immu(0x7A0A0000, '$r223'))   # SRC1
    L.append(immu(0x0042757A, '$r224')); L.append(immu(0x7A000000, '$r225'))   # SRC2
    L.append(immh(0.5, 0.5, '$n226')); L.append(immf(-2.0 ** 22 + 1, '$s240')); L.append(immf(-2.0 ** 22 + 1, '$s241'))
    L.append(immh(1.0, 1.0, '$n228')); L.append('imm f"1.0" $ln250')
    L.append(immh(-1.0, -2.0, '$n230')); L.append(immh(-64.0, -11.0, '$s242'))
    L.append(immh(-3.0, 0.0, '$n232')); L.append(immh(-6.0, -597.0, '$s244'))
    L.append(immh(5.0, 5.0, '$s250'))
    L.append(immh(8.0, 8.0, '$n236')); L.append(immh(-8.0, -8.0, '$n238'))
    L.append(immf(M23 + 1024, '$s246'))
    # region bias long word at $ls112v: [bias0, 805961728]
    L.append(immf(float(0x300A0000), '$s113v2'))
    L.append('nop'); L.append('nop')
    # --- region flags (from X) ---
    L.append('fvadd $lr0v $s234e $lr112v $omr1')                          # t1
    L.append('fvadd $lr0v $s236e $lr112v $omr2')                          # t2
    L.append('fvadd $lr0v $s238e $lr112v $omr3')                          # t3
    L.append(immf(48.0, '$s112v2/$imr1'))
    L.append(immf(12336.0, '$s112v2/$imr2'))
    L.append(immf(3158064.0, '$s112v2/$imr3'))
    # --- digits ---
    L.append('fvmul $lr104v $ls230 $lr120v')                              # [n/100, n/10]
    L.append('fvmul $lr104v $ls232 $lr128v')                              # [n/1000, 0]
    L.append('ffloor $lr120v $ls120v')                                    # [f2, f1]
    L.append('ffloor $lr128v $ls128v')                                    # [f3, 0]
    L.append('fvfma $lr104v $n224e $ls112v $lr136v')                      # P = [bias0, 2^24 n + C]
    L.append('nop')
    L.append('fvfma $ls120v $n218e $lr136v $lr144v')                      # Q
    L.append('nop')
    L.append('fvfma $ls128v $n220e $lr144v $lr136v')                      # R
    L.append('nop')
    L.append('fvfma $s121v2 $n222e $lr136v $lr144v')                      # S = [HI, LO]
    L.append('nop')
    L.append('fftoi $lr144v $lr152v')                                     # V (integer)
    # --- class flags & text writes ---
    L.append('llsl $ln240 $lr96v $ls136v')                                # CW1
    L.append('llsl $ln242 $lr96v $ls144v')                                # CW2
    L.append('hrelu $ls136v $ls136v $ln136v $omr4')
    L.append('hrelu $ls144v $ls144v $ln144v $omr5')
    L.append('lpassa $lr222 $lr152v/$imr4')
    L.append('lpassa $lr224 $lr152v/$imr5')
    # --- u, Delta, s ---
    L.append('fvfma $lr72v $n226e $ls240 $lr160v')                        # m/2 + 1 - ... (biased form) -> floor(m/2)+1
    L.append('nop')
    L.append('ffloor $lr160v $ls160v')                                    # floor(m/2)+1
    L.append('llsl $ln244 $lr96v $lr168v')                                # CWz
    L.append('nop')
    L.append('frelu $lr168v $ln250 $lr248v')                              # z (1.0 or -0) -> GRF0
    L.append('nop')
    L.append('fvfma $lr248v -$n228e $ls160v $lr176v')                     # u = floor(m/2)+1 - z
    L.append('nop')
    L.append('fvfma $lr176v $n230e $s242e $ls176v')                       # [-64-u, -11-2u]
    L.append('fvfma $lr176v $n232e $s244e $lr216v')                       # [-6-3u, -597] -> GRF0
    L.append('nop')
    L.append('fmax $ls176v $lr216v $lr184v $ls192v')                      # [max(a,c), max(b,-597)]
    L.append('nop')
    L.append('fmax $r185v2 $ls192v $lr192v')                              # Delta' (sub0)
    L.append('fvadd -$lr0v -$ls88v $lr200v')                              # -X - q
    L.append('nop')
    L.append('fvfma $ln104v $s250e $lr200v $ls200v')                      # 5m - X - q
    L.append('nop')
    L.append('fvadd $ls200v $lr192v $lr208v')                             # s (sub0)
    L.append('nop')
    L.append('fvfma $lr208v $n236e $s246 $s209v2')                        # SR into word 209+2c  (lr208v = [s, SR])
    L.append('fvfma $lr208v $n238e $s246 $s217v2')                        # SL into word 217+2c of GRF1
    L.append('nop')
    L.append('ullsr $lr152v $ls208v $ls224v')                             # V >> 8s
    L.append('llsl $lr152v $ls216v $nowrite')                             # V << -8s
    L.append('lor $aluf $ls224v $lr160v')                                 # F
    return L

def tail():
    return ['nop', 'l1bmr4lbor $lr160v $lb0', 'nop', 'nop', 'l2bmd $lb0 $lc0', 'l2bmd $lb32 $lc256', 'nop',
            'mvd/n512 $lc0 $p0@0', 'mvp/n4096 $p0@0 $d0@0']

if __name__ == "__main__":
    prog = "\n".join(coords() + estimator() + token() + render() + tail()) + "\n"
    open("/tmp/v1.vsm", "w").write(prog)
    print("written /tmp/v1.vsm")
