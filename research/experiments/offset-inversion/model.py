#!/usr/bin/env python3
"""Exact model of the full byte generation driven by the divmod inversion.

For every one of the 4096 long words (block b = 0..4095, byte base B = 8b) the
model produces the 8 bytes, and the result is compared with the official
testcase expectation (all 32,766 bytes).

Machine assumptions encoded here (see REPORT.md for the evidence):
  * one PE per long word; the 8 output bytes are 2 words of GRF1,
  * one ALU instruction covers 4 int32 lanes, one MAU instruction covers
    8 float32 slots,
  * a per-PE scalar is broadcast to every lane for free (same register address
    in all four cycles),
  * LM0 with T-indirect addressing is the canvas: one instruction can write
    four characters to four independently computed byte addresses.

Stages:
  A  region select (3 compares + mask selects)
  B  int->float via the 2^23 trick
  C  divmod by the region period P_d  (exact, zero corrections)
  D  slot decode  j, c  (d=4 arithmetic, d=2/3 table gather)
  E  three candidates n0, n0+1, n0+2: class, digit count, piece length
  F  canvas positions relative to the block start
  G  decimal digits of the candidates
  H  canvas writes (digits / letters / newlines)
  I  pack + transfer (inherited from the 93-word solution)

Run: python3 model.py
"""

from __future__ import annotations

import numpy as np

from ref import NMAX, build

PIECES, OUT, L, OWNER = build()
NB = len(OUT)
NP = 4096

F32 = np.float32
NCAND = 4


def piece_len(n: int, d: int) -> int:
    if n % 15 == 0:
        return 9
    if n % 3 == 0 or n % 5 == 0:
        return 5
    return d + 1


def class_of(n: int) -> str:
    if n % 15 == 0:
        return "FB"
    if n % 3 == 0:
        return "F"
    if n % 5 == 0:
        return "B"
    return "p"


def region_tables(d: int):
    N = 10 ** (d - 1)
    lens = [piece_len(N + j, d) for j in range(15)]
    cls = [class_of(N + j) for j in range(15)]
    jtab, ctab = [], []
    for j in range(15):
        for k in range(lens[j]):
            jtab.append(j)
            ctab.append(k)
    assert len(jtab) == 8 * d + 47
    return 8 * d + 47, jtab, ctab, cls, lens


REG = {}
for d, B0 in ((2, 30), (3, 408), (4, 4668)):
    Pd, jtab, ctab, cls, lens = region_tables(d)
    REG[d] = dict(N=10 ** (d - 1), B0=B0, P=Pd,
                  jtab=np.array(jtab), ctab=np.array(ctab), cls=cls, lens=lens)

# d = 1: the 30 bytes 0..29 are a direct map (no period).
D1_N = np.array([OWNER[B][0] for B in range(30)], dtype=np.int64)
D1_C = np.array([OWNER[B][1] for B in range(30)], dtype=np.int64)


# --------------------------------------------------------------- instruction budget
STAGES = [
    # (stage, ALU, MAU, imm, l1b, l2b, mv, nop, note)
    ("A region select",        3, 0, 0, 0, 0, 0, 0, "lsub with 3 lanes -> mask flags; 2 masked selects"),
    ("B int->float",           1, 1, 0, 0, 0, 0, 0, "ior 0x4b000000; fvadd -(2^23)"),
    ("C divmod P_d",           3, 2, 0, 0, 0, 0, 0, "fvfma(R,1/P,bias), ffloor, fftoi, fvfma(q,-P,R); 1 lane"),
    ("D slot decode",          4, 1, 0, 0, 0, 0, 0, "d=4: 2 cmp + /5 + c ; d=2,3: T set+read + select"),
    ("E candidates",          12, 8, 0, 0, 0, 0, 0, "4x(add); 4x(mod15 fma+iand+select); 4x digits/len"),
    ("F canvas positions",     4, 0, 0, 0, 0, 0, 0, "rel0=-c; rel_k=rel_(k-1)+len_(k-1)"),
    ("G digits",               8, 10, 0, 0, 0, 0, 0, "2 MAU groups of 8 slots x 5 ops = 10 MAU; 4x2 ALU floor"),
    ("H canvas writes",       12, 0, 0, 0, 0, 0, 0, "4 candidates x 3 (chars0-3, chars4-7, newline) masked"),
    ("I pack",                 6, 0, 0, 0, 0, 0, 0, "3x(ilsl+ior) inherits 93-word tail"),
    ("I transfer",             0, 0, 0, 1, 2, 2, 3, "l1bmd, 2x l2bmd, mvd, mvp, 3 nop"),
    ("prologue (inherited)",  12, 0,24, 0, 0, 0, 0, "93-word solution L1-16: coordinates + constants"),
]


def budget():
    tot = dict(alu=0, mau=0, imm=0, l1bm=0, l2bm=0, mv=0, nop=0)
    for s in STAGES:
        for key, idx in (("alu", 1), ("mau", 2), ("imm", 3), ("l1bm", 4),
                         ("l2bm", 5), ("mv", 6), ("nop", 7)):
            tot[key] += s[idx]
    return tot


# --------------------------------------------------------------- semantics
def model_words():
    """Compute the 4096 output words exactly (byte-accurate)."""
    b = np.arange(NP, dtype=np.int64)
    B = 8 * b
    is1 = B < 30
    is2 = (B >= 30) & (B < 408)
    is3 = (B >= 408) & (B < 4668)
    is4 = B >= 4668

    # --- stage C: divmod per region
    q = np.zeros(NP, dtype=np.int64)
    r = np.zeros(NP, dtype=np.int64)
    for d, m in ((2, is2), (3, is3), (4, is4)):
        info = REG[d]
        R = B[m] - info["B0"]
        inv = F32(1.0 / info["P"])
        qf = np.floor(R.astype(np.float32) * inv + F32(0.002))
        q[m] = qf.astype(np.int64)
        r[m] = R - info["P"] * q[m]
        assert (r[m] >= 0).all() and (r[m] < info["P"]).all()

    # --- stage D/E: n0, c0
    n0 = np.zeros(NP, dtype=np.int64)
    c0 = np.zeros(NP, dtype=np.int64)
    for d, m in ((2, is2), (3, is3), (4, is4)):
        info = REG[d]
        n0[m] = info["N"] + 15 * q[m] + info["jtab"][r[m]]
        c0[m] = info["ctab"][r[m]]
    n0[is1] = D1_N[B[is1]]
    c0[is1] = D1_C[B[is1]]

    # --- stage E: candidates
    lens = []
    classes = []
    ndigits = []
    for k in range(NCAND):
        n = n0 + k
        cl = np.array([class_of(int(x)) for x in n])
        dg = np.array([len(str(int(x))) for x in n])
        ln = np.where(cl == "p", dg + 1, np.where(cl == "FB", 9, 5))
        lenses = ln.astype(np.int64)
        lens.append(lenses)
        classes.append(cl)
        ndigits.append(dg.astype(np.int64))

    # --- stage F: canvas positions
    rel = [-c0]
    for k in range(NCAND - 1):
        rel.append(rel[k] + lens[k])

    # --- stage G/H: render into a canvas around the block start
    OFF = 12
    canvas = np.zeros((NP, 40), dtype=np.int64)
    for k in range(NCAND):
        n = n0 + k
        for B_i in range(NP):
            rk = rel[k][B_i] + OFF
            cl = classes[k][B_i]
            if cl == "p":
                text = str(int(n[B_i]))
                seq = [ord(ch) for ch in text] + [ord("\n")]
            elif cl == "F":
                seq = [ord(ch) for ch in "Fizz\n"]
            elif cl == "B":
                seq = [ord(ch) for ch in "Buzz\n"]
            else:
                seq = [ord(ch) for ch in "FizzBuzz\n"]
            for t, ch in enumerate(seq):
                canvas[B_i, rk + t] = ch
    return canvas[:, OFF:OFF + 8]


def main():
    out = model_words()
    got = out.astype(np.uint8).tobytes()
    bad = sum(1 for a, b in zip(got[:NB], OUT) if a != b)
    word_bad = [w for w in range(4096)
                if got[8 * w:8 * w + 8][:len(OUT[8*w:8*w+8])] != OUT[8 * w:8 * w + 8]]
    print("model bytes:", len(got), "expected:", len(OUT))
    print("byte mismatches:", bad, " word mismatches:", len(word_bad), word_bad[:8])

    tot = budget()
    alu, mau, imm = tot["alu"], tot["mau"], tot["imm"]
    rest = tot["l1bm"] + tot["l2bm"] + tot["mv"] + tot["nop"]
    lines = max(alu, mau) + imm + rest
    print("\ninstruction budget")
    for s in STAGES:
        print(f"  {s[0]:24s} alu={s[1]:3d} mau={s[2]:3d} imm={s[3]:3d} "
              f"l1b={s[4]} l2b={s[5]} mv={s[6]} nop={s[7]}   {s[8]}")
    print(f"\n  totals: {tot}")
    print(f"  ALU={alu} MAU={mau} imm={imm} non-ALU/MAU={rest}")
    print(f"  line estimate = max(ALU,MAU) + imm + rest = {lines}")
    print(f"  (pairing each ALU with an independent MAU costs nothing extra; "
          f"imm cannot share a line with ALU)")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
