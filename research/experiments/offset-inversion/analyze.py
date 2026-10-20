#!/usr/bin/env python3
"""Closed-form analysis of the offset -> (n, char) inversion.

Output layout facts (proved in ref.py):
  32,766 bytes, 4096 blocks of 8 bytes, block b starts at byte B = 8b.

Region d = number of decimal digits of the owning number:
  d=1: bytes [0,30)        numbers 1..9
  d=2: bytes [30,408)      numbers 10..99
  d=3: bytes [408,4668)    numbers 100..999
  d=4: bytes [4668,32766)  numbers 1000..6334

In region d >= 2 the numbers split into full groups of 15 consecutive numbers
starting at N_d = 10^(d-1) (because N_d % 15 == 10 for every d >= 2).  Every
group consumes exactly P_d = 8d + 47 bytes, and the byte offset r inside a
group determines the number offset j in the group and the character index c by
a fixed table of P_d entries.  Therefore

    q, r = divmod(B - B0, P_d);  n = N_d + 15*q + jtab_d[r];  c = ctab_d[r]

is exact, with zero correction steps.

This script measures that, plus the residual distribution of affine estimates
n ~ a*B + b (+ c*B^2) and the number of 0/1/2 correction steps each would need,
and simulates the all-float32 arithmetical realisation of the divmod.

Run: python3 analyze.py
"""

from __future__ import annotations

import math
from collections import Counter

import numpy as np

from ref import NMAX, build

PIECES, OUT, L, OWNER = build()
NB = len(OUT)
NBLOCK = 4096

F32 = np.float32


def P(d: int) -> int:
    return 8 * d + 47


REG = {
    2: dict(N=10, B0=30, d=2),
    3: dict(N=100, B0=408, d=3),
    4: dict(N=1000, B0=4668, d=4),
}
REG_END = {1: 30, 2: 408, 3: 4668, 4: NB}


def piece_len(n: int, d: int) -> int:
    if n % 15 == 0:
        return 9
    if n % 3 == 0 or n % 5 == 0:
        return 5
    return d + 1


def slot_tables(d: int):
    Pd = P(d)
    N = 10 ** (d - 1)
    jtab = [0] * Pd
    ctab = [0] * Pd
    pos = 0
    for j in range(15):
        ln = piece_len(N + j, d)
        for k in range(ln):
            jtab[pos + k] = j
            ctab[pos + k] = k
        pos += ln
    assert pos == Pd, (d, pos, Pd)
    return jtab, ctab


def exact_inversion_stats():
    bad = 0
    for d, info in REG.items():
        jtab, ctab = slot_tables(d)
        Pd = P(d)
        for B in range(info["B0"], REG_END[d]):
            q, r = divmod(B - info["B0"], Pd)
            n = info["N"] + 15 * q + jtab[r]
            c = ctab[r]
            if (n, c) != OWNER[B]:
                bad += 1
    for B in range(0, 30):
        n, c = OWNER[B]
        if not (1 <= n <= 9 and c == B - L[n]):
            bad += 1
    return bad


def check_period_closed_form():
    ok = True
    for d, info in REG.items():
        jtab, _ = slot_tables(d)
        N, B0, Pd = info["N"], info["B0"], P(d)
        endn = 10 ** d - 1
        for q in range(0, (endn - N) // 15 + 1):
            for j in range(15):
                n = N + 15 * q + j
                if n > NMAX or n > endn:
                    continue
                r0 = jtab.index(j)
                if L[n] != B0 + q * Pd + r0:
                    ok = False
    return ok


def ls_affine(Bs, ns):
    m = len(Bs)
    Sb = sum(Bs)
    Sn = sum(ns)
    Sbb = sum(b * b for b in Bs)
    Sbn = sum(b * n for b, n in zip(Bs, ns))
    det = m * Sbb - Sb * Sb
    a = (m * Sbn - Sb * Sn) / det
    b0 = (Sn - a * Sb) / m
    return a, b0


def ls_quadratic(Bs, ns):
    S = [0.0] * 5
    T = [0.0] * 3
    for B, n in zip(Bs, ns):
        p = 1.0
        for k in range(5):
            S[k] += p
            p *= B
        p = 1.0
        for k in range(3):
            T[k] += n * p
            p *= B
    A = [[S[0], S[1], S[2]], [S[1], S[2], S[3]], [S[2], S[3], S[4]]]
    b = T[:]
    for i in range(3):
        p = max(range(i, 3), key=lambda r: abs(A[r][i]))
        A[i], A[p] = A[p], A[i]
        b[i], b[p] = b[p], b[i]
        for r in range(i + 1, 3):
            f = A[r][i] / A[i][i]
            for cc in range(i, 3):
                A[r][cc] -= f * A[i][cc]
            b[r] -= f * b[i]
    c = [0.0] * 3
    for i in reversed(range(3)):
        c[i] = (b[i] - sum(A[i][j] * c[j] for j in range(i + 1, 3))) / A[i][i]
    return c


def summary(name, residuals):
    lo, hi = min(residuals), max(residuals)
    mean = sum(residuals) / len(residuals)
    print(f"   {name}: min={lo:.4f} max={hi:.4f} mean={mean:.4f} span={hi - lo:.4f}")
    # binned histogram, 1-unit bins
    h = Counter(int(math.floor(r)) for r in residuals)
    lo_b, hi_b = min(h), max(h)
    if hi_b - lo_b <= 14:
        print(f"      floor-bin histogram: {dict(sorted(h.items()))}")


def correction_step_table():
    """Per-region exact-rational floored affine: scan-up steps and error."""
    rows = {}
    all_steps = Counter()
    all_err = Counter()
    for d in (1, 2, 3, 4):
        if d == 1:
            N, B0, Pd, Bend = 1, 0, 55, 30
        else:
            info = REG[d]
            N, B0, Pd, Bend = info["N"], info["B0"], P(d), REG_END[d]
        steps = Counter()
        err = Counter()
        for B in range(B0, Bend):
            nt = OWNER[B][0]
            ne = N + (15 * (B - B0)) // Pd
            err[nt - ne] += 1
            all_err[nt - ne] += 1
            m = max(1, min(ne, NMAX))
            k = 0
            while not (L[m] <= B < L[m + 1]):
                m += 1
                k += 1
                if m > NMAX:
                    k = 99
                    break
            steps[k] += 1
            all_steps[k] += 1
        rows[d] = (dict(sorted(err.items())), dict(sorted(steps.items())))
    return rows, dict(sorted(all_err.items())), dict(sorted(all_steps.items()))


def rounded_affine():
    tot = Counter()
    per = {}
    for d, info in REG.items():
        Pd = P(d)
        N, B0 = info["N"], info["B0"]
        h = Counter()
        for B in range(B0, REG_END[d]):
            nt = OWNER[B][0]
            ne = N + int(math.floor((15.0 * (B - B0)) / Pd + 0.5))
            h[nt - ne] += 1
            tot[nt - ne] += 1
        per[d] = dict(sorted(h.items()))
    return per, dict(sorted(tot.items()))


def divmod_float32_bias():
    """Find biases b such that q = floor(float32(R)*float32(1/P) + b) == R//P."""
    out = []
    for d, info in REG.items():
        Pd = P(d)
        Rmax = REG_END[d] - info["B0"]
        R = np.arange(Rmax, dtype=np.float32)
        x = R * F32(1.0 / Pd)
        true_q = np.arange(Rmax, dtype=np.int64) // Pd
        frac = x.astype(np.float64) - np.floor(x.astype(np.float64))
        # valid b: for all R with floor(exact)=floor(x): b >= ceil(-frac) and b < 1-frac
        # simply scan a grid
        ok = []
        for bias in (0.0005, 0.001, 0.002, 0.005, 0.01):
            q = np.floor(x + F32(bias)).astype(np.int64)
            if np.array_equal(q, true_q):
                ok.append(bias)
        out.append(dict(d=d, P=Pd, Rmax=Rmax,
                        min_frac=float(frac[frac > 1e-9].min()) if (frac > 1e-9).any() else None,
                        max_frac=float(frac.max()),
                        ok_biases=ok))
    return out


def main():
    print("== 0. structural facts ==")
    print("   output bytes:", NB, "blocks:", NBLOCK, "L(6334):", L[NMAX])
    print("   L(10)=%d L(100)=%d L(1000)=%d" % (L[10], L[100], L[1000]))
    print("   periods P_d (bytes per 15 numbers):", {d: P(d) for d in (1, 2, 3, 4)})
    print("   per-period closed form L(N+15q+j) = B0 + q*P_d + cum[j]:",
          check_period_closed_form())

    bad = exact_inversion_stats()
    print("\n== 1. exact divmod inversion ==")
    print("   bytes needing a correction step:", bad, "/", NB)

    print("\n== 2. global affine n ~ a*B+b (least squares, all 32766 bytes) ==")
    Bs = list(range(NB))
    ns = [OWNER[B][0] for B in Bs]
    a, b0 = ls_affine(Bs, ns)
    print(f"   a={a:.12f} b={b0:.6f}")
    summary("global affine residual", [n - (a * B + b0) for B, n in zip(Bs, ns)])

    print("\n== 3. global quadratic n ~ c0+c1*B+c2*B^2 ==")
    c = ls_quadratic(Bs, ns)
    print(f"   c0={c[0]:.9f} c1={c[1]:.12f} c2={c[2]:.6e}")
    summary("global quadratic residual",
            [n - (c[0] + c[1] * B + c[2] * B * B) for B, n in zip(Bs, ns)])

    print("\n== 4. per-region exact-rational affine, floored ==")
    rows, all_err, all_steps = correction_step_table()
    for d in sorted(rows):
        e, st = rows[d]
        print(f"   d={d}: error(n_true-n_est)={e}")
        print(f"         candidate-scan steps={st}")
    print(f"   ALL: error={all_err}")
    print(f"        scan steps={all_steps}")

    print("\n== 5. per-region affine, rounded to nearest ==")
    per, tot = rounded_affine()
    for d in sorted(per):
        print(f"   d={d}: {per[d]}")
    print(f"   ALL: {tot}")

    print("\n== 6. float32 divmod: q = floor(R*float32(1/P) + bias) ==")
    for r in divmod_float32_bias():
        print("   " + ", ".join(f"{k}={v}" for k, v in r.items()))

    print("\n== 7. integer reconstruction r = R - P*q ==")
    for d, info in REG.items():
        Pd = P(d)
        Rmax = REG_END[d] - info["B0"]
        R = np.arange(Rmax, dtype=np.float32)
        x = R * F32(1.0 / Pd)
        q = np.floor(x + F32(0.002)).astype(np.int64)
        rr = np.arange(Rmax, dtype=np.int64) - Pd * q
        print(f"   d={d}: 0<=r<P for all R: {bool((rr >= 0).all() and (rr < Pd).all())}, "
              f"max|r-(R mod P)|={int(np.abs(rr - (np.arange(Rmax) % Pd)).max())}")


if __name__ == "__main__":
    main()
