#!/usr/bin/env python3
"""Exact float32 helpers (RNE), half-precision (1,6,9) encode/decode."""
from fractions import Fraction as Fr
import struct, math
def f32(x):
    """round exact rational/float to nearest float32 (ties even); returns Fraction."""
    x = Fr(x)
    if x == 0: return Fr(0)
    s = -1 if x < 0 else 1
    a = abs(x)
    e = math.floor(math.log2(a.numerator) - math.log2(a.denominator))
    # fix e so that 2^e <= a < 2^(e+1)
    while Fr(2) ** e > a: e -= 1
    while Fr(2) ** (e + 1) <= a: e += 1
    ulp = Fr(2) ** (e - 23)
    q = a / ulp
    n = q.numerator // q.denominator
    r = q - n
    if r > Fr(1, 2) or (r == Fr(1, 2) and n % 2 == 1): n += 1
    return s * n * ulp
def bits32(x):
    return struct.unpack(">I", struct.pack(">f", float(x)))[0]
def from_bits32(b):
    return Fr(struct.unpack(">f", struct.pack(">I", b))[0])
def fma(a, b, c):
    return f32(Fr(a) * Fr(b) + Fr(c))
def half_bits(x):
    x = Fr(x)
    if x == 0: return 0
    s = 0x8000 if x < 0 else 0
    a = abs(x); e = 0
    while a >= 2: a /= 2; e += 1
    while a < 1: a *= 2; e -= 1
    man = (a - 1) * 512
    assert man.denominator == 1, f"{x} not half-exact"
    assert -30 <= e <= 31
    return s | ((e + 31) << 9) | int(man)
def is_half(x):
    try:
        half_bits(x); return True
    except AssertionError:
        return False
def hpair(a, b):
    return (half_bits(a) << 16) | half_bits(b)
