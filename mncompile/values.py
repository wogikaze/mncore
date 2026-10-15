"""Element encodings (MN-Core formats) and lane packing in 64-bit long words."""

from __future__ import annotations

import math
import struct

from .layout import DType

# (exponent bits, mantissa bits) of MN-Core floating-point formats. No subnormals,
# no NaN: exponent 0 is zero, all ones is infinity.
FORMATS = {64: (11, 52), 32: (8, 23), 16: (6, 9)}


def float_decode(bits: int, width: int) -> float:
    exp_bits, man_bits = FORMATS[width]
    sign = (bits >> (width - 1)) & 1
    exp = (bits >> man_bits) & ((1 << exp_bits) - 1)
    man = bits & ((1 << man_bits) - 1)
    s = -1.0 if sign else 1.0
    if exp == 0:
        return s * 0.0
    if exp == (1 << exp_bits) - 1:
        return s * math.inf
    bias = (1 << (exp_bits - 1)) - 1
    return s * math.ldexp(float((1 << man_bits) | man), exp - bias - man_bits)


def float_encode(value: float, width: int) -> int:
    """Round to nearest even in the MN-Core format (flush to zero, overflow to inf)."""
    exp_bits, man_bits = FORMATS[width]
    bias = (1 << (exp_bits - 1)) - 1
    sign = 1 if math.copysign(1.0, value) < 0 else 0
    a = abs(value)
    if a == 0.0:
        return sign << (width - 1)
    if math.isinf(a):
        return (sign << (width - 1)) | (((1 << exp_bits) - 1) << man_bits)
    if width == 64:
        bits = struct.unpack(">Q", struct.pack(">d", a))[0]
        exp = (bits >> 52) & 0x7FF
        if exp == 0:
            return sign << 63
        return (sign << 63) | bits
    m, e = math.frexp(a)  # a = m * 2**e, 0.5 <= m < 1
    exp = e - 1 + bias
    # significand with man_bits fraction bits
    scaled = m * (1 << (man_bits + 1))
    sig = int(scaled)
    rest = scaled - sig
    if rest > 0.5 or (rest == 0.5 and sig & 1):
        sig += 1
    if sig >> (man_bits + 1):
        sig >>= 1
        exp += 1
    if exp <= 0:
        return sign << (width - 1)
    if exp >= (1 << exp_bits) - 1:
        return (sign << (width - 1)) | (((1 << exp_bits) - 1) << man_bits)
    return (sign << (width - 1)) | (exp << man_bits) | (sig & ((1 << man_bits) - 1))


def round_to(value: float, width: int) -> float:
    return float_decode(float_encode(value, width), width)


def decode(bits: int, dtype: DType):
    bits &= (1 << dtype.bits) - 1
    if dtype.kind == "uint":
        return bits
    if dtype.kind == "int":
        return bits - (1 << dtype.bits) if bits >> (dtype.bits - 1) else bits
    if dtype.kind == "float":
        return float_decode(bits, dtype.bits)
    if dtype.kind == "bytes":
        return bits
    raise ValueError(dtype)


def encode(value, dtype: DType) -> int:
    if dtype.kind in ("uint", "int", "bytes"):
        return int(value) % (1 << dtype.bits)
    return float_encode(float(value), dtype.bits)


def lane_shift(dtype: DType, lane: int) -> int:
    return 64 - dtype.bits * (lane + 1)


def pack(lanes: dict[int, int], dtype: DType, base: int = 0) -> int:
    """Long word with raw lane bits placed (lane 0 = MSB side)."""
    word = base
    mask = (1 << dtype.bits) - 1
    for lane, bits in lanes.items():
        shift = lane_shift(dtype, lane)
        word = (word & ~(mask << shift)) | ((bits & mask) << shift)
    return word


def unpack(word: int, dtype: DType, lane: int) -> int:
    return (word >> lane_shift(dtype, lane)) & ((1 << dtype.bits) - 1)


def matches(actual, expected, dtype: DType, atol: float) -> bool:
    """Judge rule: |actual - expected| <= atol (an infinite pair with the same sign matches)."""
    if dtype.kind in ("int", "uint", "bytes"):
        if isinstance(expected, str):
            expected = ord(expected)
        return int(actual) == int(expected) % (1 << dtype.bits) if dtype.kind != "int" else int(actual) == _wrap_signed(int(expected), dtype.bits)
    a, e = float(actual), float(expected)
    if math.isinf(e) or math.isinf(a):
        return a == e
    return abs(a - e) <= atol


def _wrap_signed(v, bits):
    v %= 1 << bits
    return v - (1 << bits) if v >> (bits - 1) else v
