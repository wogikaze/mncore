#!/usr/bin/env python3
"""Builds viz/core/src/hmul_ext_round.bin from exhaustive emulator measurements.

Input: the three files written by exhaust.py (one line `e o bits` per pair of
mantissas, `bits` the single-precision hmmul output of the single product):
    exhaust.py row.txt row     # matrix element extended (shift 6)
    exhaust.py vec.txt vec     # vector element extended (shift 6)
    exhaust.py both.txt both   # both extended (shift 12)
Common exponents are 30 for both blocks, so every output is q * 2^-18 where q
is the product after the shift and the emulator's rounding.

Output layout (bits, LSB first within a byte):
    [0, 8192)        shift 6:  index (e & 63) << 7 | (o & 63) << 1 | parity
    [8192, 270336)   shift 12: index e << 9 | o
A set bit means the emulator rounds floor(e * o / 2^shift) up by one; parity is
bit 0 of that floor. The row and vector tables are identical and symmetric,
and the shift-6 decision depends only on the low six bits of each mantissa and
the parity; make_table checks both before writing.
"""
import struct
import sys


def load(path, shift):
    table = {}
    for line in open(path):
        e, o, bits = map(int, line.split())
        q = struct.unpack(">f", struct.pack(">I", bits))[0] * 2.0 ** 18
        qi = round(q)
        assert abs(q - qi) < 1e-9, (e, o, q)
        up = qi - ((e * o) >> shift)
        assert up in (0, 1), (e, o, up)
        table[(e, o)] = up
    assert len(table) == 512 * 512, path
    return table


def main():
    row_path, vec_path, both_path, out_path = sys.argv[1:5]
    row, vec, both = load(row_path, 6), load(vec_path, 6), load(both_path, 12)
    assert row == vec, "row and vector tables differ"
    six = {}
    for (e, o), up in row.items():
        assert row[(o, e)] == up
        key = ((e & 63) << 7) | ((o & 63) << 1) | (((e * o) >> 6) & 1)
        assert six.setdefault(key, up) == up, "shift-6 decision needs more than the low bits"
    bits = bytearray(270336 // 8)
    for key, up in six.items():
        if up:
            bits[key >> 3] |= 1 << (key & 7)
    for (e, o), up in both.items():
        assert both[(o, e)] == up
        if up:
            key = 8192 + ((e << 9) | o)
            bits[key >> 3] |= 1 << (key & 7)
    open(out_path, "wb").write(bits)
    print(f"{out_path}: {len(bits)} bytes, shift-6 keys {len(six)} of 8192")


if __name__ == "__main__":
    main()
