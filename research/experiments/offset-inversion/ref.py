#!/usr/bin/env python3
"""Exact FizzBuzz reference: output bytes, owner table, cumulative length L(n).

Everything here is derived from the problem statement only:
  1..6334, FizzBuzz/Fizz/Buzz/str(n), joined by '\n', no trailing '\n'.

The official testcase expectations (the 4096 `d getd` lines in
problems/challenge/20.fizzbuzz/testcase.vsm) are parsed and compared byte for
byte.

owner[B] = (n, k): output byte B is character k (0-based) of number n's
rendering (rendering includes the terminating '\n' except for n=6334).
L(n) = first output byte of number n's rendering, L(1)=0.

Run:  python3 ref.py
"""

from __future__ import annotations

import codecs
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
TESTCASE = ROOT / "problems/challenge/20.fizzbuzz/testcase.vsm"
NMAX = 6334


def render(n: int) -> bytes:
    """Rendering of n including its terminating newline."""
    if n % 15 == 0:
        return b"FizzBuzz\n"
    if n % 3 == 0:
        return b"Fizz\n"
    if n % 5 == 0:
        return b"Buzz\n"
    return str(n).encode() + b"\n"


def build():
    pieces = [render(n) for n in range(1, NMAX + 1)]
    pieces[-1] = pieces[-1][:-1]  # problem: no trailing newline
    out = b"".join(pieces)

    L = [0] * (NMAX + 2)
    for n in range(1, NMAX + 1):
        L[n + 1] = L[n] + len(pieces[n - 1])

    owner = []  # (n, k)
    for n in range(1, NMAX + 1):
        for k in range(len(pieces[n - 1])):
            owner.append((n, k))
    assert len(owner) == len(out)
    return pieces, out, L, owner


def official_expectation() -> bytes:
    """Concatenate the official testcase's per-word expectations."""
    text = TESTCASE.read_text(encoding="utf-8")
    words: dict[int, bytes] = {}
    for m in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="((?:[^"\\]|\\.)*)"', text):
        words[int(m.group(1))] = codecs.decode(m.group(2), "unicode_escape").encode("latin-1")
    assert sorted(words) == list(range(4096)), f"got {len(words)} dumps"
    return b"".join(words[i] for i in range(4096))


def check() -> dict:
    pieces, out, L, owner = build()
    expected = official_expectation()

    ok_len = len(out) == 32766
    # The last official word is 6 bytes ("z\n6334"); pad it to 8 with the
    # not-written bytes and compare only the meaningful prefix.
    ok_bytes = out == expected[: len(out)]
    # owner is a bijection and agrees with L
    ok_L = all(
        L[n] < L[n + 1] and L[n + 1] - L[n] == len(pieces[n - 1])
        for n in range(1, NMAX + 1)
    )
    ok_owner = all(owner[L[n] + k] == (n, k) for n in range(1, NMAX + 1) for k in range(len(pieces[n - 1])))
    # inverse: for every byte, L(n) + k == B
    ok_inv = all(L[n] + k == B for B, (n, k) in enumerate(owner))
    # official dump addresses -> byte offsets
    ok_last = expected[len(out):] == b""

    mism = sum(1 for i, (a, b) in enumerate(zip(out, expected)) if a != b)
    return dict(
        length=len(out),
        expected_length=len(expected),
        ok_len=ok_len,
        ok_bytes=ok_bytes,
        ok_L=ok_L,
        ok_owner=ok_owner,
        ok_inv=ok_inv,
        mismatches=mism,
        L1000=L[1000],
        L100=L[100],
        L10=L[10],
        L6334=L[NMAX],
    )


def main() -> int:
    r = check()
    print("reference:", r)
    pieces, out, L, owner = build()
    # A few spot checks against the problem statement's example.
    assert out[:8] == b"1\n2\nFizz", out[:8]
    assert out[32760:] == b"z\n6334", out[32760:]
    ok = r["ok_len"] and r["ok_bytes"] and r["ok_L"] and r["ok_owner"] and r["ok_inv"] and r["mismatches"] == 0
    print("ALL-OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
