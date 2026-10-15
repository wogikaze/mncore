"""Bit permutations of one integer lane (byte swaps, bit reversals, ...).

An integer expression of a single input lane is recognised as a bit
permutation by evaluating it on the unit vectors (and checking linearity on
random values). XOR permutations (bit i -> bit i ^ c) are synthesised stage by
stage: stages that swap halves of 16-, 32- or 64-bit fields are barrel
rotations of the matching lane width (the shortest rotation sequence with
shared shift-amount constants is searched); the other stages are mask-and-shift
swaps.
"""

from __future__ import annotations

import itertools
import random

from .errors import CompileError
from .ir import evaluate, walk

BITOPS = {"or", "sum", "add", "and", "shl", "shr", "xor"}


def recognize(node, bits):
    """(leaf, perm) with output bit perm[i] = input bit i, or None."""
    if node.ty != "i" or node.op not in BITOPS:
        return None
    leaves = {n.value: n for n in walk([node]) if n.op == "input"}
    if len(leaves) != 1:
        return None
    (key, leaf), = leaves.items()
    mask = (1 << bits) - 1

    def f(x):
        return evaluate([node], {key: x})[0]

    if f(0) != 0:
        return None
    perm = []
    for i in range(bits):
        y = f(1 << i)
        if y <= 0 or y > mask or y & (y - 1):
            return None
        perm.append(y.bit_length() - 1)
    if sorted(perm) != list(range(bits)):
        return None
    rng = random.Random(7)
    for _ in range(8):
        x = rng.getrandbits(bits)
        want = 0
        for i in range(bits):
            if x >> i & 1:
                want |= 1 << perm[i]
        if f(x) != want:
            return None
    return leaf, perm


def _rotate_perm(width, amount, bits):
    """Bit index map of a left barrel rotation by `amount` inside every `width`-bit field."""
    return [(i & ~(width - 1)) | ((i + amount) % width) for i in range(bits)]


def _compose(p, q):
    """Apply p then q."""
    return [q[p[i]] for i in range(len(p))]


def rotation_plan(target, bits, max_ops=4):
    """Shortest sequence of field rotations (with as few shift constants as possible) realising
    `target`; returns [(width, amount_constant)] where the constant is replicated per 16-bit field."""
    widths = [w for w in (16, 32, 64) if w <= bits]
    ident = list(range(bits))
    best = None
    # constants: a 16-bit value replicated in every 16-bit field; the shift amount of a w-bit field is
    # (constant replicated over w/16 fields) mod w = c16 mod w for w >= 16
    for n_ops in range(1, max_ops + 1):
        for seq in itertools.product(widths, repeat=n_ops):
            # one shared constant c16 for all the rotations
            for c16 in range(1, 64):
                p = ident
                for w in seq:
                    p = _compose(p, _rotate_perm(w, c16 % w, bits))
                if p == target:
                    return [(w, c16) for w in seq]
    return best


def xor_constant(perm):
    c = perm[0]
    return c if all(perm[i] == i ^ c for i in range(len(perm))) else None


def _two_rotations(target, bits):
    """[(w1, k1), (w2, k2)]: two field rotations with their own amounts realising `target`."""
    widths = [w for w in (16, 32, 64) if w <= bits]
    for w1, w2 in itertools.product(widths, repeat=2):
        for k1 in range(1, w1):
            p1 = _rotate_perm(w1, k1, bits)
            for k2 in range(1, w2):
                if _compose(p1, _rotate_perm(w2, k2, bits)) == target:
                    return [(w1, k1), (w2, k2)]
    return None


def _amount_ok(bits32, w, k):
    """Does a 32-bit word (replicated over the long) rotate every w-bit field by k?"""
    if w == 16:
        return (bits32 >> 16) % 16 == k and (bits32 & 0xFFFF) % 16 == k
    if w == 32:
        return bits32 % 32 == k
    return False


def _derived_pair(w1, k1, w2, k2):
    """A 32-bit constant C (a normal f32) for the first rotation such that fma(C, C, C) in f32 gives
    the second rotation's amount: one immediate, the second constant from the idle MAU."""
    import numpy as np

    lows = [lo for lo in range(1 << 16) if _amount_ok((k1 << 16) | lo, w1, k1) or w1 == 32 and lo % 32 == k1]
    for hi in range(0x3000, 0x4F00):
        cs = np.array([(hi << 16) | lo for lo in lows], dtype=np.uint32)
        ok1 = np.array([_amount_ok(int(c), w1, k1) for c in cs])
        if not ok1.any():
            continue
        f = cs[ok1].view(np.float32)
        d = (f.astype(np.float64) * f + f).astype(np.float32).view(np.uint32)
        for c, dv in zip(cs[ok1], d):
            if _amount_ok(int(dv), w2, k2) and np.isfinite(np.uint32(dv).view(np.float32)):
                return int(c)
    return None


def _word_swap_operands(x, dst):
    """Word-access operands (input words, output words with the halves swapped) covering at most two
    long words in four cycles, or None."""
    from .machine import Mem

    if not (isinstance(x, Mem) and isinstance(dst, Mem)) or x.wl != 2 or dst.wl != 2:
        return None
    if x.tind or dst.tind or dst.mask is not None or x.neg or x.ext or x.rnd:
        return None
    pairs = []
    for a, d in zip(x.addrs, dst.addrs):
        if (a, d) not in pairs:
            pairs.append((a, d))
    if len(pairs) > 2 or len({a for a, _ in pairs}) != len(pairs):
        return None
    while len(pairs) < 2:
        pairs.append(pairs[-1])
    (a0, d0), (a1, d1) = pairs
    xw = Mem(x.space, 1, (a0, a0 + 1, a1, a1 + 1))
    dw = Mem(dst.space, 1, (d0 + 1, d0, d1 + 1, d1))
    return xw, dw


def synthesize(gen, x, perm, bits, dst):
    """Emit ops computing the permutation of operand x; returns the result value (None if written to dst)."""
    q = {64: "l", 32: "i", 16: "s"}[bits]
    c = xor_constant(perm)
    if c is None:
        raise CompileError("bit permutation is not an XOR permutation")
    if c == 0:
        return gen.emit("lpassa", [x], dst)
    if bits == 64 and c & 32:
        words = _word_swap_operands(x, dst)
        if words is not None:
            # the 32-bit halves trade places by addressing: each output word is the other input
            # word under the remaining 32-bit permutation
            xw, dw = words
            return synthesize(gen, xw, [i ^ (c & 31) for i in range(32)], 32, dw)
    high = c & ~7 & (bits - 1)
    low = c & 7
    stages = []
    derived = None
    if high:
        target = [i ^ high for i in range(bits)]
        plan = rotation_plan(target, bits, max_ops=3)
        two = _two_rotations(target, bits) if plan is None or len(plan) > 2 else None
        if two is not None and not low:
            c = _derived_pair(*two[0], *two[1])
            if c is not None:
                derived = (two, c)
        if plan is None:
            # one rotation per stage: swapping the halves of every 2k-bit field is a rotation by k
            plan = [(2 * k, k) for k in (8, 16, 32) if high & k]
        stages += [("rot", w, k) for w, k in plan]
    if derived is not None:
        (w1, _k1), (w2, _k2) = derived[0]
        cval = gen.consts.word32(derived[1])
        dval = gen.emit("fvfma", [cval, cval, cval])  # the second shift amount, on the MAU
        p1, p2 = ({16: "s", 32: "i", 64: "l"}[w] for w in (w1, w2))
        mid = gen.emit(f"{p1}bsl", [x, cval])
        return gen.emit(f"{p2}bsl", [mid, dval], dst)
    for k in (1, 2, 4):
        if low & k:
            stages.append(("swap", k, None))
    cur = x
    for n, st in enumerate(stages):
        last = n == len(stages) - 1
        out = dst if last else None
        if st[0] == "rot":
            _, w, k = st
            p = {16: "s", 32: "i", 64: "l"}[w]
            amount = gen.consts.word16(k)
            cur = gen.emit(f"{p}bsl", [cur, amount], out)
        else:
            _, k, _ = st
            m = 0
            for i in range(bits):
                if not i & k:
                    m |= 1 << i
            mask = gen.consts.word64(m) if bits == 64 else gen.consts.word32(m)
            sh = gen.consts.word64(k) if bits == 64 else gen.consts.word32(k)
            a = gen.emit(f"u{q}lsr", [cur, sh])
            a = gen.emit(f"{q}and", [a, mask])
            b = gen.emit(f"{q}and", [cur, mask])
            b = gen.emit(f"{q}lsl", [b, sh])
            cur = gen.emit(f"{q}or", [a, b], out)
    return cur
