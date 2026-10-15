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


def synthesize(gen, x, perm, bits, dst):
    """Emit ops computing the permutation of operand x; returns the result value (None if written to dst)."""
    q = {64: "l", 32: "i", 16: "s"}[bits]
    c = xor_constant(perm)
    if c is None:
        raise CompileError("bit permutation is not an XOR permutation")
    if c == 0:
        return gen.emit("lpassa", [x], dst)
    high = c & ~7 & (bits - 1)
    low = c & 7
    stages = []
    if high:
        target = [i ^ high for i in range(bits)]
        plan = rotation_plan(target, bits, max_ops=3)
        if plan is None:
            # one rotation per stage: swapping the halves of every 2k-bit field is a rotation by k
            plan = [(2 * k, k) for k in (8, 16, 32) if high & k]
        stages += [("rot", w, k) for w, k in plan]
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
