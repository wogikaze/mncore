"""Analyze a traced `sep.join(f(i) for i in range(a, b))` into periodic blocks.

The item function is traced once with a symbolic index. The result is a
`Cat`/`Sel` tree: per-item strings selected by symbolic conditions, with `Dec`
leaves standing for `str(<integer expr>)`. Every check is exact, done by
enumerating the range; any violation raises CompileError.
"""

from __future__ import annotations

from dataclasses import dataclass

from .errors import CompileError
from .ir import Graph, evaluate
from .strsym import Cat, Concat, Dec, Sel, to_strval
from .trace import Sym, _fork_merge, _state


@dataclass(frozen=True)
class Number:
    a: int
    b: int  # value = a*i + b for item variable i


@dataclass(frozen=True)
class Leaf:
    parts: tuple  # str | int (int = index into plan.numbers); separator NOT included


@dataclass
class Block:
    lo: int
    hi: int  # item variable range [lo, hi)
    digits: tuple  # decimal digit count of each plan.numbers entry (constant in the block)
    period_bytes: int  # S = sum of item lengths (incl. separator) over one period
    base: int  # pos(i) = base + S*q + offsets[k], (q, k) = divmod(i - plan.start, plan.period); may be negative
    offsets: tuple  # length plan.period, offsets[0] == 0, prefix sums of item lengths in this block


@dataclass
class ConcatPlan:
    sep: str
    start: int
    stop: int
    period: int
    leaves: list
    numbers: list
    leaf_of: tuple  # length period: leaf index of items with k = (i - start) % period
    blocks: list
    length: int  # total bytes of the joined string


def analyze_concat(c: Concat) -> ConcatPlan:
    rng = c.rng
    if not isinstance(rng, range) or rng.step != 1:
        raise CompileError("concat: range must have step 1")
    start, stop, n = rng.start, rng.stop, len(rng)
    if n == 0:
        raise CompileError("concat: empty range")
    if n > 1 << 20:
        raise CompileError("concat: too many items")
    sep = c.sep
    try:
        sep.encode("latin-1")
    except UnicodeEncodeError:
        raise CompileError("concat: separator is not latin-1 encodable")

    graph = Graph()
    _state.graph = graph
    try:
        i = Sym(graph.input("__i", (), "i"))
        res = _fork_merge(c.body, (i,), {})
    finally:
        _state.graph = None
        _state.recorder = None
    if not isinstance(res, (str, Cat, Sel)):
        raise CompileError("concat: item is not a string")
    res = to_strval(res)

    def eval1(node, i):
        return evaluate([node], {("__i", ()): i})[0]

    # distinct Cat leaves of the Sel tree, in discovery order
    leaves = []

    def collect(v):
        if isinstance(v, Cat):
            if v not in leaves:
                leaves.append(v)
        elif isinstance(v, Sel):
            collect(v.a)
            collect(v.b)

    collect(res)

    def pick(v, i):
        while isinstance(v, Sel):
            v = v.a if eval1(v.cond, i) else v.b
        return v

    leaf_idx = [leaves.index(pick(res, i)) for i in range(start, stop)]

    # distinct Dec nodes -> affine numbers a*i + b, verified where used
    dec_nodes = []
    for leaf in leaves:
        for p in leaf.parts:
            if isinstance(p, Dec) and p.node not in dec_nodes:
                dec_nodes.append(p.node)
    num_idx = {node: k for k, node in enumerate(dec_nodes)}
    numbers = []
    for node in dec_nodes:
        a = eval1(node, start + 1) - eval1(node, start)
        numbers.append(Number(a, eval1(node, start) - a * start))
    for i in range(start, stop):
        for p in leaves[leaf_idx[i - start]].parts:
            if isinstance(p, Dec):
                num = numbers[num_idx[p.node]]
                v = eval1(p.node, i)
                if v != num.a * i + num.b or v < 0:
                    raise CompileError("concat: str() argument is not a nonnegative affine function of the index")

    # smallest period of the leaf-choice sequence
    period = None
    for p in range(1, 65):
        if all(leaf_idx[j] == leaf_idx[j + p] for j in range(n - p)):
            period = p
            break
    if period is None:
        raise CompileError("concat: leaf choice is not periodic")
    leaf_of = tuple(leaf_idx[k] for k in range(period))

    # concrete positions of every item
    items = [c.body(i) for i in rng]
    pos = [0] * (n + 1)
    for j, it in enumerate(items):
        pos[j + 1] = pos[j] + len(it) + len(sep)
    length = pos[n] - len(sep)

    # blocks: maximal runs of i with equal digit counts over all numbers
    blocks = []
    for i in range(start, stop):
        digits = tuple(len(str(num.a * i + num.b)) for num in numbers)
        if blocks and blocks[-1].digits == digits:
            blocks[-1].hi = i + 1
            continue
        item_len = [
            len(sep) + sum(len(p) if isinstance(p, str) else digits[num_idx[p.node]] for p in leaves[leaf_of[k]].parts)
            for k in range(period)
        ]
        offsets = [0] * period
        for k in range(1, period):
            offsets[k] = offsets[k - 1] + item_len[k - 1]
        s = sum(item_len)
        q, k = divmod(i - start, period)
        blocks.append(Block(i, i + 1, digits, s, pos[i - start] - s * q - offsets[k], tuple(offsets)))

    bi = 0
    for i in range(start, stop):
        while i >= blocks[bi].hi:
            bi += 1
        blk = blocks[bi]
        q, k = divmod(i - start, period)
        if blk.base + blk.period_bytes * q + blk.offsets[k] != pos[i - start]:
            raise CompileError("concat: position formula does not match the concrete layout")

    plan = ConcatPlan(
        sep, start, stop, period,
        [Leaf(tuple(num_idx[p.node] if isinstance(p, Dec) else p for p in leaf.parts)) for leaf in leaves],
        numbers, leaf_of, blocks, length,
    )
    if render(plan) != sep.join(items):
        raise CompileError("concat: plan does not reproduce the joined string")
    return plan


def render(plan: ConcatPlan) -> str:
    """Rebuild the joined string from the plan alone."""
    out = []
    for i in range(plan.start, plan.stop):
        leaf = plan.leaves[plan.leaf_of[(i - plan.start) % plan.period]]
        out.append(
            "".join(p if isinstance(p, str) else str(plan.numbers[p].a * i + plan.numbers[p].b) for p in leaf.parts)
        )
    return plan.sep.join(out)
