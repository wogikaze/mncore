"""Transformation library over the 93-word FizzBuzz program.

Every generator yields `Mutation` objects.  Nothing here assumes semantic
equivalence: the simulator is the only judge.  The generators exist to make
the search space explicit and to pre-filter structurally impossible rows
(one ALU per line, MV alone, ...) so evaluations are not wasted on programs
the assembler would reject on field conflicts alone.

Families
--------
delete      drop a row (nop or instruction)
repair      drop a copy row and substitute its source at later uses
merge       fuse two adjacent rows
split       split one row into two (costs a word; used to enable moves)
move        move one expression to another row (may empty a row => -1 word)
dissolve    move both expressions of a 2-expression row to two other rows
relocate    move a whole row to another position (word-neutral)
swap        exchange two adjacent rows (word-neutral)
commute     swap the two source operands of a commutative expression
const       replace an immediate with an equivalent literal
addr        rewrite an addressing form to an equivalent encoding
reorder     swap the expressions inside a row (word-neutral)
noforward   move the `noforward` marker to another row
insert_nop  insert a nop (word +1; repairs a hazard for a later move)
"""

from __future__ import annotations

import re
from dataclasses import dataclass, replace
from typing import Iterator

from mncompile.machine import ALU_OPS, Fwd, Imm, Mem

from . import vsmx
from .vsmx import Program, Row


@dataclass
class Mutation:
    program: Program
    family: str
    detail: str

    @property
    def delta(self) -> int:
        return 0


def _rows_with(prog: Program, i: int, instrs: list) -> list[Row]:
    out = list(prog.rows)
    out[i] = vsmx.set_instrs(prog.rows[i], instrs)
    return out


def _mut(prog: Program, rows: list[Row], family: str, detail: str) -> Mutation:
    return Mutation(prog.clone(rows=rows, chain_add=f"{family}:{detail}"), family, detail)


# ------------------------------------------------------------------ delete


def delete(prog: Program, src_rows: set[int] | None = None) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        if src_rows is not None and i not in src_rows:
            continue
        rows = vsmx.drop_row(prog.rows, i)
        yield _mut(prog, rows, "delete", f"L{i + 1}")


def repair(prog: Program) -> Iterator[Mutation]:
    """Drop a one-expression copy and rewrite later uses of its destination."""
    for i, row in enumerate(prog.rows):
        if row.nop or len(row.instrs) != 1:
            continue
        ins = row.instrs[0]
        op = ins.opcode.split("/")[0]
        if op not in _PASS_OPS:
            continue
        if len(ins.srcs) != 1 or len(ins.dsts) != 1:
            continue
        src, dst = ins.srcs[0], ins.dsts[0]
        if not isinstance(src, Mem) or not isinstance(dst, Mem):
            continue
        if src.wl != dst.wl:
            continue
        old, new = dst.text(), src.text()
        if old == new or old == "$nowrite":
            continue
        rows = []
        for j, r in enumerate(prog.rows):
            if j == i:
                continue
            if j < i:
                rows.append(r)
                continue
            changed = False
            instrs = []
            for e in r.instrs:
                new_srcs = []
                for o in e.srcs:
                    if isinstance(o, Mem) and o.text() == old:
                        new_srcs.append(_parse_like(new, o))
                        changed = True
                    else:
                        new_srcs.append(o)
                new_dsts = []
                for o in e.dsts:
                    if isinstance(o, Mem) and o.text() == old:
                        new_dsts.append(_parse_like(new, o))
                        changed = True
                    else:
                        new_dsts.append(o)
                instrs.append(replace(e, srcs=tuple(new_srcs), dsts=tuple(new_dsts)))
            rows.append(vsmx.set_instrs(r, instrs) if changed else r)
        yield _mut(prog, rows, "repair", f"L{i + 1}->{new}")


_PASS_OPS = {"passa", "ipassa", "lpassa", "fvpassa", "mvpassa", "hvpassa",
             "ffpassa", "fpassa", "ifpassa"}


def _parse_like(text: str, like):
    """Parse `text` as an operand, keeping the mask of `like` when present."""
    from mncompile.machine import parse_operand

    o = parse_operand(text)
    return replace(o, mask=getattr(like, "mask", None)) if isinstance(o, Mem) else o


# ------------------------------------------------------------------ merge


def merge(prog: Program) -> Iterator[Mutation]:
    n = len(prog.rows)
    for i in range(n - 1):
        a, b = prog.rows[i], prog.rows[i + 1]
        if a.nop or b.nop:
            continue
        for order, x, y in (("ab", a, b), ("ba", b, a)):
            extra = y.instrs
            if not all(vsmx.can_host(x, e) for e in extra):
                continue
            instrs = list(x.instrs) + list(extra)
            rows = list(prog.rows)
            rows[i] = vsmx.set_instrs(x, instrs)
            del rows[i + 1]
            yield _mut(prog, rows, "merge", f"L{i + 1}+L{i + 2}/{order}")


def split(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        if row.nop or len(row.instrs) < 2:
            continue
        for k in range(1, len(row.instrs)):
            rows = list(prog.rows)
            rows[i:i + 1] = [
                vsmx.set_instrs(row, row.instrs[:k]),
                vsmx.set_instrs(row, row.instrs[k:]),
            ]
            yield _mut(prog, rows, "split", f"L{i + 1}@{k}")


# ------------------------------------------------------------------ move


def move_expr(prog: Program, positions: bool = False,
              src_rows: set[int] | None = None) -> Iterator[Mutation]:
    """Move one expression to another row; a row that loses its last
    expression is removed, which is the only way this reduces words."""
    n = len(prog.rows)
    for i, row in enumerate(prog.rows):
        if row.nop:
            continue
        if src_rows is not None and i not in src_rows:
            continue
        for e_idx, expr in enumerate(row.instrs):
            for j, dst in enumerate(prog.rows):
                if i == j or not vsmx.can_host(dst, expr):
                    continue
                for place in (("append",) if not positions else ("append", "prepend")):
                    rows = []
                    for k, r in enumerate(prog.rows):
                        if k == i:
                            rest = row.instrs[:e_idx] + row.instrs[e_idx + 1:]
                            if rest:
                                rows.append(vsmx.set_instrs(row, rest))
                            continue
                        if k == j:
                            ins = list(r.instrs)
                            if place == "append":
                                ins = ins + [expr]
                            else:
                                ins = [expr] + ins
                            rows.append(vsmx.set_instrs(r, ins))
                        else:
                            rows.append(r)
                    yield _mut(prog, rows, "move",
                               f"L{i + 1}.{e_idx}->L{j + 1}/{place}")


def dissolve(prog: Program, targets_limit: int = 64) -> Iterator[Mutation]:
    """Move both expressions of a two-expression row into two other rows."""
    n = len(prog.rows)
    for i, row in enumerate(prog.rows):
        if len(row.instrs) != 2:
            continue
        a, b = row.instrs
        # Candidate hosts for each expression; both orders (a->j,b->k) and
        # (b->j,a->k) are useful because the destination row's unit mix differs.
        cand_a = [j for j in range(n) if j != i and vsmx.can_host(prog.rows[j], a)]
        cand_b = [j for j in range(n) if j != i and vsmx.can_host(prog.rows[j], b)]
        if not cand_a or not cand_b:
            continue
        # Prefer nearby hosts: a move that changes the writer/reader distance
        # much is almost always a data race.  Keep all nop hosts, then the
        # nearest ones.
        cand_a = _order_by_distance(cand_a, i, prog)[:targets_limit]
        cand_b = _order_by_distance(cand_b, i, prog)[:targets_limit]
        for j in cand_a:
            for k in cand_b:
                if j == k:
                    continue
                add = {j: a, k: b}
                rows = []
                ok = True
                for idx, r in enumerate(prog.rows):
                    if idx == i:
                        continue
                    if idx in add:
                        if not vsmx.can_host(r, add[idx]):
                            ok = False
                            break
                        rows.append(vsmx.set_instrs(r, list(r.instrs) + [add[idx]]))
                    else:
                        rows.append(r)
                if ok:
                    yield _mut(prog, rows, "dissolve",
                               f"L{i + 1}:({a.unit}->L{j + 1},{b.unit}->L{k + 1})")


def move_row(prog: Program, src_rows: set[int] | None = None) -> Iterator[Mutation]:
    """Move every expression of a row into one other row.

    A nop target turns into an instruction row while the source row vanishes,
    which is -1 word: this is "relocate the row into a free nop slot".
    """
    n = len(prog.rows)
    for i, row in enumerate(prog.rows):
        if row.nop or not row.instrs:
            continue
        if src_rows is not None and i not in src_rows:
            continue
        for j, dst in enumerate(prog.rows):
            if i == j:
                continue
            if not all(vsmx.can_host(dst, e) for e in row.instrs):
                continue
            extra = list(row.instrs)
            rows = []
            for k, r in enumerate(prog.rows):
                if k == i:
                    continue
                if k == j:
                    rows.append(vsmx.set_instrs(r, list(r.instrs) + extra))
                else:
                    rows.append(r)
            yield _mut(prog, rows, "move_row", f"L{i + 1}->L{j + 1}")


def _order_by_distance(cands: list[int], i: int, prog: Program) -> list[int]:
    nops = [j for j in cands if prog.rows[j].nop]
    rest = sorted((j for j in cands if not prog.rows[j].nop), key=lambda j: abs(j - i))
    return nops + rest


def relocate(prog: Program, stride: int = 1) -> Iterator[Mutation]:
    n = len(prog.rows)
    counter = 0
    for i, row in enumerate(prog.rows):
        for j in range(n):
            if j == i:
                continue
            counter += 1
            if stride > 1 and counter % stride:
                continue
            rows = list(prog.rows)
            r = rows.pop(i)
            rows.insert(j if j < i else j, r)
            if rows == prog.rows:
                continue
            yield _mut(prog, rows, "relocate", f"L{i + 1}->{j + 1}")


def swap(prog: Program) -> Iterator[Mutation]:
    for i in range(len(prog.rows) - 1):
        rows = list(prog.rows)
        rows[i], rows[i + 1] = rows[i + 1], rows[i]
        yield _mut(prog, rows, "swap", f"L{i + 1}<->L{i + 2}")


def reorder(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        if len(row.instrs) < 2:
            continue
        ins = list(row.instrs)
        ins.reverse()
        yield _mut(prog, _rows_with(prog, i, ins), "reorder", f"L{i + 1}")


# ------------------------------------------------------------------ commute


_MAU_RE = re.compile(r"^[dfgh][vm](fma|mul|add|passa)[ud]?r?$")
_COMMUT = {"add", "mul", "or", "and", "xor", "max", "min", "packbit"}


def _commutative_base(opcode: str) -> str | None:
    base = opcode.split("/")[0]
    if m := _MAU_RE.match(base):
        return m.group(1)
    if base.startswith("u") and len(base) > 1:
        base = base[1:]
    name = base[1:] if base[1:] in ALU_OPS else base
    return name


def commute(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        for e_idx, e in enumerate(row.instrs):
            kind = _commutative_base(e.opcode)
            if kind not in _COMMUT:
                continue
            if len(e.srcs) < 2:
                continue
            a, b = e.srcs[0], e.srcs[1]
            # A forwarding source has its own operand field; only swap two
            # memory-form sources (that is the encoding-equivalent case).
            if not (isinstance(a, Mem) and isinstance(b, Mem)):
                continue
            ins = list(row.instrs)
            ins[e_idx] = replace(e, srcs=(b, a) + tuple(e.srcs[2:]))
            yield _mut(prog, _rows_with(prog, i, ins), "commute",
                       f"L{i + 1}.{e_idx}/{e.opcode}")


# ------------------------------------------------------------------ constants


def const_equiv(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        for e_idx, e in enumerate(row.instrs):
            if not e.srcs or not isinstance(e.srcs[0], Imm):
                continue
            imm = e.srcs[0]
            for text in _imm_variants(imm):
                ins = list(row.instrs)
                ins[e_idx] = replace(e, srcs=(Imm(imm.kind, text),) + tuple(e.srcs[1:]))
                yield _mut(prog, _rows_with(prog, i, ins), "const",
                           f'L{i + 1}.{e_idx}/{imm.kind}"{imm.literal}"->"{text}"')


def _imm_variants(imm: Imm) -> Iterator[str]:
    kind, text = imm.kind, imm.literal
    if kind in ("i", "ui", "us"):
        try:
            if text.lower().startswith("0x"):
                yield str(int(text, 16))
            else:
                yield hex(int(text))
        except ValueError:
            pass
        return
    if kind in ("f", "h"):
        try:
            v = float(text)
        except ValueError:
            return
        import struct
        packed = struct.pack(">f", v)
        exact = struct.unpack(">f", packed)[0]
        variants = [f"{exact:.17g}", f"{exact:g}", f"{v:.9g}"]
        seen = {text}
        for candidate in variants:
            if candidate in seen:
                continue
            seen.add(candidate)
            try:
                if struct.pack(">f", float(candidate)) != packed:
                    continue
            except (ValueError, OverflowError):
                continue
            yield candidate


# ------------------------------------------------------------------ addressing


_LETTER = {"lm0": "m", "lm1": "n", "grf0": "r", "grf1": "s"}
_WL = {1: "", 2: "l", 4: "ll"}


def mem_text(o: Mem, style: str) -> str:
    if o.space == "t":
        return "$t" if style == "t" else "$llt"
    s = "-" if o.neg else ""
    s += "$" + _WL[o.wl] + _LETTER[o.space]
    if o.tind:
        s += "t"
    a = o.addrs
    if style == "flat" or not _uniform(a):
        s += "[" + ",".join(map(str, a)) + "]"
    else:
        d = a[1] - a[0]
        s += str(a[0])
        if d:
            s += "v" + ("" if d == o.wl else str(d))
    if o.madpe is not None:
        s += f"j{o.madpe}"
    if o.ext:
        s += "e"
    if o.rnd:
        s += "r"
    if o.mask is not None:
        s += "/" + o.mask.text()
    return s


def _uniform(a) -> bool:
    return a[1] - a[0] == a[2] - a[1] == a[3] - a[2] and a[1] - a[0] >= 0


def addr_rewrite(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        for e_idx, e in enumerate(row.instrs):
            for which, seq in (("src", e.srcs), ("dst", e.dsts)):
                for o_idx, o in enumerate(seq):
                    if not isinstance(o, Mem):
                        continue
                    if o.space == "t":
                        continue  # T-register spelling has no structured variant
                    if _uniform(o.addrs):
                        styles = ["flat", "compact"]
                    else:
                        styles = ["flat"]
                    for style in styles:
                        text = mem_text(o, style)
                        if text == o.text():
                            continue
                        new = _make_mem(o, style)
                        ins = list(row.instrs)
                        if which == "src":
                            srcs = list(e.srcs)
                            srcs[o_idx] = new
                            ins[e_idx] = replace(e, srcs=tuple(srcs))
                        else:
                            dsts = list(e.dsts)
                            dsts[o_idx] = new
                            ins[e_idx] = replace(e, dsts=tuple(dsts))
                        yield _mut(prog, _rows_with(prog, i, ins), "addr",
                                   f"L{i + 1}.{e_idx}/{which}{o_idx}:{o.text()}->{text}")


def _make_mem(o: Mem, style: str) -> Mem:
    """Return an operand whose canonical text() matches the requested style.

    For the T register canonical text is `$llt`; a `$t` spelling has no
    structured counterpart, so it is represented with `Mem(wl=4, space='t')`
    and a raw-text marker is attached by the caller... Instead we simply keep
    the same Mem: the text rewrite is done by re-parsing `mem_text(o, style)`.
    """
    from mncompile.machine import parse_operand

    return parse_operand(mem_text(o, style))


# ------------------------------------------------------------------ noforward


def noforward_move(prog: Program) -> Iterator[Mutation]:
    for i, row in enumerate(prog.rows):
        for e_idx, e in enumerate(row.instrs):
            if e.opcode.split("/")[0] != "noforward":
                continue
            for j, dst in enumerate(prog.rows):
                if j == i or dst.nop:
                    continue
                if any(x.opcode.split("/")[0] == "noforward" for x in dst.instrs):
                    continue
                rows = []
                for k, r in enumerate(prog.rows):
                    if k == i:
                        rest = row.instrs[:e_idx] + row.instrs[e_idx + 1:]
                        rows.append(vsmx.set_instrs(row, rest) if rest else vsmx.make_nop_row())
                    elif k == j:
                        rows.append(vsmx.set_instrs(r, list(r.instrs) + [e]))
                    else:
                        rows.append(r)
                yield _mut(prog, rows, "noforward", f"L{i + 1}->L{j + 1}")


# ------------------------------------------------------------------ nop


def insert_nop(prog: Program) -> Iterator[Mutation]:
    for i in range(len(prog.rows) + 1):
        rows = list(prog.rows)
        rows.insert(i, vsmx.make_nop_row())
        yield _mut(prog, rows, "insert_nop", f"@{i + 1}")


# ------------------------------------------------------------------ index

ALL_FAMILIES = {
    "delete": delete,
    "repair": repair,
    "merge": merge,
    "split": split,
    "move": move_expr,
    "move_row": move_row,
    "dissolve": dissolve,
    "relocate": relocate,
    "swap": swap,
    "reorder": reorder,
    "commute": commute,
    "const": const_equiv,
    "addr": addr_rewrite,
    "noforward": noforward_move,
    "insert_nop": insert_nop,
}


def enumerate_all(prog: Program, families: list[str] | None = None):
    for name in families or list(ALL_FAMILIES):
        fn = ALL_FAMILIES[name]
        for mut in fn(prog):
            yield mut


def random_mutation(prog: Program, rng, weights: dict[str, float] | None = None,
                    sample_cap: int = 24) -> Mutation | None:
    """Sample one mutation, preferring families that can reduce words.

    `dissolve` has up to ~50k members for a 93-row program, so only a lazy
    prefix of each family is materialised (`sample_cap`); materialising a
    whole family per sample would dominate the search cost.
    """
    import itertools
    weights = weights or {
        "move": 5, "move_row": 4, "dissolve": 4, "merge": 2, "delete": 2, "swap": 3,
        "relocate": 3, "repair": 1, "commute": 1, "addr": 1, "const": 1,
        "reorder": 1, "split": 0.5, "insert_nop": 0.3, "noforward": 0.5,
    }
    names = list(weights)
    w = [weights[n] for n in names]
    for _ in range(20):
        name = rng.choices(names, weights=w, k=1)[0]
        got = list(itertools.islice(ALL_FAMILIES[name](prog), sample_cap))
        if got:
            return rng.choice(got)
    return None
