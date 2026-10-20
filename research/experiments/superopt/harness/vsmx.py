"""Row-level model of a VSM program for superoptimization.

A program is a list of `Row`s.  A row keeps both its original text and its
structured expressions (`mncompile.machine.Instr`).  Rows that were never
touched re-emit byte-for-byte; touched rows are re-emitted canonically (the
canonical form is itself verified end-to-end by the scorer).

Only PE/MV statements are handled; the baseline has no comments or debug
statements.  `machine.parse_expr` is the single source of truth for operand
grammar, and `machine.unit_of` for the issue unit of an expression.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from mncompile.machine import Instr, Mem, parse_expr, unit_of

# ---------------------------------------------------------------- unit classes

# Units that consume a whole issue line on their own (MV transfers and the
# L1BM/L2BM address generators are issued on their own pipeline in the
# baseline; see docs/fizzbuzz-notes/06-unit-budget.md).
SOLO_UNITS = {"mv"}


def units(instrs: list[Instr]) -> list[str]:
    return [i.unit for i in instrs]


# ---------------------------------------------------------------- row / program


@dataclass
class Row:
    instrs: list[Instr]
    nop: int = 0
    raw: str | None = None  # original text; None => canonical re-emit

    def text(self) -> str:
        if self.raw is not None:
            return self.raw
        if self.nop:
            return "nop" if self.nop == 1 else f"nop/{self.nop}"
        return "; ".join(i.text() for i in self.instrs)

    def unit_list(self) -> list[str]:
        return ["nop"] if self.nop else units(self.instrs)

    def touches_imm(self) -> bool:
        return any(i.opcode.split("/")[0] == "imm" for i in self.instrs)

    def has_unit(self, unit: str) -> bool:
        return unit in self.unit_list()

    def n_alu(self) -> int:
        return sum(1 for u in self.unit_list() if u == "alu")

    def n_mau(self) -> int:
        return sum(1 for u in self.unit_list() if u == "mau")


@dataclass
class Program:
    rows: list[Row]
    # chain is a human-readable transformation history (latest last)
    chain: tuple[str, ...] = ()

    def text(self) -> str:
        return "".join(r.text() + "\n" for r in self.rows)

    def words(self) -> int:
        """Assembled word count as fbcheck counts it (nop/n counts n)."""
        return sum(r.nop if r.nop else 1 for r in self.rows)

    def digest(self) -> str:
        return hashlib.sha256(self.text().encode()).hexdigest()

    def clone(self, rows: list[Row] | None = None, chain_add: str | None = None) -> "Program":
        c = Program(
            rows=list(rows if rows is not None else self.rows),
            chain=self.chain,
        )
        if chain_add is not None:
            c.chain = self.chain + (chain_add,)
        return c


def parse(text: str) -> Program:
    rows: list[Row] = []
    for raw in text.splitlines():
        line = raw.split("#")[0].strip()
        if not line:
            continue
        exprs = [e.strip() for e in line.split(";") if e.strip()]
        if len(exprs) == 1 and exprs[0] == "nop":
            rows.append(Row([], nop=1, raw=line))
            continue
        if len(exprs) == 1 and exprs[0].startswith("nop/"):
            rows.append(Row([], nop=int(exprs[0].split("/")[1]), raw=line))
            continue
        rows.append(Row([parse_expr(e) for e in exprs], nop=0, raw=line))
    return Program(rows)


# ---------------------------------------------------------------- issue filters


def can_host(row: Row, instr: Instr) -> bool:
    """Conservative pre-filter for 'this expression may join this row'.

    It encodes only the rules we are confident of (SDM 3.6.4 as summarised in
    docs/shortening_techniques.md).  The simulator's own `issue::check` and the
    official assembler are the real gates; this filter only avoids wasting
    evaluations on obviously impossible pairs.
    """
    if row.nop:
        return True
    u = instr.unit
    if u == "mv":
        return False  # MV must be alone; use a nop slot
    if any(i.unit == "mv" for i in row.instrs):
        return False
    cur = row.unit_list()
    if u == "alu":
        # One ALU expression per line (66 ALU rows, 93 lines in the baseline).
        if "alu" in cur:
            return False
        return True
    if u == "mau":
        # At most two MAU groups, and the baseline never issues two MAU
        # expressions in one line; allow it (different groups) and let the
        # simulator reject what is illegal.
        if cur.count("mau") >= 2:
            return False
        return True
    if u in ("mwrite", "mread"):
        return "mwrite" not in cur and "mread" not in cur
    if u in ("l1bm", "l1bm-turnaround", "l2bm"):
        return True
    if u == "noforward":
        return "noforward" not in cur
    return True


# ---------------------------------------------------------------- row editing


def set_instrs(row: Row, instrs: list[Instr]) -> Row:
    return Row(list(instrs), nop=0, raw=None)


def make_nop_row(n: int = 1) -> Row:
    return Row([], nop=n, raw=None)


def drop_row(rows: list[Row], i: int) -> list[Row]:
    return rows[:i] + rows[i + 1:]


# ---------------------------------------------------------------- def / use

REG_FIXED = {"l2bid", "l1bid", "mabid", "peid", "subpeid", "msb1"}


def operand_regs(instr: Instr) -> set[str]:
    """Register names mentioned by an expression (textual, per cycle)."""
    from mncompile.machine import Bar, Dar, Fixed, Fwd, L1, L2, Mat, Omr, Pdm, Dram

    out: set[str] = set()
    for o in instr.srcs + instr.dsts:
        if isinstance(o, Mem):
            out.add(o.text())
        elif isinstance(o, Fwd):
            out.add(o.text())
        elif isinstance(o, Fixed):
            out.add("$" + o.name)
        elif isinstance(o, Omr):
            out.add(f"$omr{o.entry}")
        elif isinstance(o, (Bar, L1, L2, Mat, Dar, Pdm, Dram)):
            out.add(o.text())
    return out


def defs(instr: Instr) -> set[str]:
    """Names written by an expression (textual operand forms)."""
    out: set[str] = set()
    for o in instr.dsts:
        if isinstance(o, Mem) or type(o).__name__ in ("Omr", "Bar"):
            out.add(o.text())
    return out


def uses(instr: Instr) -> set[str]:
    out: set[str] = set()
    for o in instr.srcs:
        out.add(o.text())
    return out


# ---------------------------------------------------------------- misc helpers


def commutative(instr: Instr) -> bool:
    base = instr.opcode.split("/")[0]
    if base.startswith("u") and len(base) > 1:
        base = base[1:]
    # Integer/float add, multiply, and bitwise ops are commutative at the
    # operand level; subtract/shift/fma are not.
    return base in {
        "iadd", "fadd", "fvadd", "mvadd", "hvadd",
        "fvmul", "fadd", "imul", "fmul",
        "ior", "iand", "ixor",
        "ladd", "land", "lor",
    }


def imm_rows(prog: Program):
    for i, row in enumerate(prog.rows):
        for j, ins in enumerate(row.instrs):
            if ins.opcode.split("/")[0] == "imm":
                yield i, j, ins


def is_nop(prog: Program, i: int) -> bool:
    return prog.rows[i].nop > 0


__all__ = [
    "Program", "Row", "parse", "can_host", "set_instrs", "make_nop_row",
    "drop_row", "defs", "uses", "commutative", "imm_rows", "is_nop",
    "units", "unit_of",
]
