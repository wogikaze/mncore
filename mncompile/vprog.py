"""Virtual programs: machine expressions over SSA vector values.

A `Value` is a per-PE vector: for each of the four cycles of a step, `width`
words (1 word, 2 = one long word, 4 = two long words). A `VOp` is one machine
expression whose register operands are values; the scheduler decides the
issue step of every op and where each value lives (a forwarding register,
GRF0, GRF1 or T), then emits concrete `Instr`s.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field

from .machine import Fixed, Fwd, Imm, Instr, L1, L2, Mask, Mem, NoWrite, Omr

_ids = itertools.count()


@dataclass(eq=False)
class Value:
    width: int  # words per cycle on the bus that matter (1, 2 or 4)
    name: str = ""
    id: int = field(default_factory=lambda: next(_ids))
    # fixed home (e.g. a constant that must live at a given place); None = allocate
    home: Mem | None = None
    # the bus written by the producer carries this many words per cycle that a reader may use
    def __repr__(self):
        return f"v{self.id}{':' + self.name if self.name else ''}"


@dataclass(frozen=True)
class Use:
    """A read of a value with MAU/ALU input modifiers."""

    value: Value
    neg: bool = False
    ext: bool = False
    rnd: bool = False
    wl: int | None = None  # access width override (e.g. read a long-word value as words)
    cycle: int | None = None  # read the value's slot of this cycle in every cycle (needs storage)
    word: int = 0  # word offset inside the slot (for word-width reads of lanes)


@dataclass(frozen=True)
class FlagUse:
    """Masked write controlled by a mask register entry holding a flag value."""

    flags: "Value"
    ll: bool = False


@dataclass(eq=False)
class VOp:
    opcode: str
    srcs: list  # Use | Mem | Fixed | Imm | Fwd(raw) | L1 | L2 ...
    out: Value | None = None  # SSA result (allocated by the scheduler)
    dsts: list = field(default_factory=list)  # fixed destinations (Mem, Omr, L1, ...)
    flags_out: Value | None = None  # value representing mask flags written to an omr entry
    write_mask: FlagUse | Mask | None = None  # masked write of `out`/dsts
    flush: FlagUse | Mask | None = None
    unit: str = "alu"
    # values that must be complete before this op (ordering only, e.g. masked-merge base)
    after: list = field(default_factory=list)
    # read of the value this op merges into (masked write keeps the old contents)
    merge_into: Value | None = None
    note: str = ""
    id: int = field(default_factory=lambda: next(_ids))
    # (opcode, unit) the op may issue as instead when its own unit is taken (same result bits)
    alt: tuple | None = None

    def uses(self):
        out = [s.value for s in self.srcs if isinstance(s, Use)]
        if isinstance(self.write_mask, FlagUse):
            out.append(self.write_mask.flags)
        if isinstance(self.flush, FlagUse):
            out.append(self.flush.flags)
        if self.merge_into is not None:
            out.append(self.merge_into)
        return out

    def __repr__(self):
        return f"{self.opcode}({', '.join(map(repr, self.srcs))}) -> {self.out}{self.dsts}"


@dataclass
class VProgram:
    ops: list = field(default_factory=list)
    # values whose final location is fixed by an output Mem (written via dsts)
    notes: dict = field(default_factory=dict)

    def add(self, op: VOp) -> VOp:
        self.ops.append(op)
        return op

    def value(self, width, name=""):
        return Value(width, name)


def forward_stores(prog: VProgram, temps) -> int:
    """Store-to-load forwarding for temporaries: an op whose only destination is a temporary
    Mem that a later plain copy reads back exactly gives its result as a value instead (the
    copy and the memory round trip disappear). Returns the number of forwarded temporaries."""
    temps = set(temps)
    writer, readers = {}, {}
    for op in prog.ops:
        for d in op.dsts:
            if isinstance(d, Mem) and d in temps:
                writer.setdefault(d, []).append(op)
        for s in op.srcs:
            if isinstance(s, Mem) and s in temps:
                readers.setdefault(s, []).append(op)
    replace_by = {}
    dead = set()
    for m, ws in writer.items():
        rs = readers.get(m, [])
        if len(ws) != 1 or len(rs) != 1:
            continue
        a, b = ws[0], rs[0]
        if a.dsts != [m] or a.write_mask is not None or a.flush is not None or a.merge_into is not None:
            continue
        if b.opcode != "lpassa" or b.srcs != [m] or b.out is None or b.dsts or b.write_mask is not None or b.flush is not None:
            continue
        if prog.ops.index(a) > prog.ops.index(b):
            continue
        src = a.srcs[0] if len(a.srcs) == 1 else None
        if a.opcode == "lpassa" and isinstance(src, Use) and src == Use(src.value) and a.out is None:
            replace_by[b.out.id] = src.value  # a plain copy: read its source directly
            dead.add(a.id)
        else:
            if a.out is None:
                a.out = Value(b.out.width)
            a.dsts = []
            replace_by[b.out.id] = a.out
        dead.add(b.id)
    if not replace_by:
        return 0

    def sub(v):
        while v is not None and v.id in replace_by:
            v = replace_by[v.id]
        return v

    from dataclasses import replace as dc_replace

    ops = []
    for op in prog.ops:
        if op.id in dead:
            continue
        op.srcs = [dc_replace(s, value=sub(s.value)) if isinstance(s, Use) else s for s in op.srcs]
        if isinstance(op.write_mask, FlagUse):
            op.write_mask = dc_replace(op.write_mask, flags=sub(op.write_mask.flags))
        if op.merge_into is not None:
            op.merge_into = sub(op.merge_into)
        op.after = [sub(v) for v in op.after]
        ops.append(op)
    prog.ops = ops
    return len(replace_by)
