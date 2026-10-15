"""Gathers: outputs that select an element of a stored table by a stored index.

Y = table[index] where the table is a run of long words in the output's PE and
the index is an input element in that PE. The index (scaled to words) is put in
the T register, and the table is read with T-indirect LM0 addressing.
"""

from __future__ import annotations

from .errors import CompileError
from .layout import Contract
from .machine import Mask, Mem
from .vprog import VOp, VProgram


def gather_strategy(source, contract: Contract, outputs: dict, *, variant=None):
    if len(contract.outputs) != 1:
        raise CompileError("gather: one output")
    out = contract.outputs[0]
    specs = {s.name: s for s in contract.inputs}
    if out.dtype.bits != 64:
        raise CompileError("gather: 64-bit elements only")
    items = []
    for idx, node in outputs[out.name].items():
        if node.op != "gather" or node.args[0].op != "input":
            raise CompileError("gather: output is not a table lookup by an input index")
        ix, table = node.args[0], node.args[1:]
        if any(t.op != "input" for t in table):
            raise CompileError("gather: table entries must be inputs")
        oloc = out.locations(idx, replicate=False)[0]
        ispec = specs[ix.value[0]]
        if ispec.space not in ("lm0", "lm1") or ispec.dtype.bits != 64:
            raise CompileError("gather: index must be a 64-bit LM value")
        iloc = [l for l in ispec.locations(ix.value[1], replicate=True) if l.pe == oloc.pe]
        if not iloc:
            raise CompileError("gather: index not in the output's PE")
        tspec = specs[table[0].value[0]]
        if tspec.space != "lm0" or any(specs[t.value[0]] is not tspec for t in table):
            raise CompileError("gather: table must be one LM0 tensor")
        addrs = []
        for t in table:
            l = [l for l in tspec.locations(t.value[1], replicate=True) if l.pe == oloc.pe]
            if not l:
                raise CompileError("gather: table not in the output's PE")
            addrs.append(l[0].addr)
        base = addrs[0]
        if addrs != list(range(base, base + len(addrs))):
            raise CompileError("gather: table is not contiguous")
        lo, hi = ispec.low, ispec.high
        if lo is None or lo < 0 or hi is None or hi >= len(table):
            raise CompileError("gather: index range exceeds the table")
        items.append((oloc, iloc[0], base, ispec.space))
    # SPMD: one representative PE; all PEs must use the same local addresses
    rep = min(i[0].pe for i in items)
    local = sorted((o.addr, il.addr, b, sp) for o, il, b, sp in items if o.pe == rep)
    for pe in {i[0].pe for i in items}:
        other = sorted((o.addr, il.addr, b, sp) for o, il, b, sp in items if o.pe == pe)
        if other != local:
            raise CompileError("gather: PEs use different addresses")
    prog = VProgram()
    for g in range(0, len(local), 4):
        chunk = local[g:g + 4]
        live = len(chunk)
        while len(chunk) < 4:
            chunk.append(chunk[-1])
        ispace = chunk[0][3]
        imem = Mem(ispace, 2, tuple(c[1] * 2 for c in chunk))
        prog.add(VOp("ladd", [imem, imem], dsts=[Mem("t", 4)], unit="alu"))
        mask = None if live == 4 else Mask(pattern="1" * live + "0" * (4 - live))
        src = Mem("lm0", 2, tuple(c[2] * 2 for c in chunk), tind=True)
        prog.add(VOp("lpassa", [src], dsts=[Mem(out.space, 2, tuple(c[0] * 2 for c in chunk), mask=mask)], unit="alu"))
    return prog
