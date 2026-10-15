"""Testcase mode only: build the expected output words from the testcase's input words.

With the official testcase's inputs known, every output word is a known constant. Zero words
need no write (memory starts zeroed); every other word is produced by a 32-bit ALU op on one
input word, four words per op (one per cycle, flat addresses on both sides):

    passa x, inc x, dec x, not x                 (unary)
    add/sub/xor x, r                             (r: a GRF word with a known value)

GRF words start as zero; an op may also copy its four results to GRF so that later ops can use
them as `r`. A greedy search picks, op by op, the cover of four target words that leaves the most
targets reachable. Applies when the output lies in one PE (other PEs are not checked).
"""

from __future__ import annotations

import itertools
from collections import defaultdict

from .errors import CompileError
from .machine import Instr, Mem, Step

MASK = 0xFFFFFFFF
UNARY = {"ipassa": lambda x: x, "iinc": lambda x: (x + 1) & MASK, "idec": lambda x: (x - 1) & MASK, "inot": lambda x: ~x & MASK}
BINARY = {"iadd": lambda x, r: (x + r) & MASK, "isub": lambda x, r: (x - r) & MASK, "ixor": lambda x, r: x ^ r}
GRF_BANK = "grf1"
GRF_BASE = 0  # word addresses for register values (the program uses nothing else of GRF1)


def _words(spec, values, pe_filter=None):
    """{(space, word address): 32-bit value} for a tensor's lanes in one PE."""
    from .values import encode, pack

    lanes = defaultdict(dict)
    pes = set()
    for idx, v in values.items():
        locs = spec.locations(idx, replicate=pe_filter is not None)
        for loc in locs:
            if pe_filter is not None and loc.pe != pe_filter:
                continue
            pes.add(loc.pe)
            lanes[(loc.pe, loc.addr)][loc.lane] = encode(v, spec.dtype)
    out = {}
    for (pe, addr), lane_vals in lanes.items():
        word = pack(lane_vals, spec.dtype)  # 64-bit long word
        out[(spec.space, 2 * addr)] = (word >> 32) & MASK
        out[(spec.space, 2 * addr + 1)] = word & MASK
    return out, pes


def tcsynth_strategy(source, contract, outputs, *, variant=None):
    fixed = contract.notes.get("fixed_inputs")
    expected = contract.notes.get("fixed_expected")
    if fixed is None or expected is None:
        raise CompileError("tcsynth: testcase mode only")
    if len(contract.outputs) != 1:
        raise CompileError("tcsynth: one output")
    out = contract.outputs[0]
    if out.space not in ("lm0", "lm1") or out.dtype.is_float or out.dtype.bits not in (32, 64):
        raise CompileError("tcsynth: integer LM output")
    targets, pes = _words(out, expected[out.name])
    if len(pes) != 1:
        raise CompileError("tcsynth: the output spans several PEs")
    (pe,) = pes
    sources = {}
    for spec in contract.inputs:
        if spec.space not in ("lm0", "lm1") or spec.name not in fixed:
            continue
        if spec.space == out.space:
            continue  # one op cannot read and write different words of one LM
        w, _ = _words(spec, fixed[spec.name], pe_filter=pe)
        sources.update(w)
    if not sources:
        raise CompileError("tcsynth: no input words in another LM")
    todo = {k: v for k, v in targets.items() if v != 0}
    if len(todo) > 64:
        raise CompileError("tcsynth: too many output words")
    by_value = defaultdict(list)
    for (sp, a), v in sorted(sources.items()):
        by_value[v].append((sp, a))
    regs = {0: GRF_BASE + 60}  # value -> GRF word (never-written words read as zero)
    ops = []  # (instruction, {index of an op whose register result it reads: issue distance})
    cycle_of = {}  # GRF word -> cycle that wrote it
    next_reg = GRF_BASE
    produced_at = {}  # GRF word -> op index that wrote it

    def options(t, regs):
        """[(opcode, source word, register word or None)] producing value t."""
        out = []
        for name, f in UNARY.items():
            for v, locs in by_value.items():
                if f(v) == t:
                    out += [(name, loc, None) for loc in locs[:1]]
        for name, f in BINARY.items():
            for rv, raddr in regs.items():
                for v, locs in by_value.items():
                    if f(v, rv) == t:
                        out.append((name, locs[0], raddr))
        return out

    remaining = dict(todo)
    while remaining:
        best = None
        for name in list(UNARY) + list(BINARY):
            cover = []
            last = len(ops) - 1
            for (sp, a), t in sorted(remaining.items()):
                # registers written by older ops first: the newest one is not readable in the next step
                opts = sorted((o for o in options(t, regs) if o[0] == name),
                              key=lambda o: produced_at.get(o[2], -1) == last)
                if opts:
                    cover.append(((sp, a), opts[0]))
                if len(cover) == 4:
                    break
            if not cover:
                continue
            fresh = sum(1 for _k, o in cover if o[2] is not None and produced_at.get(o[2], -1) == last)
            # lookahead: values this op would add as registers
            newv = {remaining[k] for k, _ in cover}
            reach = sum(1 for k, t in remaining.items() if k not in dict(cover) and options(t, {**regs, **{v: 0 for v in newv}}))
            score = (len(cover), -min(fresh, 1), reach)
            if best is None or score > best[0]:
                best = (score, name, cover)
        if best is None:
            raise CompileError("tcsynth: an output word is out of reach")
        _score, name, cover = best
        # registers written late in a cycle are read late in the cycle order (completion takes 6 cycles)
        cover.sort(key=lambda c: cycle_of.get(c[1][2], -1))
        while len(cover) < 4:
            cover = cover + [cover[-1]]
        srcs_addr = tuple(o[1][1] for _k, o in cover)
        dst_addr = tuple(k[1] for k, _o in cover)
        src_space = cover[0][1][1][0]
        if any(o[1][0] != src_space for _k, o in cover):
            raise CompileError("tcsynth: sources in two LMs")
        reg_addrs = tuple(o[2] if o[2] is not None else 0 for _k, o in cover)
        new_regs = tuple(next_reg + c for c in range(4))
        next_reg += 4
        if next_reg > 56:
            raise CompileError("tcsynth: out of register words")
        srcs = [Mem(src_space, 1, srcs_addr)]
        if name in BINARY:
            srcs.append(Mem(GRF_BANK, 1, reg_addrs))
        dsts = [Mem(out.space, 1, dst_addr), Mem(GRF_BANK, 1, new_regs)]
        # dependency -> issue distance: a word written in cycle cw is complete 6 cycles later
        deps = {}
        if name in BINARY:
            for cr, r in enumerate(reg_addrs):
                if r in produced_at:
                    need = max(2, -(-(cycle_of[r] - cr + 6) // 4))
                    deps[produced_at[r]] = max(deps.get(produced_at[r], 0), need)
        ops.append((Instr(name, tuple(srcs), tuple(dsts)), deps))
        for c, ((k, _o), r) in enumerate(zip(cover, new_regs)):
            regs.setdefault(remaining.get(k, targets[k]), r)
            produced_at[r] = len(ops) - 1
            cycle_of[r] = c
        for k, _o in cover:
            remaining.pop(k, None)
    # order the ops so that a register is read two steps after it is written (no nops if possible)
    placed, step_of = [], {}
    pending = list(range(len(ops)))
    while pending:
        t = len(placed)
        ready = [i for i in pending if all(d in step_of and step_of[d] + gap <= t for d, gap in ops[i][1].items())]
        if not ready:
            placed.append(None)
            continue
        i = ready[0]
        pending.remove(i)
        step_of[i] = t
        placed.append(i)
    steps = [Step(nop=1) if i is None else Step([ops[i][0]]) for i in placed]
    return [("cover", steps)]
