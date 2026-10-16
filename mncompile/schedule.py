"""Step scheduling, forwarding and register-bank assignment for virtual programs.

The scheduler fills steps in order. An op is placed in the earliest step where
its unit is free, every operand can be read (from the producing unit's
forwarding register when the producer issued in the previous non-nop step,
otherwise from GRF0/GRF1 at least two steps after the write), and the step's
read and write ports stay consistent (one address pattern per memory per step,
one writer per memory). Storage for a value is chosen lazily, when a consumer
first needs it, and added as an extra destination of the producer.

The official assembler is the final authority: rejected programs are repaired
by splitting the offending step, and nops are removed only when the assembler
accepts the result.
"""

from __future__ import annotations

import random
import re
from collections import defaultdict
from dataclasses import dataclass, field, replace

from .errors import CompileError
from .machine import Dram, Fixed, Fwd, Imm, Instr, L1, L2, Mask, Mem, NoWrite, Omr, Pdm, Step, emit, unit_of
from .vprog import FlagUse, Use, Value, VOp, VProgram

FWD_OF_UNIT = {"alu": "aluf", "mau": "mauf", "l1bm": "lbf", "l1bm-turnaround": "lbf", "mread": "mreadf"}
GRF = ("grf0", "grf1")
GRF_WORDS = 512
RESERVED_TOP = 64  # top of each GRF kept for constants


EAGER_COPIES = True

# --------------------------------------------------------------------------- transfer instructions
# L1BM / L2BM / MV instructions scheduled with the computation. Issue distances between transfers
# that touch the same buffer (SDM 3.6.3; the conservative step counts, so every address works):
#   data:  PE->L1BM => L1BM->L2BM/multicast 4, L2BM->L1BM => L1BM->PE 3, multicast => L1BM->PE 4,
#          L1BM->L2BM => MV reading L2BM 4
#   port:  L1BM->L2BM => L2BM->L1BM 4, PE->L1BM => L1BM->PE 3, L2BM->L1BM => L1BM->L2BM/multicast 3,
#          multicast => L1BM->L2BM/multicast 4
_BUFFERS = (L1, L2, Pdm, Dram)
_DATA_GAP = {("p2b", "b2c"): 4, ("p2b", "mc"): 4, ("c2b", "b2p"): 3, ("mc", "b2p"): 4, ("b2c", "mv"): 4}
_PORT_GAP = {("b2c", "c2b"): 4, ("p2b", "b2p"): 3, ("c2b", "b2c"): 3, ("c2b", "mc"): 3, ("mc", "b2c"): 4, ("mc", "mc"): 4}


def transfer_kind(op) -> str | None:
    """Direction of a transfer op: p2b (PE->L1BM), b2p (L1BM->PE), b2c (L1BM->L2BM), c2b (L2BM->L1BM),
    mc (L1BM->L1BM multicast), mv (MV statement); None for PE computation."""
    name = op.opcode.split("/")[0]
    srcs = [x for x in op.srcs if isinstance(x, _BUFFERS)]
    dsts = [x for x in op.dsts if isinstance(x, _BUFFERS)]
    if name.startswith("mv"):
        return "mv"
    if not (name.startswith("l1bm") or name.startswith("l2bm")):
        return None
    s = type(srcs[0]) if srcs else None
    d = type(dsts[0]) if dsts else None
    if s is None and d is L1:
        return "p2b"
    if s is L1 and d is None:
        return "b2p"
    if s is L1 and d is L2:
        return "b2c"
    if s is L2 and d is L1:
        return "c2b"
    if s is L1 and d is L1:
        return "mc"
    return "other"


def transfer_unit(instr) -> str:
    name = instr.opcode.split("/")[0]
    if name.startswith("mv"):
        return "mv"
    if name.startswith("l1bm") and any(isinstance(x, L1) and x.addr is None for x in instr.srcs):
        return "l1bm-turnaround"
    return unit_of(instr.opcode)


def hop_ops(hops) -> list:
    """VOps for the instructions of a transfer chain (in order); the scheduler interleaves them with
    the computation under the issue distances above."""
    ops = []
    for hop in hops:
        for ins in hop:
            ops.append(VOp(ins.opcode, list(ins.srcs), dsts=list(ins.dsts), unit=transfer_unit(ins),
                           flush=ins.flush, note="transfer"))
    return ops


def with_hops(prog: VProgram, hops) -> VProgram:
    """A copy of prog followed by the transfer chain as schedulable ops."""
    return VProgram(list(prog.ops) + hop_ops(hops), dict(prog.notes))


def op_unit(op: VOp) -> str:
    return op.unit or unit_of(op.opcode)


@dataclass
class Slot:
    units: dict = field(default_factory=dict)
    reads: dict = field(default_factory=dict)  # memory -> pattern
    writes: dict = field(default_factory=dict)  # memory -> op id
    mask_read: tuple | None = None
    flush_used: bool = False
    imm: bool = False
    lm0_access: bool = False
    write_pat: dict = field(default_factory=dict)  # LM space -> pattern written in this step

    @property
    def empty(self):
        return not self.units


def _pattern(mem: Mem):
    if mem.space == "t":
        return ("t",)
    return tuple((a, mem.wl, mem.tind, mem.madpe) for a in mem.addrs)


def _overlap(a: Mem, b: Mem) -> bool:
    if a.space == "t" or b.space == "t":
        return True
    if (a.tind and a.trange is None) or (b.tind and b.trange is None):
        return True  # T-indirect addresses are only known at run time

    def words(m):
        return set(range(*m.trange)) if m.tind else {w for c in range(4) for w in m.words(c)}

    return bool(words(a) & words(b))


def storage_mem(stored, wl=None, neg=False, ext=False, rnd=False, mask=None, cycle=None, word=0):
    bank, base, width = stored[:3]
    stride = stored[3] if len(stored) > 3 else width
    wl = min(wl or width, width) if bank != "t" else 4
    if bank == "t":
        return Mem("t", 4, (0, 0, 0, 0), neg=neg, ext=ext, rnd=rnd, mask=mask)
    if cycle is not None:
        return Mem(bank, wl, (base + stride * cycle + word,) * 4, neg=neg, ext=ext, rnd=rnd, mask=mask)
    return Mem(bank, wl, tuple(base + stride * c + word for c in range(4)), neg=neg, ext=ext, rnd=rnd, mask=mask)


class Scheduler:
    def __init__(self, prog: VProgram, *, seed: int = 0, jitter: float = 0.0, pressure: bool = True):
        # private copies: deadlock breaking rewrites operands
        prog = VProgram([replace(op, srcs=list(op.srcs), dsts=list(op.dsts), after=list(op.after)) for op in prog.ops], dict(prog.notes))
        self.prog = prog
        self.pressure = pressure
        self.rng = random.Random(seed)
        self.jitter = jitter
        self.slots: list[Slot] = []
        self.step_of: dict[int, int] = {}
        self.def_op: dict[int, VOp] = {}
        self.flag_op: dict[int, VOp] = {}
        self.storage: dict[int, tuple] = {}
        self.extra_dsts: dict[int, list] = {}
        self.fwd_use: dict[tuple, str] = {}
        self.use_storage: dict[tuple, tuple] = {}
        self.omr_entry: dict[int, int] = {}
        self.next_entry = 1
        self.free_entries: list[int] = []  # (entry) free from a step onward
        self.entry_free_at: dict[int, int] = {}
        reserved = prog.notes.get("grf_reserved", {})  # words at the bottom of each GRF used by fixed buffers
        self.next_addr = {b: reserved.get(b, 0) for b in GRF}
        self.free_ranges = {"grf0": [], "grf1": []}  # (base, width, free_from_step)
        self.consumers = defaultdict(list)
        for op in prog.ops:
            if op.out is not None:
                self.def_op[op.out.id] = op
                if op.out.home is not None:
                    h = op.out.home
                    stride = h.addrs[1] - h.addrs[0]
                    self.storage[op.out.id] = (h.space, h.addrs[0], op.out.width, stride) if h.space != "t" else ("t", 0, 4, 0)
            if op.flags_out is not None:
                self.flag_op[op.flags_out.id] = op
            for x in op.srcs:
                if isinstance(x, Use) and getattr(x.value, "preset", False):
                    h = x.value.home
                    self.storage[x.value.id] = (h.space, h.addrs[0], x.value.width, h.addrs[1] - h.addrs[0])
        self._mem_deps = self._fixed_dependencies()
        self.height = self._heights()
        self.uses_left = {}
        for op in prog.ops:
            for v in op.uses():
                self.uses_left[v.id] = self.uses_left.get(v.id, 0) + 1
                if op not in self.consumers[v.id]:
                    self.consumers[v.id].append(op)
        self.last_use = {}
        self.t_owner = None  # value id held in T
        # programs that address LM0 through T (or write T themselves) never use T as value storage
        self.t_reserved = any(isinstance(x, Mem) and (x.tind or x.space == "t") for op in prog.ops for x in list(op.srcs) + list(op.dsts))
        self.unsticks = 0
        self._flag_order = [op for op in self.prog.ops if op.flags_out is not None]
        # how often each GRF is read through fixed operands (values prefer the quieter bank)
        self._bank_load = {b: 0 for b in GRF}
        for op in self.prog.ops:
            for x in op.srcs:
                if isinstance(x, Mem) and x.space in self._bank_load:
                    self._bank_load[x.space] += 1
        self.color = self._bank_colors()
        self._merge_bases = {op.merge_into.id for op in prog.ops if op.merge_into is not None}
        self._eager_done = set()
        self.eager_copies = True
        self.l1copy = {}  # op id -> (up step, op): copies routed through the L1BM turnaround register
        self.use_l1copy = True
        self.relax = not pressure  # allow results that cannot get storage (deadlock fallback)
        self.t_fixed_steps = set()

    # ------------------------------------------------------------ analysis
    def _fixed_dependencies(self):
        deps = {op.id: [] for op in self.prog.ops}
        self._dst_deps = {op.id: [] for op in self.prog.ops}  # the part due to the op's own writes
        written, read = [], []
        transfers = []  # (op, kind, buffer types read, buffer types written)
        for op in self.prog.ops:
            srcs = [s for s in op.srcs if isinstance(s, Mem)]
            srcs += [Mem("t", 4) for s in list(op.srcs) + list(op.dsts) if isinstance(s, Mem) and s.tind]
            dsts = [d for d in op.dsts if isinstance(d, Mem)]
            for prev, mem in written:
                for s in srcs:
                    if s.space == mem.space and _overlap(s, mem):
                        deps[op.id].append((prev, 3 if mem.space in ("lm0", "lm1") else 2))
                for d in dsts:
                    if d.space == mem.space and _overlap(d, mem):
                        deps[op.id].append((prev, 1))
                        self._dst_deps[op.id].append((prev, 1))
            for prev, mem in read:
                for d in dsts:
                    if d.space == mem.space and _overlap(d, mem):
                        deps[op.id].append((prev, 0))
                        self._dst_deps[op.id].append((prev, 0))
            kind = transfer_kind(op)
            if kind is not None:
                bufs_r = {type(x) for x in op.srcs if isinstance(x, _BUFFERS)}
                bufs_w = {type(x) for x in op.dsts if isinstance(x, _BUFFERS)}
                if kind == "mv":
                    bufs_r, bufs_w = bufs_r | {L2, Pdm, Dram}, bufs_w | {L2, Pdm, Dram}
                for prev, pkind, pr, pw in transfers:
                    gap = 1 if (pw & (bufs_r | bufs_w)) or (pr & bufs_w) else 0
                    if pw & bufs_r:
                        gap = max(gap, _DATA_GAP.get((pkind, kind), 1))
                    gap = max(gap, _PORT_GAP.get((pkind, kind), 0))
                    if pkind == "mv" or kind == "mv":
                        gap = max(gap, 1)  # MV statements keep their program order
                    if gap:
                        deps[op.id].append((prev, gap))
                transfers.append((op, kind, bufs_r, bufs_w))
            written += [(op, d) for d in dsts]
            read += [(op, s) for s in srcs]
            for v in op.after:
                p = self.def_op.get(v.id) or self.flag_op.get(v.id)
                if p is not None:
                    deps[op.id].append((p, 1))
            if op.merge_into is not None:
                p = self.def_op.get(op.merge_into.id)
                if p is not None:
                    deps[op.id].append((p, 1))
        return deps

    def _preds(self, op):
        out = []
        for v in op.uses():
            p = self.def_op.get(v.id) or self.flag_op.get(v.id)
            if p is not None:
                out.append(p)
        out += [p for p, _ in self._mem_deps[op.id]]
        return out

    def _heights(self):
        succ = {op.id: [] for op in self.prog.ops}
        for op in self.prog.ops:
            for p in self._preds(op):
                succ[p.id].append(op)
        height = {}
        for op in reversed(self.prog.ops):
            height[op.id] = 1 + max((height[s.id] for s in succ[op.id]), default=0)
        return height

    # ------------------------------------------------------------ helpers
    def _slot(self, t):
        while len(self.slots) <= t:
            self.slots.append(Slot())
        return self.slots[t]

    def _prev_nonnop(self, t):
        k = t - 1
        while k >= 0 and self.slots[k].empty:
            k -= 1
        return k

    def _lm_blocked(self, space, t):
        return any(0 <= k < len(self.slots) and space in self.slots[k].writes for k in (t - 1, t - 2))

    def _read_ok(self, slot, mem, pending):
        have = pending.get(mem.space, slot.reads.get(mem.space))
        if mem.space in ("lm0", "lm1"):
            # an LM read and write in one step must cover the same words (SDM 3.6.4)
            wp = slot.write_pat.get(mem.space)
            if wp is not None and wp != _pattern(replace(mem, mask=None, neg=False, ext=False, rnd=False)):
                return False
        return have is None or have == _pattern(mem)

    def _alloc(self, bank, width, pending, at_step=None):
        if at_step is not None:
            taken = {(s[1]) for s in pending.values() if s[0] == bank}
            for k, (base, w, free_from) in enumerate(self.free_ranges[bank]):
                if w == width and free_from <= at_step and base not in taken:
                    return base
        start = self.next_addr[bank]
        for s in pending.values():
            if s[0] == bank:
                start = max(start, s[1] + 4 * s[2])
        align = 4 if width >= 2 else 1
        start = (start + align - 1) // align * align
        if start + 4 * width > GRF_WORDS - RESERVED_TOP:
            return None
        return start

    def _new_storage(self, v, p, d, slot, src, pending_reads, new_storage):
        pslot = self.slots[d]
        banks = self._bank_preference(v)
        if self.jitter and self.rng.random() < 0.3:
            self.rng.shuffle(banks)
        for bank in banks + ["t"]:
            if bank == "t":
                if self.t_reserved or (src is not None and (src.cycle is not None or src.word)) or v.width > 4 or "t" in pslot.writes or any(isinstance(dd, Mem) and dd.space == "t" for dd in p.dsts):
                    continue
                owner = self.t_owner
                if owner is not None and (self.uses_left.get(owner, 0) > 0 or self.last_use.get(owner, -1) >= d):
                    continue
                if any(k >= d for k in self.t_fixed_steps):
                    continue
                stored = ("t", 0, 4, 0)
                if src is None or self._read_ok(slot, self._mem_for(stored, src), pending_reads):
                    return stored
                continue
            if bank in pslot.writes:
                continue
            if any(isinstance(dd, Mem) and dd.space == bank for dd in p.dsts):
                continue
            if any(s[0] == bank and self.def_op.get(vid) is p for vid, s in new_storage.items()):
                continue
            base = self._alloc(bank, v.width, new_storage, at_step=d)
            if base is None:
                continue
            stored = (bank, base, v.width)
            if src is None or self._read_ok(slot, self._mem_for(stored, src), pending_reads):
                return stored
        return None

    def _mem_for(self, stored, src: Use):
        return storage_mem(stored, src.wl, src.neg, src.ext, src.rnd, cycle=src.cycle, word=src.word)

    # ------------------------------------------------------------ placement
    def _try(self, op: VOp, t: int, land: int | None = None):
        """Plan op at step t; with `land`, the dependencies of its writes count from that step
        (an L1BM turnaround copy reads at t and writes one step later)."""
        unit = op_unit(op)
        slot = self._slot(t)
        if unit in slot.units:
            return None
        if (unit == "mv" and slot.units) or "mv" in slot.units:
            return None  # an MV statement is a line of its own
        if unit in ("mau", "mwrite", "mread") and sum(u in ("mau", "mwrite", "mread") for u in slot.units) >= 2:
            return None
        prev = self._prev_nonnop(t)
        pending_reads: dict = {}
        plan_fwd, plan_storage, new_storage = {}, {}, {}
        is_imm = op.opcode.startswith("imm")
        touches_lm0 = False
        if land is None:
            for p, dist in self._mem_deps[op.id]:
                if p.id not in self.step_of or self.step_of[p.id] + dist > t:
                    return None
        else:
            dst_deps = list(self._dst_deps.get(op.id, []))
            rest = list(self._mem_deps[op.id])
            for d in dst_deps:
                rest.remove(d)
            for deps_, at in ((rest, t), (dst_deps, land)):
                for p, dist in deps_:
                    if p.id not in self.step_of or self.step_of[p.id] + dist > at:
                        return None
        mask_read = slot.mask_read
        for fu in (op.write_mask, op.flush):
            if isinstance(fu, FlagUse):
                p = self.flag_op.get(fu.flags.id)
                if p is None or p.id not in self.step_of or self.step_of[p.id] >= t:
                    return None
                key = (self.omr_entry[fu.flags.id], fu.ll)
                if mask_read is not None and mask_read != key:
                    return None
                mask_read = key
        for d in op.dsts:
            # a fixed cycle pattern ("/1000") is a one-time mask: it takes the step's mask read too
            if isinstance(d, Mem) and d.mask is not None:
                key = ("pattern", d.mask.pattern, d.mask.ll) if d.mask.pattern is not None else (d.mask.entry, d.mask.ll)
                if mask_read is not None and mask_read != key:
                    return None
                mask_read = key
        if op.flush is not None and slot.flush_used:
            return None
        for i, src in enumerate(op.srcs):
            if isinstance(src, Use):
                v = src.value
                p = self.def_op.get(v.id)
                if p is None and getattr(v, "preset", False):
                    # present from the start at its home (e.g. never-written zero words)
                    mem = self._mem_for(self.storage[v.id], src)
                    if not self._read_ok(slot, mem, pending_reads):
                        return None
                    pending_reads[mem.space] = _pattern(mem)
                    plan_storage[i] = self.storage[v.id]
                    continue
                if p is None:
                    raise CompileError(f"value {v} has no producer")
                if p.id not in self.step_of or self.step_of[p.id] >= t:
                    return None
                d = self.step_of[p.id]
                kind = FWD_OF_UNIT.get(op_unit(p))
                can_fwd = (
                    src.cycle is None and src.word == 0
                    and not getattr(v, "nofwd", False)
                    and kind is not None
                    and d == prev
                    and (kind != "mreadf" or (unit == "alu" and i == 0))
                )
                stored = self.storage.get(v.id) or new_storage.get(v.id)
                if stored and t - d >= 2 and self._read_ok(slot, self._mem_for(stored, src), pending_reads):
                    if can_fwd and stored[0] != "t":
                        plan_fwd[i] = kind
                        continue
                    mem = self._mem_for(stored, src)
                    pending_reads[mem.space] = _pattern(mem)
                    plan_storage[i] = stored
                    continue
                if can_fwd:
                    plan_fwd[i] = kind
                    continue
                if stored or t - d < 2:
                    return None
                choice = self._new_storage(v, p, d, slot, src, pending_reads, new_storage)
                if choice is None:
                    return None
                new_storage[v.id] = choice
                mem = self._mem_for(choice, src)
                pending_reads[mem.space] = _pattern(mem)
                plan_storage[i] = choice
            elif isinstance(src, Mem):
                if src.space in ("lm0", "lm1") and self._lm_blocked(src.space, t):
                    return None
                if not self._read_ok(slot, src, pending_reads):
                    return None
                pending_reads[src.space] = _pattern(src)
                if src.tind:
                    pending_reads.setdefault("t", ("t",))
                if src.space == "lm0":
                    touches_lm0 = True
            elif isinstance(src, Fwd):
                if prev < 0 or src.kind not in [FWD_OF_UNIT.get(u) for u in self.slots[prev].units]:
                    return None
        merge_stored = None
        if op.merge_into is not None:
            b = op.merge_into
            bp = self.def_op.get(b.id)
            if bp is None or bp.id not in self.step_of or self.step_of[bp.id] >= t:
                return None
            merge_stored = self.storage.get(b.id) or new_storage.get(b.id)
            if merge_stored is None:
                merge_stored = self._new_storage(b, bp, self.step_of[bp.id], slot, None, pending_reads, new_storage)
                if merge_stored is None:
                    return None
                new_storage[b.id] = merge_stored
        writes = set()
        for dst in op.dsts:
            if isinstance(dst, Mem):
                if dst.space in slot.writes or dst.space in writes:
                    return None
                if dst.space in ("lm0", "lm1"):
                    r = pending_reads.get(dst.space, slot.reads.get(dst.space))
                    if r is not None and r != _pattern(replace(dst, mask=None)):
                        return None
                    if dst.space == "lm0":
                        touches_lm0 = True
                writes.add(dst.space)
            elif isinstance(dst, Omr):
                if "omr" in slot.writes or "omr" in writes:
                    return None
                writes.add("omr")
        if op.flags_out is not None:
            if "omr" in slot.writes or "omr" in writes:
                return None
            free = (16 - self.next_entry) + sum(1 for e in self.free_entries if self.entry_free_at[e] <= t)
            if free <= 0:
                return None  # every mask register entry still holds live flags
            if free <= 2 and self._first_unplaced_flag() is not op:
                return None  # few entries left: keep flag producers in program order (no deadlock)
            writes.add("omr")
        if merge_stored is not None:
            if merge_stored[0] in slot.writes or merge_stored[0] in writes:
                return None
            writes.add(merge_stored[0])
        if is_imm and (slot.lm0_access or touches_lm0):
            return None
        if touches_lm0 and slot.imm:
            return None
        if not self.relax and self._needs_storage(op) and not self._storage_available(op, t, writes, new_storage):
            return None
        return {
            "fwd": plan_fwd, "storage": plan_storage, "new_storage": new_storage, "reads": pending_reads,
            "writes": writes, "imm": is_imm, "lm0": touches_lm0, "mask_read": mask_read, "merge": merge_stored,
        }

    def _commit(self, op, t, plan):
        slot = self._slot(t)
        slot.units[op_unit(op)] = op
        self.step_of[op.id] = t
        slot.reads.update(plan["reads"])
        for mem in plan["writes"]:
            slot.writes[mem] = op.id
        for d in op.dsts:
            if isinstance(d, Mem) and d.space in ("lm0", "lm1"):
                slot.write_pat[d.space] = _pattern(replace(d, mask=None))
        slot.mask_read = plan["mask_read"]
        if op.flush is not None:
            slot.flush_used = True
        slot.imm |= plan["imm"]
        slot.lm0_access |= plan["lm0"]
        for i, kind in plan["fwd"].items():
            self.fwd_use[(op.id, i)] = kind
        for vid, stored in plan["new_storage"].items():
            bank, base, width = stored[:3]
            if bank != "t":
                self._claim(bank, base, width)
            self.storage[vid] = stored
            producer = self.def_op[vid]
            self.slots[self.step_of[producer.id]].writes[bank] = producer.id
            self.extra_dsts.setdefault(producer.id, []).append(stored)
        for i, stored in plan["storage"].items():
            self.use_storage[(op.id, i)] = stored
        if plan["merge"] is not None and op.out is not None:
            # the merged result lives where its base did: record it before the base is released
            self.storage[op.out.id] = plan["merge"]
        for v in op.uses():
            self.uses_left[v.id] = self.uses_left.get(v.id, 0) - 1
            self.last_use[v.id] = max(self.last_use.get(v.id, -1), t)
            if self.uses_left[v.id] == 0:
                st = self.storage.get(v.id)
                if st and st[0] in GRF and v.home is None and not any(self.storage.get(o) == st for o in self._aliases(v)):
                    self.free_ranges[st[0]].append((st[1], st[2], t))
        self._eager_storage(op, t)
        for vid, stored in plan["new_storage"].items():
            if stored[0] == "t":
                self.t_owner = vid
        if any(isinstance(x, Mem) and (x.space == "t" or x.tind) for x in list(op.srcs) + list(op.dsts)):
            self.t_fixed_steps.add(t)
        if op.flags_out is not None:
            self.omr_entry[op.flags_out.id] = self._entry(t)
        for fu in (op.write_mask, op.flush):
            if isinstance(fu, FlagUse) and self.uses_left.get(fu.flags.id, 0) <= 0:
                e = self.omr_entry[fu.flags.id]
                if e not in self.free_entries:
                    self.free_entries.append(e)
                    self.entry_free_at[e] = t

    def _claim(self, bank, base, width):
        self.free_ranges[bank] = [r for r in self.free_ranges[bank] if r[0] != base or r[1] != width]
        self.next_addr[bank] = max(self.next_addr[bank], base + 4 * width)

    def _aliases(self, v):
        """Values sharing v's storage through masked merges (still live)."""
        return [o for o, st in self.storage.items() if o != v.id and self.uses_left.get(o, 0) > 0]

    def _first_unplaced_flag(self):
        while self._flag_order and self._flag_order[0].id in self.step_of:
            self._flag_order.pop(0)
        return self._flag_order[0] if self._flag_order else None

    def _needs_storage(self, op):
        """True when op's result must outlive the forwarding window."""
        v = op.out
        if v is None or v.width == 0 or v.home is not None or op.merge_into is not None or v.id in self.storage:
            return False
        cons = self.consumers.get(v.id, [])
        if not cons:
            return False
        return len(cons) > 1 or any(any(p.id not in self.step_of and p is not op for p in self._preds(c)) for c in cons)

    def _storage_available(self, op, t, writes, new_storage):
        slot = self.slots[t]
        for bank in GRF:
            if bank in slot.writes or bank in writes or any(isinstance(d, Mem) and d.space == bank for d in op.dsts):
                continue
            if any(st[0] == bank for st in new_storage.values()):
                continue
            if self._alloc(bank, op.out.width, {}, at_step=t) is not None:
                return True
        return False

    def _bank_colors(self):
        """A GRF bank per value from a greedy two-colouring of 'read by the same op' (values
        merged into one another share storage, constants keep their homes): one op reading two
        values of one bank needs a staging copy."""
        parent = {}

        def find(x):
            while parent.get(x, x) != x:
                x = parent[x]
            return x

        for op in self.prog.ops:
            if op.merge_into is not None and op.out is not None:
                parent[find(op.out.id)] = find(op.merge_into.id)
        fixed, adj = {}, defaultdict(lambda: defaultdict(int))
        for op in self.prog.ops:
            vals = [x.value for x in op.srcs if isinstance(x, Use)]
            mems = [x.space for x in op.srcs if isinstance(x, Mem) and x.space in GRF]
            ids = []
            for v in vals:
                r = find(v.id)
                if v.home is not None and v.home.space in GRF:
                    fixed[r] = v.home.space
                ids.append(r)
            for i, a in enumerate(ids):
                for b in ids[i + 1:]:
                    if a != b:
                        adj[a][b] += 1
                        adj[b][a] += 1
                for sp in mems:
                    adj[a][("mem", sp)] += 1
        color = dict(fixed)
        for op in self.prog.ops:
            if op.out is None:
                continue
            r = find(op.out.id)
            if r in color:
                continue
            score = {b: 0 for b in GRF}
            for nb, w in adj[r].items():
                c = nb[1] if isinstance(nb, tuple) else color.get(nb)
                if c in score:
                    score[c] += w
            color[r] = min(GRF, key=lambda b: (score[b], self._bank_load[b]))
        return {v: color[find(v)] for v in set(parent) | set(color) if find(v) in color}

    def _bank_preference(self, v):
        """GRF banks ordered by how rarely v's consumers also read them at other addresses."""
        score = {b: 0 for b in GRF}
        c = self.color.get(v.id)
        if c is not None:
            score[c] -= 10  # the colouring decides (it sees the readers of merged values too)
        for c in self.consumers.get(v.id, []):
            for x in c.srcs:
                if isinstance(x, Mem) and x.space in score:
                    score[x.space] += 1
                elif isinstance(x, Use) and x.value is not v:
                    st = self.storage.get(x.value.id)
                    if st is not None and st[0] in score:
                        score[st[0]] += 1
        return sorted(GRF, key=lambda b: (score[b], self._bank_load[b]))

    def _eager_storage(self, op, t):
        """Give a value storage at definition when a write port is free and it may be needed later."""
        v = op.out
        if v is None or v.id in self.storage or getattr(v, "nofwd", False) and op.merge_into is None and v.home is None and v.width == 0:
            return
        if v.width == 0 or v.home is not None or op.merge_into is not None:
            return
        cons = self.consumers.get(v.id, [])
        if not cons:
            return
        later = len(cons) > 1 or v.name == "copy" or any(any(p.id not in self.step_of and p is not op for p in self._preds(c)) for c in cons)
        if not later:
            return
        slot = self.slots[t]
        for bank in self._bank_preference(v):
            if bank in slot.writes or any(isinstance(d, Mem) and d.space == bank for d in op.dsts):
                continue
            base = self._alloc(bank, v.width, {}, at_step=t)
            if base is None:
                continue
            stored = (bank, base, v.width)
            self._claim(bank, base, v.width)
            self.storage[v.id] = stored
            slot.writes[bank] = op.id
            self.extra_dsts.setdefault(op.id, []).append(stored)
            return

    def _unstick(self, ready, remaining):
        """Break a read-port deadlock: copy one stored operand of a stuck op into a fresh value."""
        from dataclasses import replace as dc_replace

        # 1. values whose forwarding window passed without storage: recompute their producers
        def recompute(value, consumer, index, depth):
            prod = self.def_op.get(value.id)
            if prod is None or prod.id not in self.step_of or prod.merge_into is not None or prod.flags_out is not None or depth > 6:
                return False
            if prod.dsts and any(isinstance(d, Mem) and d.space in ("lm0", "lm1") for d in prod.dsts):
                return False
            for x in prod.srcs:
                # the clone reads its operands again: they must still hold the same values
                if isinstance(x, Use) and x.value.home is None and x.value.id in self.storage and self.uses_left.get(x.value.id, 0) <= 0:
                    return False
                if isinstance(x, Mem) and (x.space in ("lm0", "lm1", "t") or x.space in GRF or x.tind):
                    return False
            v2 = Value(value.width, "remat")
            clone = VOp(prod.opcode, list(prod.srcs), out=v2, unit=prod.unit, flush=prod.flush, write_mask=prod.write_mask, note="recompute")
            self.def_op[v2.id] = clone
            self.uses_left[v2.id] = 1
            self.consumers[v2.id] = [consumer]
            self.uses_left[value.id] -= 1
            consumer.srcs[index] = dc_replace(consumer.srcs[index], value=v2)
            self._mem_deps[clone.id] = list(self._mem_deps.get(prod.id, []))
            self.height[clone.id] = self.height[consumer.id] + 1
            remaining.insert(0, clone)
            for j, x in enumerate(clone.srcs):
                if isinstance(x, Use):
                    self.uses_left[x.value.id] = self.uses_left.get(x.value.id, 0) + 1
                    self.consumers[x.value.id].append(clone)
                    if x.value.id not in self.storage:
                        if not recompute(x.value, clone, j, depth + 1):
                            return False
            return True

        port_conflict = self._port_conflict
        conflicts = [(op, port_conflict(op)) for op in ready]
        if not any(i is not None for _, i in conflicts):
            for op in ready:
                for i, src in enumerate(op.srcs):
                    if isinstance(src, Use) and src.value.id not in self.storage:
                        prod = self.def_op.get(src.value.id)
                        if prod is not None and prod.id in self.step_of and recompute(src.value, op, i, 0):
                            return True
        # 2. read-port deadlock: copy a stored operand to a fresh value
        for op, i in conflicts:
            if i is None:
                stored = [(k, s) for k, s in enumerate(op.srcs) if isinstance(s, Use) and s.value.id in self.storage and self.storage[s.value.id][0] in GRF]
                if len(stored) < 2:
                    continue
                i = stored[-1][0]
            self._port_copy(op, i, remaining)
            return True
        return False

    def _port_conflict(self, op, skip=None):
        """Index of a stored operand whose bank is also read at another address by op (storage
        does not move, so the op can never issue as it is)."""
        seen = {}
        for s in op.srcs:
            if isinstance(s, Mem) and s.space in GRF:
                seen.setdefault(s.space, set()).add(_pattern(s))
        hit = None
        for i, s in enumerate(op.srcs):
            if i == skip:
                continue
            if isinstance(s, Use) and s.value.id in self.storage and self.storage[s.value.id][0] in GRF:
                m = self._mem_for(self.storage[s.value.id], s)
                pats = seen.setdefault(m.space, set())
                pats.add(_pattern(m))
                if len(pats) > 1:
                    hit = i
        return hit

    def _port_copy(self, op, i, remaining):
        """Read operand i of op through a fresh copy (forwarded or stored elsewhere)."""
        from dataclasses import replace as dc_replace

        src = op.srcs[i]
        v2 = Value(src.value.width, "copy")
        # the copy lives in the bank the op's other stored operands leave free
        taken = {self.storage[x.value.id][0] for k, x in enumerate(op.srcs)
                 if k != i and isinstance(x, Use) and x.value.id in self.storage}
        taken |= {x.space for x in op.srcs if isinstance(x, Mem)}
        free = [b for b in GRF if b not in taken]
        if free:
            self.color[v2.id] = free[0]
        copy = VOp("lpassa", [Use(src.value)], out=v2, unit="alu", note="port copy")
        self.def_op[v2.id] = copy
        self.uses_left[src.value.id] = self.uses_left.get(src.value.id, 0) + 1
        self.uses_left[v2.id] = 1
        self.consumers[v2.id] = [op]
        op.srcs[i] = dc_replace(src, value=v2)
        self.uses_left[src.value.id] -= 1
        self._mem_deps[copy.id] = []
        self.height[copy.id] = self.height[op.id] + 1
        remaining.insert(0, copy)

    def _entry(self, t):
        for e in list(self.free_entries):
            if self.entry_free_at[e] <= t:
                self.free_entries.remove(e)
                return e
        e = self.next_entry
        self.next_entry += 1
        if e > 15:
            raise CompileError("out of mask register entries")
        return e

    def run(self):
        remaining = list(self.prog.ops)
        t = 0
        last_progress = 0
        while remaining:
            done = self.step_of
            ready = [op for op in remaining if all(p.id in done for p in self._preds(op))]
            prev = self._prev_nonnop(t)

            def urgent(op):
                for v in op.uses():
                    p = self.def_op.get(v.id)
                    if p is not None and self.step_of.get(p.id) == prev and v.id not in self.storage:
                        return 1
                return 0

            pending_lm_reads = set()
            for op in remaining:
                for src in op.srcs:
                    if isinstance(src, Mem) and src.space in ("lm0", "lm1"):
                        pending_lm_reads.add((src.space, op.id))

            def blocks(op):
                for d in op.dsts:
                    if isinstance(d, Mem) and d.space in ("lm0", "lm1"):
                        if any(space == d.space and oid != op.id for space, oid in pending_lm_reads):
                            return 1
                return 0

            def score(op):
                return self.height[op.id] + (self.rng.random() * self.jitter if self.jitter else 0) + 2.0 * urgent(op) - 50.0 * blocks(op)

            ready.sort(key=lambda op: (-score(op), op.id))
            placed = False
            for op in ready:
                plan = self._try(op, t)
                if plan is None and op.alt is not None:
                    # (opcode, unit[, srcs]): the same result on another unit
                    own = (op.opcode, op.unit, list(op.srcs))
                    op.opcode, op.unit = op.alt[0], op.alt[1]
                    if len(op.alt) > 2:
                        op.srcs = list(op.alt[2])
                    plan = self._try(op, t)
                    if plan is None:
                        op.opcode, op.unit, op.srcs = own
                    else:
                        op.alt = own
                if plan is not None:
                    self._commit(op, t, plan)
                    remaining.remove(op)
                    placed = True
                elif self.use_l1copy and self._l1copy_ok(op) and self._try_l1copy(op, t):
                    remaining.remove(op)
                    placed = True
            # copies that became ready in this very step may still go up through the L1BM now
            # (their write lands next step, after the writes they wait for)
            if self.use_l1copy and self.eager_copies:
                for op in list(remaining):
                    if (op not in ready and self._l1copy_ok(op) and all(p.id in self.step_of for p in self._preds(op))
                            and self._try_l1copy(op, t)):
                        remaining.remove(op)
                        placed = True
            # ready ops whose stored operands clash on a read port: copy one now instead of waiting
            for op in (ready if EAGER_COPIES and self.eager_copies else []):
                if (op in remaining and op.merge_into is None and all(p.id in self.step_of for p in self._preds(op))
                        and all(x.value.id in self.storage for x in op.srcs if isinstance(x, Use))
                        and all(self.step_of.get(self.def_op[x.value.id].id, -1) < t for x in op.srcs if isinstance(x, Use) and x.value.id in self.def_op)):
                    i = self._port_conflict(op)
                    if (i is not None and op.id not in self._eager_done and op.srcs[i].value.width == 2
                            and op.srcs[i].value.id not in self._merge_bases and self._port_conflict(op, skip=i) is None):
                        self._eager_done.add(op.id)
                        self._port_copy(op, i, remaining)
            self._slot(t)
            self.relax = not self.pressure or (not placed and t - last_progress >= 2)
            if placed:
                last_progress = t
            elif t - last_progress > 4 and ready and self.unsticks < max(32, len(self.prog.ops)) and self._unstick(ready, remaining):
                self.unsticks += 1
                last_progress = t
            elif t - last_progress > 8:
                raise CompileError(f"cannot place {(ready or remaining)[0]!r}")
            t += 1
        return self.emit()

    # ------------------------------------------------------------ emission
    # ------------------------------------------------------------ copies through the L1BM turnaround register
    def _l1copy_ok(self, op):
        """A plain long-word copy into PE memory (optionally masked) can go PE -> $lbi -> PE with
        l1bmd, using the two L1BM groups instead of the ALU."""
        if op.opcode != "lpassa" or op_unit(op) != "alu" or op.flags_out is not None or op.flush is not None:
            return False
        if len(op.srcs) != 1:
            return False
        if op.merge_into is not None:
            # masked write into the storage of the merged value (its only result)
            if op.dsts or not isinstance(op.write_mask, FlagUse) or op.out is None or op.out.width != 2:
                return False
        else:
            if op.out is not None or len(op.dsts) != 1:
                return False
            dst = op.dsts[0]
            if not isinstance(dst, Mem) or dst.wl != 2 or dst.space == "t" or dst.tind:
                return False
        src = op.srcs[0]
        if isinstance(src, Use):
            return src.value.width == 2 and src.cycle is None and not src.word and not (src.neg or src.ext or src.rnd)
        return isinstance(src, Mem) and src.wl == 2 and not src.tind and src.space != "t" and not (src.neg or src.ext or src.rnd)

    def _try_l1copy(self, op, t):
        nxt = self._slot(t + 1)
        if "l1bm-turnaround" in nxt.units:
            return False
        merge = op.merge_into is not None
        new_st = None
        if merge:
            b = op.merge_into
            bp = self.def_op.get(b.id)
            if bp is None or bp.id not in self.step_of or self.step_of[bp.id] >= t:
                return False
            st = self.storage.get(b.id)
            if st is None:
                st = new_st = self._new_storage(b, bp, self.step_of[bp.id], self._slot(t), None, {}, {})
            if st is None or st[0] not in GRF + ("lm0", "lm1"):
                return False
            dst = storage_mem(st)
        else:
            dst = op.dsts[0]
        key = None
        if isinstance(op.write_mask, FlagUse):
            fp = self.flag_op.get(op.write_mask.flags.id)
            if fp is None or fp.id not in self.step_of or self.step_of[fp.id] >= t + 1:
                return False
            key = (self.omr_entry[op.write_mask.flags.id], op.write_mask.ll)
            if nxt.mask_read is not None and nxt.mask_read != key:
                return False
        if dst.space in nxt.writes:
            return False
        if dst.space in ("lm0", "lm1"):
            r = nxt.reads.get(dst.space)
            if r is not None and r != _pattern(replace(dst, mask=None)):
                return False
            if dst.space == "lm0" and nxt.imm:
                return False
        shadow = replace(op, unit="l1bm", dsts=[], write_mask=None, merge_into=None, out=None)
        plan = self._try(shadow, t, land=t + 1)
        if plan is None:
            return False
        if new_st is not None:
            if any(v == new_st for v in plan["new_storage"].values()):
                return False
            plan["new_storage"][op.merge_into.id] = new_st
        self._commit(shadow, t, plan)
        if isinstance(op.write_mask, FlagUse):
            # the mask entry is read when the write lands (t + 1); release it after its last use
            fid = op.write_mask.flags.id
            self.uses_left[fid] = self.uses_left.get(fid, 0) - 1
            self.last_use[fid] = max(self.last_use.get(fid, -1), t + 1)
            if self.uses_left[fid] <= 0:
                e = self.omr_entry[fid]
                if e not in self.free_entries:
                    self.free_entries.append(e)
                    self.entry_free_at[e] = t + 2
        if merge:
            self.storage[op.out.id] = self.storage[op.merge_into.id]
            mi = op.merge_into
            self.uses_left[mi.id] = self.uses_left.get(mi.id, 0) - 1
            self.last_use[mi.id] = max(self.last_use.get(mi.id, -1), t + 1)
        nxt.units["l1bm-turnaround"] = op
        nxt.writes[dst.space] = op.id
        if dst.space in ("lm0", "lm1"):
            nxt.write_pat[dst.space] = _pattern(replace(dst, mask=None))
        if key is not None:
            nxt.mask_read = key
        if dst.space == "lm0":
            nxt.lm0_access = True
        self.step_of[op.id] = t + 1  # the write lands one step later
        self.l1copy[op.id] = (t, op)
        return True

    def _l1copy_instrs(self, op):
        from .machine import L1

        full = self._instr(op)
        dsts = tuple(d for d in full.dsts if not isinstance(d, NoWrite))
        return Instr("l1bmd", (full.srcs[0],), (L1(None, 2),)), Instr("l1bmd", (L1(None, 2),), dsts)

    def emit(self) -> list[Step]:
        steps = []
        for k, slot in enumerate(self.slots):
            if slot.empty:
                steps.append(Step(nop=1))
                continue
            instrs = []
            for unit, op in slot.units.items():
                if op.id in self.l1copy:
                    up, down = self._l1copy_instrs(self.l1copy[op.id][1])
                    instrs.append(up if unit == "l1bm" else down)
                else:
                    instrs.append(self._instr(op))
            steps.append(Step(instrs))
        merged = []
        for s in steps:
            if s.nop and merged and merged[-1].nop:
                merged[-1].nop += s.nop
            else:
                merged.append(s)
        while merged and merged[-1].nop:
            merged.pop()
        return merged

    def _instr(self, op: VOp) -> Instr:
        srcs = []
        for i, src in enumerate(op.srcs):
            if isinstance(src, Use):
                if (op.id, i) in self.fwd_use:
                    srcs.append(Fwd(self.fwd_use[(op.id, i)], src.neg, src.ext, src.rnd))
                else:
                    srcs.append(self._mem_for(self.use_storage.get((op.id, i)) or self.storage[src.value.id], src))
            else:
                srcs.append(src)
        wmask = None
        if isinstance(op.write_mask, FlagUse):
            wmask = Mask(entry=self.omr_entry[op.write_mask.flags.id], ll=op.write_mask.ll)
        elif isinstance(op.write_mask, Mask):
            wmask = op.write_mask
        dsts = []
        for d in op.dsts:
            if isinstance(d, Mem) and wmask is not None and d.mask is None:
                d = replace(d, mask=wmask)
            dsts.append(d)
        if op.merge_into is not None:
            dsts.append(storage_mem(self.storage[op.merge_into.id], mask=wmask))
        for stored in self.extra_dsts.get(op.id, []):
            dsts.append(storage_mem(stored, mask=wmask))
        if op.flags_out is not None:
            dsts.append(Omr(self.omr_entry[op.flags_out.id]))
        if not dsts:
            dsts.append(NoWrite())
        flush = None
        if isinstance(op.flush, FlagUse):
            flush = Mask(entry=self.omr_entry[op.flush.flags.id], ll=op.flush.ll)
        elif isinstance(op.flush, Mask):
            flush = op.flush
        return Instr(op.opcode, tuple(srcs), tuple(dsts), flush)


# ---------------------------------------------------------------- assembler-backed finishing

def _error_line(err: str):
    m = re.search(r"[Ll]ine (\d+)", err)
    return int(m[1]) if m else None


def repair(steps: list[Step], asm) -> list[Step] | None:
    """Split steps the assembler rejects until it accepts (bounded)."""
    steps = [Step(list(s.instrs), s.nop) for s in steps]
    for _ in range(96):
        result = asm.assemble(emit(steps))
        if result.ok:
            return steps
        line = _error_line(result.error)
        if line is None or line > len(steps):
            return None
        idx = line - 1
        step = steps[idx]
        if step.nop:
            return None

        def reads_fwd(st):
            return any(isinstance(x, Fwd) for ins in st.instrs for x in ins.srcs)

        if len(step.instrs) > 1:
            moved = step.instrs.pop()
            # a new step would separate forwarding pairs: the moved op's reads, or the next step's
            if any(isinstance(x, Fwd) for x in moved.srcs) or (idx + 1 < len(steps) and not steps[idx + 1].nop and reads_fwd(steps[idx + 1])):
                return None
            steps.insert(idx + 1, Step([moved]))
        else:
            if reads_fwd(step):
                return None
            steps.insert(idx, Step(nop=1))
    return None


def _rw_sets(ins):
    """(reads, writes) of an instruction as resource tokens (PE words exactly; transfer buffers by
    kind; forwarding registers and mask entries by name)."""
    def tokens(x):
        if isinstance(x, Mem):
            if x.tind or x.space == "t":
                return {("pe", x.space)}
            return {("pe", x.space, w) for c in range(4) for w in x.words(c)}
        if isinstance(x, L1):
            if x.addr is None:
                return {("lbi",)}
            return {("l1", a) for a in range(x.addr, x.addr + _l1_extent(ins.opcode, x.wl))}
        if isinstance(x, L2):
            return {("l2", a) for a in range(x.addr, x.addr + _l2_extent(ins.opcode))}
        if isinstance(x, Pdm):
            return {("pdm",)}
        if isinstance(x, Dram):
            return {("dram",)}
        if isinstance(x, Fwd):
            return {("fwd", x.kind)}
        if isinstance(x, Omr):
            return {("omr", x.entry)}
        if isinstance(x, Mask) and x.entry is not None:
            return {("omr", x.entry)}
        return set()

    reads, writes = set(), set()
    for x in ins.srcs:
        reads |= tokens(x)
        if isinstance(x, Mem) and x.tind:
            reads.add(("pe", "t"))
    for x in ins.dsts:
        writes |= tokens(x)
        if isinstance(x, Mem) and x.mask is not None:
            reads |= tokens(x.mask)
    if ins.flush is not None:
        reads |= tokens(ins.flush)
    name = ins.opcode.split("/")[0]
    if name.startswith("mv"):
        # MV statements: whole L2BM (any group), PDM and DRAM
        allc = {("l2", a) for a in range(0, 4096)}
        reads |= allc | {("pdm",), ("dram",)}
        writes |= allc | {("pdm",), ("dram",)}
    if any(isinstance(x, L1) and x.addr is not None for x in ins.dsts) and any(isinstance(x, (Mem, Fwd)) for x in ins.srcs):
        writes.add(("lbi",))  # a PE->L1BM transfer also refreshes the turnaround register
    return reads, writes


def _base_opcode(opcode: str) -> str:
    return re.split(r"[@+\-/]", opcode, maxsplit=1)[0]


def _l1_extent(opcode: str, wl: int) -> int:
    """L1BM long words an instruction reads or writes over its four cycles (SDM 3.6.7, 3.6.8)."""
    name = _base_opcode(opcode)
    k = max(1, wl // 2)
    if name.startswith("l2bmb") or name.startswith("l2bmi"):
        return 64
    if name.startswith("l2bmd"):
        return 32
    if name.startswith("l2bm"):
        return 64
    if name.startswith(("l1bmm4", "l1bmr4")):
        return 128
    if name.startswith("l1bmm") or name.startswith("l1bmr"):
        return 16 * k
    if name.startswith("l1bmp"):
        return 4 * k
    return 256


def _l2_extent(opcode: str) -> int:
    name = _base_opcode(opcode)
    if name.startswith("l2bmd"):
        return 256
    if name.startswith(("l2bmb", "l2bm")):
        return 64
    return 4096


def _is_transfer(ins) -> bool:
    name = ins.opcode.split("/")[0]
    return name.startswith(("l1bm", "l2bm", "mv"))


def hoist_transfers(steps: list[Step], asm) -> list[Step]:
    """Move L1BM/L2BM/MV instructions to earlier steps where their unit is free and no instruction in
    between touches what they read or write; the official assembler decides the exact hazard
    distances. Emptied steps become nops (remove_nops trims them afterwards)."""
    steps = [Step(list(s.instrs), s.nop) for s in steps]
    if not asm.assemble(emit(steps)).ok:
        return steps
    j = 0
    while j < len(steps):
        st = steps[j]
        moved_any = False
        for ins in list(st.instrs):
            if not _is_transfer(ins) or any(isinstance(x, Fwd) for x in ins.srcs):
                continue
            unit = transfer_unit(ins)
            mv = unit == "mv"
            r, w = _rw_sets(ins)
            # its forwarding result read by the next step would be lost
            nxt = steps[j + 1] if j + 1 < len(steps) else None
            if nxt is not None and not nxt.nop and any(isinstance(x, Fwd) and x.kind == "lbf" for i2 in nxt.instrs for x in i2.srcs):
                continue
            best = None
            for i in range(j - 1, -1, -1):
                tgt = steps[i]
                blocked = False
                for other in tgt.instrs:
                    r2, w2 = _rw_sets(other)
                    if (r & w2) or (w & (r2 | w2)):
                        blocked = True
                        break
                if blocked:
                    break
                if tgt.nop:
                    continue
                units = {transfer_unit(o) if _is_transfer(o) else unit_of(o.opcode) for o in tgt.instrs}
                if unit in units or (mv and tgt.instrs) or "mv" in units:
                    continue
                trial = [Step(list(x.instrs), x.nop) for x in steps]
                trial[i].instrs.append(ins)
                trial[j].instrs.remove(ins)
                if not trial[j].instrs:
                    trial[j] = Step(nop=1)
                if asm.assemble(emit(trial)).ok:
                    best = trial
            if best is not None:
                steps = best
                moved_any = True
                break
        if not moved_any:
            j += 1
    return steps


def remove_nops(steps: list[Step], asm, check=None) -> list[Step]:
    changed = True
    while changed:
        changed = False
        for i, s in enumerate(steps):
            if not s.nop:
                continue
            trial = list(steps)
            if s.nop > 1:
                trial[i] = Step(nop=s.nop - 1)
            else:
                trial = steps[:i] + steps[i + 1:]
            if asm.assemble(emit(trial)).ok and (check is None or check(trial)):
                steps = trial
                changed = True
                break
    return steps


def _words(steps):
    return sum(s.nop if s.nop else 1 for s in steps)


def rebalance_constants(prog: VProgram, wide: bool = True):
    """Constants live in the top of GRF1; when one op reads two of them, they would compete for
    GRF1's read port, so such constants are moved to GRF0 (greedy two-colouring)."""
    homed = {}
    for op in prog.ops:
        v = op.out
        if v is not None and v.home is not None and v.name.startswith("c:") and v.home.space in GRF and v.home.addrs[0] >= GRF_WORDS - RESERVED_TOP:
            homed[v.id] = v
    if len(homed) < 2:
        return lambda: None
    conflicts = defaultdict(set)
    by_unit = defaultdict(set)
    for op in prog.ops:
        ids = {x.value.id for x in op.srcs if isinstance(x, Use) and x.value.id in homed}
        for a in ids:
            conflicts[a] |= ids - {a}
        by_unit[op_unit(op)] |= ids
    # constants read by different units may be read in one step as well
    units = [u for u in ("alu", "mau") if by_unit[u]]
    if wide and len(units) == 2:
        for a in by_unit["alu"]:
            for b in by_unit["mau"]:
                if a != b:
                    conflicts[a].add(b)
                    conflicts[b].add(a)
    if not any(conflicts.values()):
        return lambda: None
    used = {(m.space, m.addrs[0]) for op in prog.ops for m in op.dsts if isinstance(m, Mem) and m.space in GRF}
    bank_of = {}
    for vid in sorted(homed, key=lambda i: -len(conflicts[i])):
        cnt = {b: sum(1 for n in conflicts[vid] if bank_of.get(n) == b) for b in ("grf1", "grf0")}
        bank_of[vid] = min(("grf1", "grf0"), key=lambda b: (cnt[b], b != "grf1"))
    nxt = {"grf1": GRF_WORDS - RESERVED_TOP, "grf0": GRF_WORDS - RESERVED_TOP}
    # homes taken by other fixed writers in the constant area stay untouched
    taken = {(b, a) for b, a in used if a >= GRF_WORDS - RESERVED_TOP} - {(v.home.space, v.home.addrs[0]) for v in homed.values()}
    remap = {}
    for vid, v in homed.items():
        b = bank_of[vid]
        while (b, nxt[b]) in taken:
            nxt[b] += 2
        if nxt[b] + 2 > 510:  # (510-511 stay unwritten: the zero words)
            return lambda: None  # no room: keep the original homes
        remap[(v.home.space, v.home.addrs[0])] = (b, nxt[b])
        nxt[b] += 2
    saved_dsts = {op.id: op.dsts for op in prog.ops}
    saved_homes = {v.id: v.home for v in homed.values()}
    for op in prog.ops:
        new_dsts = []
        for m in op.dsts:
            if isinstance(m, Mem) and m.space in GRF:
                base = (m.space, m.addrs[0] - m.addrs[0] % 2)
                if base in remap:
                    b, a = remap[base]
                    m = replace(m, space=b, addrs=tuple(a + x - base[1] for x in m.addrs))
            new_dsts.append(m)
        op.dsts = new_dsts
    for v in homed.values():
        b, a = remap[(v.home.space, v.home.addrs[0])]
        v.home = replace(v.home, space=b, addrs=(a,) * 4)

    def undo():
        for op in prog.ops:
            op.dsts = saved_dsts[op.id]
        for v in homed.values():
            v.home = saved_homes[v.id]

    return undo


def _turnaround_ok(steps) -> bool:
    """Every read of the L1BM turnaround register directly follows a PE -> L1BM transfer."""
    prev = None
    for st in steps:
        for ins in st.instrs:
            if ins.unit == "l1bm-turnaround" and not (prev is not None and any(i.unit == "l1bm" for i in prev.instrs)):
                return False
        prev = st if not st.nop else None
    return True


def schedule(prog: VProgram, asm=None, *, tries: int = 1, seed: int = 0) -> list[Step]:
    best = None
    errors = []
    for kk in range(4 * tries + 1):
        # constant placement policy, register-pressure mode and priority jitter vary by try; the
        # second half schedules without the bank colouring and eager port copies (some programs
        # pack better with the plain heuristics)
        fifo = kk == 4 * tries
        k, plain = (0, False) if fifo else (kk % (2 * tries), kk >= 2 * tries)
        undo = rebalance_constants(prog, wide=(k // 2) % 2 == 0)
        try:
            for l1 in (True, False):
                try:
                    sch = Scheduler(prog, seed=seed + k // 2, jitter=0.0 if k < 4 else 1.5, pressure=k % 2 == 0)
                    if fifo:
                        # Program order keeps streaming groups interleaved; critical-path
                        # priority can bunch all buffered groups ahead of direct writes.
                        sch.height = dict.fromkeys(sch.height, 0)
                    if plain:
                        sch.color = {}
                        sch.eager_copies = False
                    sch.use_l1copy = l1
                    steps = sch.run()
                except CompileError as exc:
                    errors.append(str(exc))
                    steps = None
                    break
                if asm is not None:
                    steps = repair(steps, asm)
                    if steps is None:
                        errors.append("assembler repair failed")
                        break
                if not sch.l1copy or _turnaround_ok(steps):
                    break
                steps = None  # repair separated an L1BM copy's two halves: schedule without them
        finally:
            undo()
        if steps is None:
            continue
        if asm is not None and len(steps) < 400:
            steps = remove_nops(steps, asm)  # compare tries by their final length
        if best is None or _words(steps) < _words(best):
            best = steps
    if best is None:
        raise CompileError("no schedule: " + "; ".join(errors[:3]))
    return best
