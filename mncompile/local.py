"""Local maps: every output lane is computed from inputs stored in the same PE.

The strategy applies when, for a representative PE, each output long word's
lanes are the same scalar function of input lanes held by that PE at the same
lane position, and other PEs hold the same function of the inputs at the same
local addresses (the program is SPMD). Output words with the same function
form classes; each vector op covers four words (one per cycle, any addresses).
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field

from .errors import CompileError
from .ir import Node, walk
from .layout import Contract, TensorSpec
from .machine import Mem


@dataclass(frozen=True)
class Leaf:
    tensor: str
    space: str
    addr: int  # long word address
    lane: int
    src: int | None = None  # PE (within the MAB) holding it when it is not the computing PE


@dataclass
class WordTask:
    """One output long word: its lanes' expressions with leaves resolved locally."""

    out: TensorSpec
    addr: int
    lanes: dict  # lane -> Node
    leaves: dict  # (node id) -> Leaf, input leaves for this PE
    signature: tuple = ()


@dataclass
class LocalProblem:
    rep_pe: int
    tasks: list
    classes: dict  # signature -> [WordTask]
    inputs: dict  # name -> TensorSpec
    outputs: dict

    def pe_index(self, pe):
        """(output name, addr) -> task for a checked PE."""
        cache = self.__dict__.setdefault("_index", {})
        if pe not in cache:
            cache[pe] = {(t.out.name, t.addr): t for t in self.pe_tasks[pe]}
        return cache[pe]


def _input_index(contract: Contract):
    """(tensor name, logical index) -> {pe: (addr, lane)} for every replica."""
    table = {}
    for spec in contract.inputs:
        if spec.space == "dram":
            continue
        for idx in spec.all_indices():
            locs = spec.locations(idx, replicate=True)
            table[(spec.name, idx)] = {loc.pe: (loc.addr, loc.lane) for loc in locs}
    return table


def _canon(node: Node, leaf_of, memo, values=True):
    """Structure of an expression with input leaves replaced by (tensor, rel addr slot, lane)."""
    hit = memo.get(node.id)
    if hit is not None:
        return hit
    if node.op == "input":
        r = ("in",) + leaf_of(node)
    elif node.op == "const":
        r = ("c", type(node.value).__name__, node.value) if values or node.ty == "b" else ("c", type(node.value).__name__)
    else:
        r = (node.op, node.ty) + tuple(_canon(a, leaf_of, memo, values) for a in node.args)
    memo[node.id] = r
    return r


def _neighbors(pes, rep):
    """PEs differing from `rep` in one coordinate (to fit location-dependent constants)."""
    have = set(pes)
    out = []
    for step in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048):
        if rep + step in have:
            out.append(rep + step)
    return out


def analyze(contract: Contract, outputs: dict, rep_pe: int | None = None, check_pes: int = 8, words: bool = False,
            pe_constants: bool = False, exchange: bool = False, offsets: bool = False,
            lane_aligned: bool = True) -> LocalProblem:
    """`outputs[name][index] -> Node`. Raises CompileError when not a uniform local map.

    With `words`, 32-bit lanes are treated as separate words (addresses are word
    addresses, every lane is lane 0), so operands from any lane can be combined.
    With `pe_constants`, constants may differ between lanes and PEs (the caller
    must then materialize them from the PE coordinates; see `lp.pe_tasks`).
    """
    inputs = {s.name: s for s in contract.inputs}
    table = _input_index(contract)
    if words:
        if any(s.dtype.bits != 32 for s in list(contract.inputs) + list(contract.outputs)):
            raise CompileError("word-level map needs 32-bit data")
        table = {k: {pe: (2 * a + l, 0) for pe, (a, l) in v.items()} for k, v in table.items()}
    by_pe = defaultdict(list)  # pe -> [(spec, addr, lane, node)]
    for spec in contract.outputs:
        if spec.space == "dram":
            raise CompileError("local map: DRAM output")
        for idx, node in outputs[spec.name].items():
            loc = spec.locations(idx, replicate=False)[0]
            if words:
                by_pe[loc.pe].append((spec, 2 * loc.addr + loc.lane, 0, node))
            else:
                by_pe[loc.pe].append((spec, loc.addr, loc.lane, node))
    if not by_pe:
        raise CompileError("no outputs")
    pes = sorted(by_pe)
    rep = rep_pe if rep_pe is not None else pes[0]

    def tasks_for(pe):
        words = defaultdict(dict)
        for spec, addr, lane, node in by_pe[pe]:
            words[(spec.name, addr)][lane] = node
        tasks = []
        for (name, addr), lanes in sorted(words.items()):
            leaves = {}
            spec = next(s for s in contract.outputs if s.name == name)
            for lane, node in lanes.items():
                for n in walk([node]):
                    if n.op == "input":
                        reps = table.get(n.value)
                        if reps is not None and pe in reps:
                            a, l = reps[pe]
                            leaves[n.id] = Leaf(n.value[0], inputs[n.value[0]].space, a, l)
                            continue
                        near = [q for q in (reps or ()) if q // 4 == pe // 4] if exchange else []
                        if not near:
                            raise CompileError(f"local map: {n.value} is not stored in PE {pe}")
                        q = min(near)
                        a, l = reps[q]
                        leaves[n.id] = Leaf(n.value[0], inputs[n.value[0]].space, a, l, src=q % 4)
            tasks.append(WordTask(spec, addr, lanes, leaves))
        return tasks

    def signatures(tasks, lane_aligned=lane_aligned, with_values=True):
        out = []
        for task in tasks:
            memo = {}
            lane_sigs = []
            full = []
            for lane in sorted(task.lanes):
                node = task.lanes[lane]

                def leaf_of(n, lane=lane):
                    leaf = task.leaves[n.id]
                    if lane_aligned and leaf.lane != lane:
                        raise CompileError("local map: lane-misaligned operand")
                    return (leaf.tensor,)

                lane_sigs.append(_canon(node, leaf_of, {}, values=not pe_constants))
                if pe_constants:
                    full.append(_canon(node, leaf_of, {}))
            if len(set(lane_sigs)) != 1:
                raise CompileError("local map: lanes compute different functions")
            # word-level operand structure: which distinct input words feed which leaf slot
            out.append((task.out.name, tuple(sorted(task.lanes)), lane_sigs[0]) + ((tuple(full),) if with_values and pe_constants else ()))
        return out

    rep_tasks = tasks_for(rep)
    sigs = signatures(rep_tasks)
    for task, sig in zip(rep_tasks, sigs):
        task.signature = sig
    cmp_sigs = [sg[:3] for sg in sigs]
    # SPMD check on other PEs: same output words, same structure, same local input addresses
    sample = [p for p in pes if p != rep]
    step = max(1, len(sample) // check_pes)
    checked = sample[::step][:check_pes]
    if pe_constants or exchange or offsets:
        extra = _neighbors(pes, rep) + [q for q in (rep + 3,) if q in set(pes)]
        checked = extra + [p for p in checked if p not in extra]
    pe_tasks = {rep: rep_tasks}
    shifted, pairs = set(), {}
    for pe in checked:
        other = tasks_for(pe)
        pe_tasks[pe] = other
        if len(other) != len(rep_tasks):
            raise CompileError("local map: PEs hold different output words")
        osigs = [sg[:3] for sg in signatures(other, with_values=False)] if pe_constants else signatures(other)
        for a, b, sa, sb in zip(rep_tasks, other, cmp_sigs, osigs):
            if (a.out.name, a.addr) != (b.out.name, b.addr) or sa != sb:
                raise CompileError("local map: non-uniform across PEs")
            la, lb = _leaf_addrs(a), _leaf_addrs(b)
            if sorted(la) != sorted(lb):
                if not offsets:
                    raise CompileError("local map: input addresses differ across PEs")
                # every differing leaf: same tensor (in LM0) shifted by one per-PE amount
                for (lane_a, pa), (lane_b, pb) in zip(la, lb):
                    if lane_a != lane_b or len(pa) != len(pb):
                        raise CompileError("local map: input structure differs across PEs")
                    for (ta, aa, wa), (tb, ab, wb) in zip(pa, pb):
                        if ta != tb or wa != wb:
                            raise CompileError("local map: inputs differ across PEs")
                        pairs.setdefault(pe, []).append((ta, ab - aa))
                        if aa != ab:
                            if inputs[ta].space != "lm0":
                                raise CompileError("local map: shifted input outside LM0")
                            shifted.add(ta)
    classes = defaultdict(list)
    for task in rep_tasks:
        classes[task.signature].append(task)
    lp = LocalProblem(rep, rep_tasks, dict(classes), inputs, {s.name: s for s in contract.outputs})
    lp.words = words
    lp.pe_tasks = pe_tasks
    lp.shift = None
    if shifted:
        # every leaf of a shifted tensor moves by the same amount in a PE (one T offset per tensor)
        shift = {t: {rep: 0} for t in shifted}
        for pe in checked:
            for t in shifted:
                ds = {d for tt, d in pairs.get(pe, []) if tt == t}
                if len(ds) > 1:
                    raise CompileError("local map: an input is shifted by several amounts")
                shift[t][pe] = ds.pop() if ds else 0
        lp.shift = shift
    return lp


def _leaf_addrs(task: WordTask):
    """Per lane and structural position, the input word address (structure-ordered)."""
    out = []
    for lane in sorted(task.lanes):
        order = []
        for n in walk([task.lanes[lane]]):
            if n.op == "input":
                leaf = task.leaves[n.id]
                order.append((leaf.tensor, leaf.addr, leaf.lane))
        out.append((lane, tuple(order)))
    return out
