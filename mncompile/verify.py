"""Generic verification of a program against the reference kernel.

Inputs are drawn from each tensor's declared domain (random values, boundary
values, and every value of a small finite domain), placed at every replica
location, and the program is run on the native simulator. Each output element
is compared with the reference (binary64 evaluation rounded to the output
format) under the declared tolerance.
"""

from __future__ import annotations

import itertools
import math
import re
import random
from collections import defaultdict
from dataclasses import dataclass, field

from .errors import CompileError
from .layout import Contract, TensorSpec, pe_coords
from .oracle import run_reference
from .sim import official_run, simulator
from .values import decode, encode, matches, pack, round_to, unpack

FULL = {"L2B": 8, "L1B": 8, "MAB": 16, "PE": 4}


def _domain_filter(spec: TensorSpec):
    if not spec.domain:
        return None
    code = compile(spec.domain, f"<domain {spec.name}>", "eval")

    def ok(x, idx):
        return bool(eval(code, {"math": math}, {"x": x, "idx": idx}))

    return ok


def finite_domain(spec: TensorSpec, limit: int = 1 << 16):
    """All admissible values if the domain is small and enumerable, else None."""
    ok = _domain_filter(spec)
    if spec.dtype.is_float:
        if spec.low is None or spec.high is None:
            return None
        # enumerate floats of the format in range only when the count is small
        width = spec.dtype.bits
        lo, hi = float(spec.low), float(spec.high)
        if ok is None:
            return None
        # candidates on a dyadic grid: try fine grids until the filter accepts a manageable set
        for denom in (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024):
            n = int((hi - lo) * denom) + 1
            if n > limit:
                break
            values = [lo + k / denom for k in range(n)]
            accepted = [v for v in values if ok(v, None)]
            if accepted and all(round_to(v, width) == v for v in accepted):
                finer = [lo + k / (denom * 2) for k in range(int((hi - lo) * denom * 2) + 1)]
                if [v for v in finer if ok(v, None)] == accepted:
                    return accepted
        return None
    lo = int(spec.low if spec.low is not None else (0 if spec.dtype.kind != "int" else -(1 << (spec.dtype.bits - 1))))
    hi = int(spec.high if spec.high is not None else ((1 << spec.dtype.bits) - 1 if spec.dtype.kind != "int" else (1 << (spec.dtype.bits - 1)) - 1))
    if hi - lo + 1 > limit:
        return None
    values = list(range(lo, hi + 1))
    if ok:
        values = [v for v in values if ok(v, None)]
    return values


def sample_value(spec: TensorSpec, rng: random.Random, idx):
    ok = _domain_filter(spec)
    for _ in range(10000):
        if spec.dtype.is_float:
            lo, hi = float(spec.low), float(spec.high)
            r = rng.random()
            if r < 0.04:
                v = rng.choice([lo, hi, 0.0 if lo <= 0 <= hi else lo])
            elif r < 0.1:
                v = float(rng.randint(math.ceil(lo), math.floor(hi))) if math.floor(hi) >= math.ceil(lo) else lo
            else:
                v = rng.uniform(lo, hi)
            v = round_to(v, spec.dtype.bits)
            v = min(max(v, lo), hi) if not (lo <= v <= hi) else v
            if not (lo <= v <= hi):
                continue
        else:
            lo = int(spec.low)
            hi = int(spec.high)
            r = rng.random()
            if r < 0.05:
                v = rng.choice([lo, hi])
            else:
                v = rng.randint(lo, hi)
        if ok is None or ok(v, idx):
            return v
    raise CompileError(f"Cannot sample the domain of {spec.name}")


def make_inputs(contract: Contract, seed: int, exhaustive_round: int = 0):
    """Logical input values for one test case."""
    rng = random.Random(seed)
    values = {}
    for spec in contract.inputs:
        finite = finite_domain(spec)
        indices = list(spec.all_indices())
        vals = {}
        if exhaustive_round % 2 == 1:
            # independent samples: coverage rounds can make outputs degenerate (e.g. every value present)
            for idx in indices:
                vals[idx] = sample_value(spec, rng, idx)
        elif finite is not None and spec.domain is None and len(finite) <= len(indices) * 64:
            # cover every value of a small range across cases
            order = finite[:]
            rng.shuffle(order)
            start = exhaustive_round * len(indices)
            for k, idx in enumerate(indices):
                vals[idx] = order[(start + k) % len(order)]
        elif finite is not None:
            order = finite[:]
            rng.shuffle(order)
            start = exhaustive_round * len(indices)
            for k, idx in enumerate(indices):
                v = order[(start + k) % len(order)]
                ok = _domain_filter(spec)
                if ok and not ok(v, idx):
                    v = sample_value(spec, rng, idx)
                vals[idx] = v
        else:
            for idx in indices:
                vals[idx] = sample_value(spec, rng, idx)
        values[spec.name] = vals
    return values


def _path(pes: set[int]) -> str | None:
    """Debug location suffix selecting exactly `pes`, or None if not a box."""
    coords = [pe_coords(p) for p in pes]
    parts = []
    names = [("L2B", None), ("L1B", "b"), ("MAB", "m"), ("PE", "p")]
    sets = {axis: sorted({c[axis] for c in coords}) for axis, _ in names}
    box = 1
    for axis, _ in names:
        box *= len(sets[axis])
    if box != len(pes):
        return None
    l2bs = sets["L2B"]
    if len(l2bs) == 8:
        pass
    elif len(l2bs) == 1:
        parts.append(f"n{l2bs[0] // 2}c{l2bs[0] % 2}")
    elif len(l2bs) == 2 and l2bs[0] // 2 == l2bs[1] // 2:
        parts.append(f"n{l2bs[0] // 2}")
    else:
        return None
    for axis, letter in names[1:]:
        s = sets[axis]
        if len(s) == FULL[axis]:
            continue
        if len(s) == 1:
            parts.append(f"{letter}{s[0]}")
        else:
            return None
    return "".join(parts)


def input_prefix(contract: Contract, values) -> str:
    """`d set` / DRAM `r` lines placing the logical inputs at every replica."""
    lines = []
    for spec in contract.inputs:
        words = defaultdict(dict)  # (pe, addr) -> {lane: bits}
        for idx, v in values[spec.name].items():
            for loc in spec.locations(idx, replicate=True):
                words[(loc.pe, loc.addr)][loc.lane] = encode(v, spec.dtype)
        if spec.space == "dram":
            for (group, addr), lanes in sorted(words.items()):
                word = pack(lanes, spec.dtype)
                lines.append(f"r {group} {addr:09x} 001 {word:016X}")
            continue
        mem = {"lm0": "m", "lm1": "n"}[spec.space]
        by_word = defaultdict(set)
        contents = {}
        for (pe, addr), lanes in words.items():
            word = pack(lanes, spec.dtype)
            by_word[(addr, word)].add(pe)
        for (addr, word), pes in sorted(by_word.items()):
            path = _path(pes)
            groups = [pes] if path is not None else [{p} for p in sorted(pes)]
            for g in groups:
                suffix = _path(g)
                lines.append(f"d set $l{mem}{addr * 2}{suffix} 1 {word:016X}")
    return "\n".join(lines) + "\n"


def output_probes(contract: Contract, expected) -> tuple[str, list]:
    """`d get` lines for every output long word, and the lanes to check."""
    lines = []
    checks = []
    seen = set()
    for spec in contract.outputs:
        for idx, want in expected[spec.name].items():
            locs = spec.locations(idx, replicate=False)
            loc = locs[0]
            checks.append((spec, idx, loc, want))
            key = (spec.space, loc.pe, loc.addr)
            if key in seen:
                continue
            seen.add(key)
            if spec.space == "dram":
                lines.append(f"d get $d{loc.addr}n{loc.pe} 1")
            else:
                c = pe_coords(loc.pe)
                mem = {"lm0": "m", "lm1": "n"}[spec.space]
                lines.append(
                    f"d get $l{mem}{loc.addr * 2}n{c['L2B'] // 2}c{c['L2B'] % 2}b{c['L1B']}m{c['MAB']}p{c['PE']} 1"
                )
    return "\n".join(lines) + "\n", checks


def _pe_name(pe):
    c = pe_coords(pe)
    return f"n{c['L2B'] // 2}c{c['L2B'] % 2}b{c['L1B']}m{c['MAB']}p{c['PE']}"


@dataclass
class Verdict:
    ok: bool
    cases: int = 0
    mismatches: list = field(default_factory=list)
    error: str | None = None
    words: int | None = None
    max_error: float = 0.0

    def summary(self):
        if self.error:
            return f"error: {self.error}"
        if self.ok:
            return f"ok ({self.cases} cases, max error {self.max_error:.3g})"
        return f"{len(self.mismatches)} mismatches, e.g. {self.mismatches[:3]}"


def expected_outputs(source, contract, values):
    raw = run_reference(source, contract.inputs, contract.outputs, values)
    out = {}
    for spec in contract.outputs:
        d = {}
        for idx, v in raw[spec.name].items():
            if spec.dtype.is_float:
                d[idx] = round_to(float(v), spec.dtype.bits)
            elif isinstance(v, bool):
                d[idx] = int(v)
            else:
                d[idx] = v
        out[spec.name] = d
    return out


# opcodes the native simulator does not model faithfully: always use the official emulator
_OFFICIAL_ONLY = re.compile(r"(^|[\s;])(u?h[vm]\w*|hmwrite|hmread|ilrelud\w*|l2bmdar\w*)\b", re.M)


def needs_official(program: str) -> bool:
    return _OFFICIAL_ONLY.search(program) is not None


def verify(program: str, source: str, contract: Contract, *, cases: int = 3, seed: int = 1, extra_values=None, backend: str = "native") -> Verdict:
    if backend == "native" and needs_official(program):
        backend = "official"
    sim = simulator() if backend == "native" else None
    verdict = Verdict(True)
    case_values = [make_inputs(contract, seed + k, exhaustive_round=k) for k in range(cases)]
    if extra_values:
        case_values.extend(extra_values)
    for values in case_values:
        expected = expected_outputs(source, contract, values)
        prefix = input_prefix(contract, values)
        probes, checks = output_probes(contract, expected)
        result = sim.run(program, prefix=prefix, suffix=probes) if sim else official_run(program, prefix, probes)
        verdict.words = result.words
        verdict.cases += 1
        if not result.ok:
            verdict.ok = False
            verdict.error = f"{result.part} line {result.line}: {result.error}"
            return verdict
        for spec, idx, loc, want in checks:
            if spec.space == "dram":
                key = ("DRAM", f"n{loc.pe}", loc.addr)
            else:
                key = ({"lm0": "LM0", "lm1": "LM1"}[spec.space], _pe_name(loc.pe), loc.addr * 2)
            word = result.dump.get(key)
            if word is None:
                verdict.ok = False
                verdict.mismatches.append((spec.name, idx, "missing", want))
                continue
            have = decode(unpack(word, spec.dtype, loc.lane), spec.dtype)
            if not matches(have, want, spec.dtype, spec.atol):
                verdict.ok = False
                if len(verdict.mismatches) < 50:
                    verdict.mismatches.append((spec.name, idx, have, want))
            elif spec.dtype.is_float and not (math.isinf(have) or math.isinf(want)):
                verdict.max_error = max(verdict.max_error, abs(have - want))
        if not verdict.ok:
            return verdict
    return verdict
