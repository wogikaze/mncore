"""Parser for official testcase VSM files (prefix with inputs, suffix with checks)."""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass

from ..layout import AXIS_SIZE, pe_index

MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="


@dataclass
class Entry:
    kind: str  # "set" (LM d set), "dram" (r line), "get"
    mem: str  # lm0, lm1, grf..., dram
    wl: int
    addr: int
    pes: list[int]  # PE indices (or DRAM groups for dram)
    indices: list[tuple[int, ...]]
    values: list
    dtype: str
    atol: float = 0.0
    payload: list[int] | None = None
    raw: str = ""
    tensor: str = ""  # "in0", "out0", ...


_LOC = re.compile(r"^\$(ll|l)?([mnrsd])(\d+)((?:[ncbmp]\d+)*)$")


def _pes_of(path: str) -> list[int]:
    fixed = {k: int(v) for k, v in re.findall(r"([ncbmp])(\d+)", path)}
    groups = [fixed["n"]] if "n" in fixed else range(4)
    l2bs = [fixed["c"]] if "c" in fixed else range(2)
    l1bs = [fixed["b"]] if "b" in fixed else range(8)
    mabs = [fixed["m"]] if "m" in fixed else range(16)
    pes = [fixed["p"]] if "p" in fixed else range(4)
    return [pe_index(g * 2 + c, b, m, p) for g in groups for c in l2bs for b in l1bs for m in mabs for p in pes]


def _comment(line: str):
    m = re.search(r"#\s*(?:values|expect)=(.*?) / (\S+) @(\S+)(?: atol=(\S+))?", line)
    if not m:
        return None
    values_text, dtype, idx_text, atol = m.groups()
    if dtype == "String":
        values = ast.literal_eval(values_text)
    else:
        values = ast.literal_eval(values_text.replace("-inf", "'-inf'").replace("inf", "'inf'"))
        values = [float(v) if v in ("inf", "-inf") else v for v in values]
    indices = [tuple(x) if isinstance(x, list) else (x,) for x in ast.literal_eval("[" + idx_text + "]")]
    return values, dtype, indices, float(atol) if atol else 0.0


def parse_entries(text: str) -> list[Entry]:
    out = []
    tensor = ""
    for line in text.splitlines():
        line = line.strip()
        if header := re.match(r"# =+ (In|Out)\((\d+)\)", line):
            tensor = ("in" if header[1] == "In" else "out") + header[2]
            continue
        if line.startswith("d set") or line.startswith("d get"):
            parts = line.split("#")[0].split()
            loc = parts[2]
            count = int(parts[3])
            m = _LOC.match(loc)
            if not m:
                continue
            wl = {"ll": 4, "l": 2, None: 1}[m[1]]
            mem = {"m": "lm0", "n": "lm1", "r": "grf0", "s": "grf1", "d": "dram"}[m[2]]
            addr = int(m[3])
            info = _comment(line)
            if info is None:
                continue
            values, dtype, indices, atol = info
            if mem == "dram":
                group = int(re.search(r"n(\d+)", m[4])[1]) if "n" in m[4] else 0
                pes = [group]
            else:
                pes = _pes_of(m[4])
            payload = None
            if parts[1] == "set":
                hexs = "".join(parts[4:])
                payload = [int(hexs[i:i + 16], 16) for i in range(0, len(hexs), 16)]
            out.append(Entry("set" if parts[1] == "set" else "get", mem, wl, addr, pes, indices, values, dtype, atol, payload, line, tensor))
            assert count == 1 or parts[1] == "set"
        elif line.startswith("r "):
            parts = line.split("#")[0].split()
            group, addr, count, payload = int(parts[1]), int(parts[2], 16), int(parts[3], 16), parts[4]
            info = _comment(line)
            if info is None:
                continue
            values, dtype, indices, atol = info
            words = [int(payload[i:i + 16], 16) for i in range(0, len(payload), 16)]
            out.append(Entry("dram", "dram", 2, addr, [group], indices, values, dtype, atol, words, line, tensor))
    return out


def split(testcase_text: str) -> tuple[str, str]:
    if MARKER not in testcase_text:
        raise ValueError("testcase has no insertion marker")
    prefix, suffix = testcase_text.split(MARKER, 1)
    return prefix, suffix


def input_values(testcase_text: str, contract) -> dict:
    """Logical input values of the official testcase, keyed like `verify.make_inputs`
    ({input name: {index: value}}); In(k) is the contract's k-th input."""
    from ..values import decode, unpack

    names = [spec.name for spec in contract.inputs]
    out = {name: {} for name in names}
    for e in parse_entries(testcase_text):
        if e.kind not in ("set", "dram") or not e.tensor.startswith("in"):
            continue
        k = int(e.tensor[2:])
        if k >= len(names):
            raise ValueError(f"testcase input {e.tensor} has no contract tensor")
        spec = contract.inputs[k]
        for lane, idx in enumerate(e.indices):
            index = tuple(idx) + (0,) * (len(spec.shape) - len(idx))
            out[names[k]][index] = decode(unpack(e.payload[0], spec.dtype, lane), spec.dtype)
    for spec in contract.inputs:
        missing = set(spec.all_indices()) - set(out[spec.name])
        if missing:
            raise ValueError(f"testcase leaves {len(missing)} elements of {spec.name} unset")
    return out
