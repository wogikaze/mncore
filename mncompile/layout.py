"""Tensor contracts in the official MN-Core Challenge layout notation.

A contract is what a problem statement gives for each tensor, for example::

    Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

Each logical axis is a product of dims ``size[_AXIS]:stride`` listed from the
outermost to the innermost. A dim without an axis name moves along the memory
address in long words (64 bit), ``W`` is the lane inside a long word (lane 0 is
the MSB side), and ``PE``, ``MAB``, ``L1B`` and ``L2B`` select the hardware
position. Several dims may map to the same axis; their contributions add.
``B@[...]`` lists axes over which an input is replicated. An output is checked
only at index 0 of the hardware axes it does not mention.

For DRAM tensors the ``L2B`` axis index selects the group (index // 2).
"""

from __future__ import annotations

import itertools
import math
import re
from dataclasses import dataclass, field

from .errors import CompileError

HW_AXES = ("L2B", "L1B", "MAB", "PE")
AXIS_SIZE = {"L2B": 8, "L1B": 8, "MAB": 16, "PE": 4}
N_PES = 4096


@dataclass(frozen=True)
class DType:
    name: str
    bits: int
    kind: str  # "int", "uint", "float", "bytes"

    @property
    def lanes(self) -> int:
        return 64 // self.bits

    @property
    def is_float(self) -> bool:
        return self.kind == "float"


DTYPES = {
    "Long": DType("Long", 64, "int"),
    "ULong": DType("ULong", 64, "uint"),
    "Int": DType("Int", 32, "int"),
    "UInt": DType("UInt", 32, "uint"),
    "Short": DType("Short", 16, "int"),
    "UShort": DType("UShort", 16, "uint"),
    "Double": DType("Double", 64, "float"),
    "Float": DType("Float", 32, "float"),
    "Half": DType("Half", 16, "float"),
    "String": DType("String", 8, "bytes"),
}


@dataclass(frozen=True)
class Dim:
    size: int
    axis: str  # "" (address), "W", or one of HW_AXES
    stride: int

    def text(self):
        return f"{self.size}{'_' + self.axis if self.axis else ''}:{self.stride}"


@dataclass(frozen=True)
class Layout:
    axes: tuple[tuple[Dim, ...], ...]
    broadcast: tuple[Dim, ...] = ()
    shape: tuple[int, ...] | None = None

    @property
    def logical_shape(self) -> tuple[int, ...]:
        return tuple(math.prod(d.size for d in axis) for axis in self.axes)

    def text(self):
        body = ", ".join("(" + ", ".join(d.text() for d in axis) + ")" for axis in self.axes)
        if self.broadcast:
            body += "; B@[" + ",".join(
                d.axis if d.size == AXIS_SIZE.get(d.axis) and d.stride == 1 else d.text()
                for d in self.broadcast
            ) + "]"
        prefix = "(" + ",".join(map(str, self.shape)) + ")" if self.shape else ""
        return f"{prefix}/({body})"


_DIM = re.compile(r"^(\d+)(?:_([A-Z0-9]+))?:(\d+)$")


def _parse_dim(text: str) -> Dim:
    match = _DIM.match(text.strip())
    if not match:
        raise CompileError(f"Bad layout dim {text!r}")
    size, axis, stride = int(match[1]), match[2] or "", int(match[3])
    if axis not in ("", "W", *HW_AXES):
        raise CompileError(f"Unknown layout axis {axis!r}")
    return Dim(size, axis, stride)


def parse_layout(text: str) -> Layout:
    text = text.strip()
    shape = None
    match = re.match(r"^\(([\d,\s]*)\)\s*/\s*(.*)$", text)
    if match and not match[1].strip().startswith("("):
        shape = tuple(int(x) for x in match[1].split(",") if x.strip())
        text = match[2]
    elif text.startswith("/"):
        text = text[1:].strip()
    else:
        raise CompileError(f"Layout must start with an optional shape and '/': {text!r}")
    if not (text.startswith("(") and text.endswith(")")):
        raise CompileError(f"Bad layout body {text!r}")
    body = text[1:-1]
    broadcast: tuple[Dim, ...] = ()
    if ";" in body:
        body, bpart = body.split(";", 1)
        bmatch = re.match(r"^\s*B@\[(.*)\]\s*$", bpart)
        if not bmatch:
            raise CompileError(f"Bad broadcast clause {bpart!r}")
        items = []
        for item in bmatch[1].split(","):
            item = item.strip()
            if item in HW_AXES:
                items.append(Dim(AXIS_SIZE[item], item, 1))
            else:
                items.append(_parse_dim(item))
        broadcast = tuple(items)
    axes = []
    for group in re.findall(r"\(([^()]*)\)", body):
        axes.append(tuple(_parse_dim(part) for part in group.split(",") if part.strip()))
    if not axes:
        raise CompileError(f"Layout has no axes: {text!r}")
    layout = Layout(tuple(axes), broadcast, shape)
    if shape is not None and len(shape) == len(axes) and shape != layout.logical_shape:
        raise CompileError(f"Layout shape {shape} disagrees with dims {layout.logical_shape}")
    return layout


@dataclass(frozen=True)
class Loc:
    """One long word lane: PE index (or DRAM group for DRAM), long word address, lane."""

    pe: int
    addr: int
    lane: int


def pe_index(l2b: int, l1b: int, mab: int, pe: int) -> int:
    return ((l2b * 8 + l1b) * 16 + mab) * 4 + pe


def pe_coords(index: int) -> dict[str, int]:
    return {
        "L2B": index // 512,
        "L1B": index // 64 % 8,
        "MAB": index // 4 % 16,
        "PE": index % 4,
    }


@dataclass(frozen=True)
class TensorSpec:
    """A tensor in PE local memory (``lm0``/``lm1``) or DRAM, with its value domain."""

    name: str
    dtype: DType
    space: str  # "lm0", "lm1", "dram"
    start: int  # words for LM, long words for DRAM
    end: int
    layout: Layout
    low: float | int | None = None
    high: float | int | None = None
    atol: float = 0.0
    group: int = 0
    domain: str | None = None  # optional Python predicate over `x`, e.g. "x & (x - 1) == 0"
    allow_inf: bool = False

    @property
    def shape(self) -> tuple[int, ...]:
        return self.layout.logical_shape

    @property
    def size(self) -> int:
        return math.prod(self.shape)

    @property
    def base_long(self) -> int:
        return self.start // 2 if self.space != "dram" else self.start

    def _axis_positions(self, axis_dims, index):
        """Decompose one logical index over its dims; returns contributions per axis."""
        contrib: dict[str, int] = {}
        for dim in reversed(axis_dims):
            index, digit = divmod(index, dim.size)
            contrib[dim.axis] = contrib.get(dim.axis, 0) + digit * dim.stride
        return contrib

    def positions(self, index: tuple[int, ...]) -> dict[str, int]:
        total: dict[str, int] = {}
        for axis_dims, i in zip(self.layout.axes, index):
            for key, value in self._axis_positions(axis_dims, i).items():
                total[key] = total.get(key, 0) + value
        return total

    def locations(self, index: tuple[int, ...], *, replicate: bool) -> list[Loc]:
        """Physical lanes holding logical element `index`.

        With `replicate` (inputs), broadcast axes take every value; otherwise the
        unmentioned hardware axes are 0.
        """
        pos = self.positions(index)
        addr = self.base_long + pos.get("", 0)
        lane = pos.get("W", 0)
        if self.space == "dram":
            group = pos.get("L2B", 2 * self.group) // 2
            return [Loc(group, addr, lane)]
        choices = []
        for axis in HW_AXES:
            base = pos.get(axis, 0)
            options = [base]
            if replicate:
                for dim in self.layout.broadcast:
                    if dim.axis == axis:
                        options = [base + k * dim.stride for k in range(dim.size)]
            choices.append(options)
        return [
            Loc(pe_index(*combo), addr, lane)
            for combo in itertools.product(*choices)
        ]

    def all_indices(self):
        return itertools.product(*(range(n) for n in self.shape))

    def check(self):
        lanes = self.dtype.lanes
        long_words = (self.end - self.start) // (2 if self.space != "dram" else 1)
        for index in self.all_indices():
            pos = self.positions(index)
            if pos.get("W", 0) >= lanes:
                raise CompileError(f"{self.name}: lane {pos['W']} exceeds {lanes} lanes")
            if not 0 <= pos.get("", 0) < max(long_words, 1):
                raise CompileError(f"{self.name}: address {pos.get('', 0)} outside {self.space}[{self.start}:{self.end}]")
            for axis in HW_AXES:
                if pos.get(axis, 0) >= AXIS_SIZE[axis]:
                    raise CompileError(f"{self.name}: {axis} index {pos[axis]} out of range")


_MEM = re.compile(r"^\$(l?)([mnd])\[(\d+):(\d+)\](?:@(\d+))?$")


def parse_tensor(
    name: str,
    dtype: str,
    memory: str,
    layout: str,
    *,
    low=None,
    high=None,
    atol=0.0,
    domain=None,
    allow_inf=False,
) -> TensorSpec:
    if dtype not in DTYPES:
        raise CompileError(f"Unknown dtype {dtype!r}")
    match = _MEM.match(memory.replace(" ", ""))
    if not match:
        raise CompileError(f"Bad memory range {memory!r}")
    _, kind, start, end, group = match.groups()
    space = {"m": "lm0", "n": "lm1", "d": "dram"}[kind]
    spec = TensorSpec(
        name=name,
        dtype=DTYPES[dtype],
        space=space,
        start=int(start),
        end=int(end),
        layout=parse_layout(layout),
        low=low,
        high=high,
        atol=float(atol or 0.0),
        group=int(group or 0),
        domain=domain,
        allow_inf=allow_inf,
    )
    spec.check()
    return spec


@dataclass
class Contract:
    inputs: list[TensorSpec]
    outputs: list[TensorSpec]
    notes: dict = field(default_factory=dict)

    @classmethod
    def from_json(cls, data: dict) -> "Contract":
        def make(entry):
            return parse_tensor(
                entry["name"],
                entry["dtype"],
                entry["memory"],
                entry["layout"],
                low=entry.get("low"),
                high=entry.get("high"),
                atol=entry.get("atol", 0.0),
                domain=entry.get("domain"),
                allow_inf=entry.get("allow_inf", False),
            )

        return cls(
            [make(e) for e in data.get("inputs", [])],
            [make(e) for e in data.get("outputs", [])],
            {k: v for k, v in data.items() if k not in ("inputs", "outputs")},
        )
