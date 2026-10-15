"""Structured MN-Core 2 instructions: every operand form, emission and access sets.

An `Instr` is one instruction expression (one unit). A `Step` is one line of
VSM: expressions issued together (or a nop). Operands are structured, so the
scheduler can reason about the memories and word addresses each expression
reads and writes in each of the four cycles. Every opcode of the ISA can be
expressed: ALU (`[u][dfghlis]<op>`, `imm`, `zero`), MAU (`[dfgh](v|m)(fma|mul|
add|passa)[u|d][r]`), matrix register write/read, L1BM, L2BM, MV, `wait`,
`noforward` and `nop`.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field, replace

from .errors import CompileError

PE_MEMORIES = ("lm0", "lm1", "grf0", "grf1", "t")
LETTER = {"lm0": "m", "lm1": "n", "grf0": "r", "grf1": "s", "t": "t"}
WL_PREFIX = {1: "", 2: "l", 4: "ll"}


@dataclass(frozen=True)
class Mask:
    """Write mask (on an output) or zero-flush mask (on an opcode)."""

    pattern: str | None = None  # "1010" fixed entry
    entry: int | None = None  # variable entry 1..15 ($imr<n>)
    ll: bool = False

    def text(self):
        if self.entry is not None:
            return f"${'ll' if self.ll else ''}imr{self.entry}"
        return ("ll" if self.ll else "") + self.pattern

    def flags(self) -> list[bool] | None:
        if self.pattern is not None:
            return [c == "1" for c in self.pattern]
        return None


@dataclass(frozen=True)
class Mem:
    """A PE memory operand: LM0/LM1/GRF0/GRF1 (addressed) or T."""

    space: str
    wl: int = 2  # access width in words: 1, 2 (long), 4 (two long)
    addrs: tuple[int, int, int, int] = (0, 0, 0, 0)  # word address per cycle
    neg: bool = False
    ext: bool = False  # 'e' precision extension
    rnd: bool = False  # 'r' rounding
    tind: bool = False  # LM0 T-register indirect
    madpe: int | None = None  # 'j<n>' address modifier
    mask: Mask | None = None
    trange: tuple[int, int] | None = None  # word range a T-indirect access stays within (when known)

    def __post_init__(self):
        if self.space not in PE_MEMORIES:
            raise CompileError(f"bad memory {self.space}")
        if self.space != "t":
            for a in self.addrs:
                if a % self.wl:
                    raise CompileError(f"unaligned {self.space} address {a} for width {self.wl}")

    @staticmethod
    def vec(space, base, wl=2, stride=None):
        stride = wl if stride is None else stride
        return Mem(space, wl, tuple(base + stride * c for c in range(4)))

    def text(self):
        s = "-" if self.neg else ""
        s += "$" + WL_PREFIX[self.wl] + LETTER[self.space]
        if self.space == "t":
            pass
        else:
            if self.tind:
                s += "t"
            a = self.addrs
            d = a[1] - a[0]
            if a[2] - a[1] == d and a[3] - a[2] == d and d >= 0 and (d == 0 or d % 1 == 0):
                s += str(a[0])
                if d != 0:
                    s += "v" + ("" if d == self.wl else str(d))
            else:
                s += "[" + ",".join(map(str, a)) + "]"
            if self.madpe is not None:
                s += f"j{self.madpe}"
        if self.ext:
            s += "e"
        if self.rnd:
            s += "r"
        if self.mask is not None:
            s += "/" + self.mask.text()
        return s

    def words(self, cycle: int) -> list[int]:
        """Word addresses touched in `cycle` (T: the cycle's 4-word slot)."""
        if self.space == "t":
            return [cycle * 4 + k for k in range(4)]
        base = self.addrs[cycle]
        return list(range(base, base + self.wl))


@dataclass(frozen=True)
class Fwd:
    kind: str  # aluf, mauf, lbf, mreadf
    neg: bool = False
    ext: bool = False
    rnd: bool = False

    def text(self):
        return ("-" if self.neg else "") + "$" + self.kind + ("e" if self.ext else "") + ("r" if self.rnd else "")


@dataclass(frozen=True)
class Fixed:
    name: str  # l2bid, l1bid, mabid, peid, subpeid, msb1

    def text(self):
        return "$" + self.name


@dataclass(frozen=True)
class Imm:
    kind: str  # f, h, i, s, ui, us
    literal: str

    def text(self):
        return f'{self.kind}"{self.literal}"'


@dataclass(frozen=True)
class Omr:
    entry: int
    mask: Mask | None = None

    def text(self):
        return f"$omr{self.entry}" + ("/" + self.mask.text() if self.mask else "")


@dataclass(frozen=True)
class NoWrite:
    def text(self):
        return "$nowrite"


@dataclass(frozen=True)
class Bar:
    lm1: bool
    wl: int = 1
    mask: Mask | None = None

    def text(self):
        return "$" + WL_PREFIX[self.wl] + ("n" if self.lm1 else "m") + "b" + ("/" + self.mask.text() if self.mask else "")


@dataclass(frozen=True)
class L1(object):
    """L1BM operand in an L1BM or L2BM expression (`addr=None` is the turnaround register)."""

    addr: int | None
    wl: int = 2

    def text(self):
        return "$" + WL_PREFIX[self.wl] + "b" + ("i" if self.addr is None else str(self.addr))


@dataclass(frozen=True)
class L2:
    addr: int
    l2b: int | None = None
    group: int | None = None

    def text(self):
        s = f"$lc{self.addr}"
        if self.group is not None:
            s += f"@{self.group}" + (f".{self.l2b}" if self.l2b is not None else "")
        elif self.l2b is not None:
            s += f"@.{self.l2b}"
        return s


@dataclass(frozen=True)
class Dram:
    addr: int
    group: int | None = None
    indirect: bool = False

    def text(self):
        return f"$d{'i' if self.indirect else ''}{self.addr}" + (f"@{self.group}" if self.group is not None else "")


@dataclass(frozen=True)
class Pdm:
    addr: int
    group: int | None = None

    def text(self):
        return f"$p{self.addr}" + (f"@{self.group}" if self.group is not None else "")


@dataclass(frozen=True)
class Mat:
    side: str  # x or y
    row: int | None = None
    wl: int = 2

    def text(self):
        return "$" + WL_PREFIX[self.wl] + self.side + ("" if self.row is None else str(self.row))


@dataclass(frozen=True)
class Dar:
    addr: int

    def text(self):
        return f"$dar{self.addr}"


Operand = Mem | Fwd | Fixed | Imm | Omr | NoWrite | Bar | L1 | L2 | Dram | Pdm | Mat | Dar


ALU_OPS = {
    # name: (inputs, kind) kind: untyped / int / float / both / bfn / bfe
    "msl": (1, "untyped"), "msr": (1, "untyped"), "passa": (1, "both"), "inc": (1, "int"),
    "dec": (1, "int"), "not": (1, "int"), "lnot": (1, "int"), "rsqrt": (1, "float"),
    "floor": (1, "float"), "ftoi": (1, "float"), "bfe": (1, "bfe"), "bfn": (1, "bfn"),
    "max": (2, "both"), "min": (2, "both"), "packbit": (2, "both"), "and": (2, "int"),
    "or": (2, "int"), "xor": (2, "int"), "add": (2, "int"), "sub": (2, "int"),
    "lsl": (2, "int"), "lsr": (2, "int"), "bsl": (2, "int"), "bsr": (2, "int"),
    "relu": (2, "float"), "relu0": (2, "float"), "relu1": (2, "float"), "relu2": (2, "float"),
    "relu3": (2, "float"), "lrelud": (2, "float"), "lreluo": (2, "float"), "ilrelud": (2, "float"),
}
ALU_PRECISIONS = {
    "untyped": [""], "int": ["l", "i", "s"], "float": ["d", "f", "h"],
    "both": ["d", "f", "h", "l", "i", "s"], "bfn": ["d", "f", "g", "h"], "bfe": ["h"],
}
UNSIGNED_OK = {"inc", "dec", "ftoi", "max", "min", "add", "sub", "lsr"}
RRN_OPS = [f"{p}fadd" for p in "dfh"] + [f"{p}max" for p in "dfh"] + [f"{p}min" for p in "dfh"] + [
    f"{p}{o}" for p in "lis" for o in ("iadd", "band", "and", "bor", "or")
]


def alu_opcodes():
    """Every ALU opcode spelling."""
    out = ["zero", "imm", "immu"]
    for name, (_, kind) in ALU_OPS.items():
        for prec in ALU_PRECISIONS[kind]:
            if name in ("bfe", "bfn") and prec == "h":
                for n in range(6, 10):
                    out.append(f"h{name}/{n}")
                continue
            out.append(prec + name)
            if name in UNSIGNED_OK and (kind == "int" or prec in "lis" or name == "ftoi"):
                out.append("u" + prec + name)
    return out


def mau_opcodes():
    out = []
    for p in "dfgh":
        for mode in "vm":
            for k in ("fma", "mul", "add", "passa"):
                if mode == "m" and k in ("add", "passa"):
                    continue
                if mode == "v" and p == "g":
                    continue
                halves = ["u", "d"] if p == "d" and k in ("fma", "mul") else [""]
                for h in halves:
                    for r in ("", "r"):
                        if r and p not in "dh":
                            continue
                        out.append(f"{p}{mode}{k}{h}{r}")
        out += [f"{p}mwrite", f"{p}mread"]
    return out


def unit_of(opcode: str) -> str:
    """Parallel-issue group of an opcode (SDM 3.6.4)."""
    base = opcode.split("/")[0]
    if base == "nop":
        return "nop"
    if base == "noforward":
        return "noforward"
    if base == "wait":
        return "wait"
    if base == "l2bmdarw":
        return "l2bmdarw"
    if base.startswith("l2bm"):
        return "l2bm"
    if base.startswith("l1bm"):
        return "l1bm"  # turnaround distinction is made from operands
    if base.startswith("mv"):
        return "mv"
    if re.fullmatch(r"[dfgh]mwrite", base):
        return "mwrite"
    if re.fullmatch(r"[dfgh]mread", base):
        return "mread"
    if re.fullmatch(r"[dfgh][vm](fma|mul|add|passa)[ud]?r?", base):
        return "mau"
    return "alu"


@dataclass(frozen=True)
class Instr:
    opcode: str
    srcs: tuple = ()
    dsts: tuple = ()
    flush: Mask | None = None

    @property
    def unit(self):
        u = unit_of(self.opcode)
        if u == "l1bm":
            if any(isinstance(o, L1) and o.addr is None for o in self.srcs):
                return "l1bm-turnaround"
        return u

    def text(self):
        op = self.opcode + ("/" + self.flush.text() if self.flush else "")
        parts = [op] + [o.text() for o in self.srcs] + [o.text() for o in self.dsts]
        return " ".join(parts)


@dataclass
class Step:
    instrs: list = field(default_factory=list)
    nop: int = 0  # nop count when this is a nop step

    def text(self):
        if self.nop:
            return "nop" if self.nop == 1 else f"nop/{self.nop}"
        return "; ".join(i.text() for i in self.instrs)


def emit(steps: list[Step]) -> str:
    return "".join(s.text() + "\n" for s in steps)


def words(steps: list[Step]) -> int:
    return sum(s.nop if s.nop else 1 for s in steps)


# ------------------------------------------------------------------ access sets

def reads(instr: Instr):
    """(memory, cycle, word) triples read by an expression, plus forwarding kinds."""
    out = []
    fwd = set()
    for o in instr.srcs:
        if isinstance(o, Mem):
            for c in range(4):
                for w in o.words(c):
                    out.append((o.space, c, w))
            if o.tind:
                for c in range(4):
                    out.append(("t", c, c * 4))
        elif isinstance(o, Fwd):
            fwd.add(o.kind)
    for o in instr.dsts:
        mask = getattr(o, "mask", None)
        if mask is not None and mask.entry is not None:
            for c in range(4):
                out.append(("omr", c, mask.entry))
    if instr.flush is not None and instr.flush.entry is not None:
        for c in range(4):
            out.append(("omr", c, instr.flush.entry))
    return out, fwd


def writes(instr: Instr):
    out = []
    for o in instr.dsts:
        if isinstance(o, Mem):
            flags = o.mask.flags() if o.mask else None
            for c in range(4):
                if flags is not None and not flags[c]:
                    continue
                for w in o.words(c):
                    out.append((o.space, c, w))
        elif isinstance(o, Omr):
            for c in range(4):
                out.append(("omr", c, o.entry))
        elif isinstance(o, Bar):
            for c in range(4):
                out.append(("bar_n" if o.lm1 else "bar_m", c, 0))
    return out


# ------------------------------------------------------------------ parsing

_MASK_RE = re.compile(r"^(ll)?([01]{4})$|^\$(ll)?imr(\d+)$")


def parse_mask(text: str) -> Mask:
    text = text.rstrip("tp")
    m = _MASK_RE.match(text)
    if not m:
        raise CompileError(f"bad mask {text!r}")
    if m[2]:
        return Mask(pattern=m[2], ll=bool(m[1]))
    return Mask(entry=int(m[4]), ll=bool(m[3]))


def _split_operands(rest: str) -> list[str]:
    toks, cur, quote = [], "", False
    i = 0
    while i < len(rest):
        c = rest[i]
        if quote:
            cur += c
            if c == '"':
                quote = False
            i += 1
            continue
        starts = (c == "$" and not cur.endswith("/") and not cur.endswith("-")) or (c == "-" and rest[i + 1:i + 2] == "$")
        if c.isspace() or (starts and cur):
            if cur:
                toks.append(cur)
                cur = ""
            if c.isspace():
                i += 1
                continue
        if c == '"':
            quote = True
        cur += c
        i += 1
    if cur:
        toks.append(cur)
    return toks


_PE_MEM = re.compile(r"^(-)?\$(ll|l)?([mnrst])(t)?(?:(\d+)(?:v(\d*))?|\[([\d,\s]+)\])?(?:j(\d+))?(e|r)?$")


def parse_operand(tok: str):
    mask = None
    body = tok
    if "/" in tok and not tok.startswith(('i"', 'f"', 'h"', 's"', 'ui"', 'us"')):
        body, mtext = tok.split("/", 1)
        mask = parse_mask(mtext)
    if m := re.match(r'^(f|h|i|s|ui|us)"(.*)"$', body):
        return Imm(m[1], m[2])
    neg = body.startswith("-")
    core = body[1:] if neg else body
    for kind in ("aluf", "mauf", "lbf", "mreadf"):
        if core.startswith("$" + kind):
            suf = core[len(kind) + 1:]
            return Fwd(kind, neg, suf == "e", suf == "r")
    if core in ("$l2bid", "$l1bid", "$mabid", "$peid", "$subpeid", "$msb1"):
        return Fixed(core[1:])
    if core == "$nowrite":
        return NoWrite()
    if m := re.match(r"^\$omr(\d+)$", core):
        return Omr(int(m[1]), mask)
    if m := re.match(r"^\$dar(\d+)$", core):
        return Dar(int(m[1]))
    if m := re.match(r"^\$(ll|l)?([mn])b$", core):
        return Bar(m[2] == "n", {None: 1, "l": 2, "ll": 4}[m[1]], mask)
    if m := re.match(r"^\$(ll|l)?b(i|\d+)$", core):
        return L1(None if m[2] == "i" else int(m[2]), {None: 1, "l": 2, "ll": 4}[m[1]])
    if m := re.match(r"^\$lc(\d+)(?:@(\d*)(?:\.(\d+))?)?$", core):
        return L2(int(m[1]), int(m[3]) if m[3] else None, int(m[2]) if m[2] else None)
    if m := re.match(r"^\$d(i)?(\d+|0x[0-9a-fA-F]+)(?:@(\d+))?$", core):
        return Dram(int(m[2], 0), int(m[3]) if m[3] else None, bool(m[1]))
    if m := re.match(r"^\$p(\d+|0x[0-9a-fA-F]+)(?:@(\d+))?$", core):
        return Pdm(int(m[1], 0), int(m[2]) if m[2] else None)
    if m := re.match(r"^\$(ll|l)?([xy])(\d+)?$", core):
        return Mat(m[2], int(m[3]) if m[3] else None, {None: 1, "l": 2, "ll": 4}[m[1]])
    m = _PE_MEM.match(body)
    if m:
        neg, wlp, letter, tind, base, inc, flat, madpe, er = m.groups()
        wl = {None: 1, "l": 2, "ll": 4}[wlp]
        space = {"m": "lm0", "n": "lm1", "r": "grf0", "s": "grf1", "t": "t"}[letter]
        if space == "t":
            addrs = (0, 0, 0, 0)
            wl = 4
        elif flat:
            addrs = tuple(int(x) for x in flat.split(","))
        else:
            b = int(base or 0)
            step = (int(inc) if inc else wl) if inc is not None else 0
            addrs = tuple(b + step * c for c in range(4))
        mem = Mem.__new__(Mem)
        object.__setattr__(mem, "space", space)
        object.__setattr__(mem, "wl", wl)
        object.__setattr__(mem, "addrs", addrs)
        object.__setattr__(mem, "neg", bool(neg))
        object.__setattr__(mem, "ext", er == "e")
        object.__setattr__(mem, "rnd", er == "r")
        object.__setattr__(mem, "tind", bool(tind))
        object.__setattr__(mem, "madpe", int(madpe) if madpe else None)
        object.__setattr__(mem, "mask", mask)
        return mem
    raise CompileError(f"unparsed operand {tok!r}")


class RawInstr(Instr):
    """An expression kept verbatim (MV statements and forms emitted as written)."""


def parse_expr(text: str):
    text = text.strip()
    if not text:
        return None
    parts = text.split(None, 1)
    opcode = parts[0]
    rest = parts[1] if len(parts) > 1 else ""
    flush = None
    if "/" in opcode and not opcode.startswith(("mv", "l2bm", "hbf", "nop")):
        opcode, mtext = opcode.split("/", 1)
        flush = parse_mask(mtext)
    toks = _split_operands(rest)
    ops = [parse_operand(t) for t in toks]
    nin = n_inputs(opcode, ops)
    return Instr(opcode, tuple(ops[:nin]), tuple(ops[nin:]), flush)


def n_inputs(opcode: str, ops) -> int:
    base = opcode.split("/")[0]
    if base in ("zero", "nop", "noforward", "l2bmdarw", "quit"):
        return 0
    if base in ("imm", "immu", "wait"):
        return 1
    if base.startswith(("l1bm", "l2bm", "mv")):
        return 1
    if re.fullmatch(r"[dfgh]mwrite|[dfgh]mread", base):
        return 1
    if m := re.fullmatch(r"[dfgh]([vm])(fma|mul|add|passa)[ud]?r?", base):
        return {"fma": 3, "mul": 2, "add": 2, "passa": 1}[m[2]]
    name = base
    if name.startswith("u") and len(name) > 1:
        name = name[1:]
    if name in ALU_OPS:
        return ALU_OPS[name][0]
    if name[1:] in ALU_OPS or name[1:].split("/")[0] in ALU_OPS:
        return ALU_OPS[name[1:].split("/")[0]][0]
    raise CompileError(f"unknown opcode {opcode!r}")


def parse_program(source: str) -> list[Step]:
    """Parse VSM PE/MV statements into steps (debug and mask directives are rejected)."""
    steps = []
    for raw in source.splitlines():
        line = re.sub(r"[#!].*$", "", raw).strip()
        if not line:
            continue
        exprs = [e.strip() for e in line.split(";") if e.strip()]
        if len(exprs) == 1 and re.fullmatch(r"nop(/\d+)?", exprs[0]):
            n = int(exprs[0].split("/")[1]) if "/" in exprs[0] else 1
            steps.append(Step(nop=n))
            continue
        instrs = []
        for e in exprs:
            if re.fullmatch(r"nop(/\d+)?", e):
                raise CompileError("nop issued with other expressions")
            instrs.append(parse_expr(e))
        steps.append(Step(instrs))
    return steps
