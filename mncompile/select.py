"""Instruction selection for lane-wise scalar functions.

`GroupGen` turns template expressions (one lane's function; every lane of a
word computes the same function of the same-lane inputs) into virtual machine
ops for one vector group: four output words, one per cycle, at arbitrary
addresses. Several output templates that share subexpressions can be generated
in one group (common subexpressions are computed once).

Integer-typed values may be held in a float representation when they are
small exact integers (|x| < 2^23); conversions are explicit ops.
"""

from __future__ import annotations

import math
import struct
from dataclasses import dataclass, replace

from .errors import CompileError
from .ir import Node, walk
from .layout import DType
from .machine import Imm, Mask, Mem
from .values import float_decode, float_encode
from .vprog import FlagUse, Use, Value, VOp, VProgram

MAGIC23 = 0x4B000000  # float 2^23: low 23 mantissa bits hold an integer


@dataclass
class LaneType:
    kind: str  # "int", "uint", "float"
    bits: int

    @property
    def iprec(self):
        return {64: "l", 32: "i", 16: "s", 8: "s"}[self.bits]

    @property
    def fprec(self):
        return {64: "d", 32: "f", 16: "h"}[self.bits]

    @property
    def unsigned(self):
        return self.kind == "uint"


def lane_type(dtype: DType) -> LaneType:
    if dtype.kind == "bytes":
        return LaneType("uint", 8)
    return LaneType(dtype.kind, dtype.bits)


def once(mem: Mem) -> Mem:
    """A constant is the same in every cycle: write it only in the first cycle."""
    return replace(mem, mask=Mask(pattern="1000"))


def f32_bits(value: float) -> int:
    return struct.unpack(">I", struct.pack(">f", value))[0]


def f32(value: float) -> float:
    return struct.unpack(">f", struct.pack(">f", value))[0]


ZERO_WORD = 510  # GRF words 510-511 are never written: they read as zero


def zero_value() -> Value:
    """A value that is zero from the start (no producing op)."""
    v = Value(2, "zero", home=Mem("grf0", 2, (ZERO_WORD,) * 4))
    v.preset = True
    v.nofwd = True
    return v


class Constants:
    """Constant vectors, each materialized once into a fixed GRF home (alternating GRF1/GRF0,
    so that ops reading two constants do not compete for one read port)."""

    def __init__(self, prog: VProgram, base: int = 448):
        self.prog = prog
        if getattr(prog, "constants", None) is None:
            prog.constants = self  # later passes over the program reuse these constants
        self.cache: dict = {}
        self.next = {"grf1": base, "grf0": base}
        self.turn = 0

    def _home(self):
        # GRF1 first; constants read together by one op are separated later (schedule.rebalance_constants)
        for bank in ("grf1", "grf0"):
            if self.next[bank] + 2 <= ZERO_WORD:
                a = self.next[bank]
                self.next[bank] += 2
                return bank, a
        raise CompileError("too many constants")

    def _value(self, key, writes_of, label, fwd_ok):
        if key in self.cache:
            return self.cache[key]
        if key[1] == 0:
            # zero needs no immediate: GRF words nothing ever writes read as 0 (memory starts zeroed)
            self.cache[key] = zero_value()
            return self.cache[key]
        bank, a = self._home()
        home = Mem(bank, 2, (a, a, a, a))
        v = Value(2, f"c:{label}", home=home)
        v.nofwd = not fwd_ok
        writes = writes_of(bank, a)
        for i, (imm, dst) in enumerate(writes):
            op = VOp("imm", [imm], dsts=[once(dst)], unit="alu", note=f"const {label}")
            if i == len(writes) - 1:
                op.out = v
            self.prog.add(op)
        self.cache[key] = v
        return v

    def word32(self, bits: int, label="") -> Value:
        bits &= 0xFFFFFFFF
        return self._value(("w32", bits), lambda b, a: [(Imm("ui", "0x%08X" % bits), Mem(b, 2, (a,) * 4))], label or hex(bits), True)

    def word16(self, bits: int, label="") -> Value:
        bits &= 0xFFFF
        return self._value(("w16", bits), lambda b, a: [(Imm("us", "0x%04X" % bits), Mem(b, 2, (a,) * 4))], label or hex(bits), True)

    def word64(self, value: int, label="") -> Value:
        value &= (1 << 64) - 1
        hi, lo = value >> 32, value & 0xFFFFFFFF
        if hi == lo:
            return self.word32(lo, label)

        def writes(b, a):
            out = []
            if hi:
                out.append((Imm("ui", "0x%08X" % hi), Mem(b, 2, (a,) * 4)))
            out.append((Imm("ui", "0x%08X" % lo), Mem(b, 1, (a + 1,) * 4)))
            return out

        return self._value(("w64", value), writes, label or hex(value), False)

    def scalar(self, value, lt: LaneType, rep: str = "int") -> Value:
        if rep == "float":
            width = {32: 32, 64: 64, 16: 16, 8: 32}[lt.bits]
            if width == 32:
                # an inexact constant is rounded to the nearest f32 (verification checks the error)
                return self.word32(f32_bits(float(value)), repr(value))
            if width == 64:
                return self.word64(struct.unpack(">Q", struct.pack(">d", float(value)))[0], repr(value))
            bits = float_encode(float(value), 16)
            if float_decode(bits, 16) != float(value) and not math.isinf(value):
                raise CompileError(f"constant {value} is not exact in half")
            return self.word16(bits, repr(value))
        v = int(value)
        if lt.bits == 32:
            return self.word32(v, str(v))
        if lt.bits == 64:
            return self.word64(v, str(v))
        if lt.bits in (16, 8):
            return self.word16(v, str(v))
        raise CompileError(f"no constant for {lt}")


def interval(node: Node, env_ranges: dict, memo: dict):
    """Value range of an int/bool node, or of an integral float node."""
    hit = memo.get(node.id)
    if hit is not None:
        return hit
    r = None
    if node.op == "const":
        if isinstance(node.value, bool):
            r = (int(node.value), int(node.value))
        elif isinstance(node.value, (int, float)) and math.isfinite(node.value):
            r = (node.value, node.value)
    elif node.op == "input":
        r = env_ranges.get(node.value[0])
    elif node.ty == "b":
        r = (0, 1)
    else:
        args = [interval(a, env_ranges, memo) for a in node.args]
        op = node.op
        try:
            if op == "select":
                if args[1] is not None and args[2] is not None:
                    r = (min(args[1][0], args[2][0]), max(args[1][1], args[2][1]))
            elif all(x is not None for x in args):
                if op in ("add", "sum"):
                    r = (sum(x[0] for x in args), sum(x[1] for x in args))
                elif op == "sub":
                    r = (args[0][0] - args[1][1], args[0][1] - args[1][0])
                elif op == "mul":
                    c = [x * y for x in args[0] for y in args[1]]
                    r = (min(c), max(c))
                elif op == "neg":
                    r = (-args[0][1], -args[0][0])
                elif op == "abs":
                    lo, hi = args[0]
                    r = (0 if lo <= 0 <= hi else min(abs(lo), abs(hi)), max(abs(lo), abs(hi)))
                elif op in ("max", "min"):
                    f = max if op == "max" else min
                    r = (f(x[0] for x in args), f(x[1] for x in args))
                elif op == "and" and all(x[0] >= 0 for x in args):
                    r = (0, min(x[1] for x in args))
                elif op in ("or", "xor") and all(x[0] >= 0 for x in args):
                    hi = max(x[1] for x in args)
                    r = (0, (1 << int(hi).bit_length()) - 1)
                elif op == "shl" and node.args[1].op == "const" and args[0][0] >= 0:
                    r = (args[0][0] << node.args[1].value, args[0][1] << node.args[1].value)
                elif op == "shr" and node.args[1].op == "const":
                    r = (args[0][0] >> node.args[1].value, args[0][1] >> node.args[1].value)
                elif op == "mod" and node.args[1].op == "const" and node.args[1].value > 0:
                    d = node.args[1].value
                    r = args[0] if 0 <= args[0][0] and args[0][1] < d else (0, d - 1)
                elif op == "floordiv" and node.args[1].op == "const" and node.args[1].value > 0:
                    r = (args[0][0] // node.args[1].value, args[0][1] // node.args[1].value)
                elif op == "bit_length":
                    lo, hi = args[0]
                    r = (int(lo).bit_length() if lo >= 0 else 0, max(abs(int(lo)), abs(int(hi))).bit_length())
                elif op in ("toint", "floor"):
                    r = (math.floor(args[0][0]), math.floor(args[0][1]))
                elif op == "trunc":
                    r = (int(args[0][0]), int(args[0][1]))
                elif op == "tofloat":
                    r = args[0]
                elif op == "not":
                    r = (~args[0][1], ~args[0][0])
        except (TypeError, ValueError, OverflowError):
            r = None
    memo[node.id] = r
    return r


class GroupGen:
    """Emit ops computing templates for one group of four output words."""

    def __init__(self, prog: VProgram, consts: Constants, lt: LaneType, operands: dict, ranges: dict, uses: dict, *, variant: dict | None = None):
        self.prog = prog
        self.consts = consts
        self.lt = lt
        self.operands = operands  # template input node id -> Mem
        self.ranges = ranges
        self.uses = uses
        self.memo: dict = {}
        self.imemo: dict = {}
        self.variant = variant or {}
        self.wrap_ok: set = set()

    # ------------------------------------------------------------ basics
    def _range(self, node):
        return interval(node, self.ranges, self.imemo)

    def op(self, opcode, srcs, unit, dst=None, flags=False, write_mask=None, flush=None, merge_into=None, width=2, note=""):
        out = None
        if merge_into is not None or (dst is None and not flags):
            out = Value(width)
        vop = VOp(opcode, list(srcs), out=out, dsts=[dst] if dst is not None else [], unit=unit,
                  write_mask=write_mask, flush=flush, merge_into=merge_into, note=note)
        if flags:
            vop.flags_out = Value(0, "flags")
        if merge_into is not None:
            out.nofwd = True
        self.prog.add(vop)
        return vop

    @staticmethod
    def _use(x, neg=False):
        if isinstance(x, Value):
            return Use(x, neg=neg)
        if isinstance(x, Use):
            return replace(x, neg=x.neg ^ neg)
        if isinstance(x, Mem):
            return replace(x, neg=x.neg ^ neg)
        raise CompileError(f"bad operand {x!r}")

    def _stage(self, srcs):
        """One read address per memory per expression: copy clashing memory operands to registers."""
        seen = {}
        out = []
        for s in srcs:
            if isinstance(s, Mem):
                pat = (s.addrs, s.wl, s.tind)
                if s.space in seen and seen[s.space] != pat:
                    v = self.op("lpassa", [replace(s, neg=False, ext=False, rnd=False)], "alu").out
                    s = Use(v, neg=s.neg, ext=s.ext, rnd=s.rnd)
                else:
                    seen[s.space] = pat
            out.append(s)
        return out

    @staticmethod
    def _conflicts(srcs, dst):
        if dst is None or dst.space not in ("lm0", "lm1"):
            return False
        return any(isinstance(s, Mem) and s.space == dst.space and s.addrs != dst.addrs for s in srcs)

    @staticmethod
    def _unit(opcode):
        if len(opcode) > 2 and opcode[0] in "dfgh" and opcode[1] in "vm" and opcode[2:5] in ("fma", "mul", "add", "pas"):
            return "mau"
        return "alu"

    def emit(self, opcode, srcs, dst=None, flags=False, write_mask=None, flush=None, unit=None):
        """Emit one expression; returns its result Value (None when written to dst, the VOp with flags)."""
        unit = unit or self._unit(opcode)
        if unit == "mau" and opcode[0] == "d" and opcode[2:5] in ("mul", "fma") and opcode[5:6] not in ("u", "d"):
            return self._double_mul(opcode, srcs, dst, flags, write_mask)
        if unit == "mau" and opcode[0] == "h" and opcode[1] == "v" and not opcode.endswith("r"):
            opcode += "r"
        srcs = self._stage([self._use(s) for s in srcs])
        if self._conflicts(srcs, dst):
            v = self.emit(opcode, srcs, None, unit=unit)
            self.emit("lpassa", [v], dst, write_mask=write_mask)
            return None
        vop = self.op(opcode, srcs, unit, dst=dst, flags=flags, write_mask=write_mask, flush=flush)
        if flags:
            return vop
        return None if dst is not None else vop.out

    def _double_mul(self, opcode, srcs, dst, flags, write_mask):
        kind = opcode[2:5]
        first = self.op(f"dv{kind}u", self._stage([self._use(s) for s in srcs]), "mau")
        return self.emit("dvfmad", list(srcs[:2]) + [first.out], dst, flags, write_mask, unit="mau")

    # ------------------------------------------------------------ operands
    def rep_of(self, node: Node) -> str:
        """Representation a node's value is computed in: 'int', 'float' or 'flags'."""
        if node.ty == "f":
            return "float"
        if node.ty == "b":
            return "flags"
        if node.op == "input":
            return "float" if node.ty == "f" or node.id in self.float_inputs else "int"
        if node.op == "const":
            return "int"
        if node.op in ("trunc", "floor"):
            return "float"
        if node.op in ("mod", "floordiv", "add", "sub", "mul", "select", "max", "min", "sum", "neg", "abs"):
            if any(self.rep_of(a) == "float" for a in node.args if a.ty != "b"):
                return "float"
        return "int"

    def operand(self, node: Node, rep: str | None = None):
        rep = rep or self.rep_of(node)
        if node.op == "input" or (node.op == "const" and node.id in self.operands):
            mem = self.operands[node.id]
            native = "float" if node.ty == "f" or node.id in self.float_inputs else "int"
            if rep == native:
                return mem
            key = (node.id, rep)
            if key not in self.memo:
                self.memo[key] = self.convert(mem, native, rep, node)  # one conversion per input word
            return self.memo[key]
        if node.op == "const":
            return self.consts.scalar(node.value, self.lt, rep)
        key = (node.id, rep)
        hit = self.memo.get(key)
        if hit is not None:
            return hit
        native = self.rep_of(node)
        r = self.convert(self.operand(node, native), native, rep, node) if native != rep else self.compute(node, None)
        self.memo[key] = r
        return r

    def convert(self, x, src: str, dst: str, node: Node):
        if src == dst:
            return x
        r = self._range(node)
        if self.lt.bits != 32:
            raise CompileError(f"{src}->{dst} conversion only for 32-bit lanes")
        if src == "int" and dst == "float":
            if r is None or r[0] < 0 or r[1] >= 1 << 23:
                raise CompileError(f"int->float needs a range within [0, 2^23): {r}")
            magic = self.consts.word32(MAGIC23)
            biased = self.emit("ior", [x, magic])
            return self.emit("fvadd", [biased, self._use(magic, neg=True)])
        if src == "float" and dst == "int":
            return self.emit("fftoi", [x])
        raise CompileError(f"no conversion {src}->{dst}")

    # ------------------------------------------------------------ writing outputs
    def native(self):
        return "float" if self.lt.kind == "float" else "int"

    # ops whose result modulo 2^bits depends only on their operands modulo 2^bits
    WRAP_OPS = {"add", "sum", "sub", "neg", "mul", "shl", "and", "or", "xor", "not"}

    def _wrap_contexts(self, root: Node):
        """Integer nodes whose value is only used modulo 2^bits (they may overflow the lane)."""
        exact, wrap = set(), set()
        for n in reversed(walk([root])):
            if n is root:
                wrap.add(n.id)
            ctx_wrap = n.id in wrap and n.id not in exact and n.op in self.WRAP_OPS and n.ty == "i"
            for a in n.args:
                if ctx_wrap and a.ty == "i":
                    wrap.add(a.id)
                else:
                    exact.add(a.id)
        self.wrap_ok |= {i for i in wrap if i not in exact}
        self.wrap_ok -= exact

    select_in_registers = False  # build deep select chains in a register, then write once

    @staticmethod
    def _select_depth(node):
        d = 0
        while node.op == "select":
            d += 1
            node = node.args[1] if node.args[1].op == "select" else node.args[2]
        return d

    def write(self, node: Node, dst: Mem):
        if self.lt.kind != "float":
            self._wrap_contexts(node)
        rep = self.native()
        if node.op == "select" and self.select_in_registers and self._select_depth(node) >= 3:
            v = self.select(node, None, rep)
            self.emit("lpassa", [v], dst)
        elif node.op == "select":
            self.select(node, dst, rep)
        elif node.op in ("input", "const") or self.rep_of(node) != rep:
            self.emit("lpassa", [self.operand(node, rep)], dst)
        else:
            self.compute(node, dst)

    # ------------------------------------------------------------ rules
    def compute(self, node: Node, dst: Mem | None):
        rep = self.rep_of(node)
        if node.op == "select":
            return self.select(node, dst, rep)
        return self._float(node, dst) if rep == "float" else self._int(node, dst)

    def _check_int(self, node):
        if node.id in self.wrap_ok:
            return
        r = self._range(node)
        if r is None:
            raise CompileError(f"unbounded integer {node.op}")
        lo, hi = r
        bits = self.lt.bits
        ok = (lo >= 0 and hi < (1 << bits)) if self.lt.unsigned else (-(1 << (bits - 1)) <= lo and hi < (1 << (bits - 1)))
        if not ok:
            raise CompileError(f"integer range {r} of {node.op} exceeds {bits}-bit lanes")

    def _int(self, node: Node, dst):
        lt = self.lt
        op, a = node.op, node.args
        if op in ("or", "sum", "add", "xor") and lt.bits in (32, 64) and len(walk([node])) >= 6:
            from . import bitperm

            hit = bitperm.recognize(node, lt.bits)
            if hit is not None:
                leaf, perm = hit
                try:
                    return bitperm.synthesize(self, self.operand(leaf, "int"), perm, lt.bits, dst)
                except CompileError:
                    pass
        self._check_int(node)
        q = lt.iprec
        u = "u" if lt.unsigned else ""
        C = lambda v: self.consts.scalar(v, lt)  # noqa: E731
        if op in ("add", "sum"):
            consts = [t for t in a if t.op == "const"]
            rest = [t for t in a if t.op != "const"]
            c = sum(int(t.value) for t in consts)
            if len(rest) == 1 and c in (1, -1):
                return self.emit(f"{u}{q}{'inc' if c == 1 else 'dec'}", [self.operand(rest[0], "int")], dst)
            vals = [self.operand(t, "int") for t in rest] + ([C(c)] if c else [])
            return self._chain(f"{u}{q}add", vals, dst)
        if op in ("add", "sub") and len(a) == 2:
            # a constant added to bit_length folds into its bias subtraction
            x, y = a if a[1].op == "const" else (a[1], a[0])
            if x.op == "bit_length" and y.op == "const" and (op == "add" or a[1] is y):
                off = int(y.value) if op == "add" else -int(y.value)
                return self._bit_length(x, dst, offset=off)
        if op == "sub":
            x, y = a
            if y.op == "const" and y.value in (1, -1):
                return self.emit(f"{u}{q}{'dec' if y.value == 1 else 'inc'}", [self.operand(x, "int")], dst)
            return self.emit(f"{u}{q}sub", [self.operand(x, "int"), self.operand(y, "int")], dst)
        if op == "neg":
            return self.emit(f"{q}sub", [C(0), self.operand(a[0], "int")], dst)
        if op in ("and", "or", "xor"):
            return self._chain(f"{q}{op}", [self.operand(t, "int") for t in a], dst)
        if op == "not":
            return self.emit(f"{q}not", [self.operand(a[0], "int")], dst)
        if op in ("shl", "shr"):
            x, s = a
            if s.op != "const":
                raise CompileError("variable shift amount")
            if s.value >= lt.bits:
                return self.emit("lpassa", [C(0)], dst)
            name = "lsl" if op == "shl" else "lsr"
            xr = self._range(x) or (0, 0)
            uu = "u" if op == "shr" and (lt.unsigned or xr[0] >= 0) else ""
            return self.emit(f"{uu}{q}{name}", [self.operand(x, "int"), C(s.value)], dst)
        if op in ("max", "min"):
            return self._chain(f"{u}{q}{op}", [self.operand(t, "int") for t in a], dst)
        if op == "abs":
            x = self.operand(a[0], "int")
            if isinstance(dst, Mem) and dst.space != "t" and not dst.tind and self._sign_on_mau():
                # -x into dst, then x where x >= 0 (MAU sign flag; the masked copy may take the
                # L1BM turnaround): one ALU op instead of two
                flags = self.emit("fvpassa", [x], flags=True).flags_out
                self.emit(f"{q}sub", [C(0), x], dst)
                self.emit("lpassa", [x], dst, write_mask=FlagUse(flags))
                return None
            return self.emit(f"{q}max", [x, self.emit(f"{q}sub", [C(0), x])], dst)
        if op == "mul":
            x, y = a
            if y.op != "const":
                x, y = y, x
            if y.op == "const":
                return self._mul_const(x, int(y.value), dst)
            raise CompileError("integer product of two variables")
        if op in ("mod", "floordiv"):
            return self._divmod(node, dst)
        if op == "bit_length":
            return self._bit_length(node, dst)
        if op == "toint":
            if a[0].ty == "b":
                return self._select_values(a[0], 1, 0, dst, "int")
            return self.emit("fftoi", [self.operand(a[0], "float")], dst)
        if op == "trunc":
            return self.emit("fftoi", [self.operand(a[0], "float")], dst)
        raise CompileError(f"no integer rule for {op}")

    def _chain(self, opcode, vals, dst):
        if len(vals) == 1:
            return self.emit("lpassa", [vals[0]], dst) if dst is not None else vals[0]
        acc = vals[0]
        for i, v in enumerate(vals[1:]):
            acc = self.emit(opcode, [acc, v], dst if i == len(vals) - 2 else None)
        return acc

    def _mul_const(self, x: Node, c: int, dst):
        lt, q = self.lt, self.lt.iprec
        C = lambda v: self.consts.scalar(v, lt)  # noqa: E731
        if c == 0:
            return self.emit("lpassa", [C(0)], dst)
        if c == 1:
            return self.emit("lpassa", [self.operand(x, "int")], dst)
        neg = c < 0
        c = abs(c)
        xo = self.operand(x, "int")
        k = c.bit_length()
        if c & (c - 1) == 0:
            r = self.emit(f"{q}lsl", [xo, C(k - 1)], None if neg else dst)
        elif (1 << k) - 1 == c:
            r = self.emit(f"{q}sub", [self.emit(f"{q}lsl", [xo, C(k)]), xo], None if neg else dst)
        else:
            bits = [i for i in range(k) if c >> i & 1]
            terms = [xo if b == 0 else self.emit(f"{q}lsl", [xo, C(b)]) for b in bits]
            r = self._chain(f"{q}add", terms, None if neg else dst)
        if neg:
            return self.emit(f"{q}sub", [C(0), r], dst)
        return r

    def _divmod(self, node: Node, dst):
        """x // d or x % d for a constant d > 0 through exact f32 arithmetic."""
        x, d = node.args
        if d.op != "const" or int(d.value) <= 0:
            raise CompileError("division by a non-constant")
        dv = int(d.value)
        r = self._range(x)
        if r is None or r[0] < 0 or r[1] >= 1 << 22 or self.lt.bits != 32:
            raise CompileError(f"division range {r}")
        if r[1] < dv:
            return self.emit("lpassa", [self.operand(x, "int") if node.op == "mod" else self.consts.scalar(0, self.lt)], dst) if dst is not None else (self.operand(x, "int") if node.op == "mod" else self.consts.scalar(0, self.lt))
        rf = quotient_fraction(dv, int(r[1]))
        xf = self.operand(x, "float")
        qf = self.emit("ffloor", [self.emit("fvmul", [xf, self.consts.scalar(rf, self.lt, "float")])])
        if node.op == "floordiv":
            return self.emit("fftoi", [qf], dst)
        rem = self.emit("fvfma", [qf, self._use(self.consts.scalar(float(dv), self.lt, "float"), neg=True), xf])
        return self.emit("fftoi", [rem], dst)

    def _bit_length(self, node: Node, dst, offset=0):
        """bit_length(x) + offset: the float exponent of x minus the bias, in one subtraction."""
        x = node.args[0]
        r = self._range(x)
        if r is None or r[0] < 1 or r[1] >= 1 << 23 or self.lt.bits != 32:
            raise CompileError(f"bit_length range {r}")
        xf = self.operand(x, "float")
        e = self.emit("ilsr", [xf, self.consts.scalar(23, self.lt)])
        return self.emit("isub", [e, self.consts.scalar(126 - offset, self.lt)], dst)

    # ------------------------------------------------------------ floats
    fold = False  # reassociate affine chains (only when the output has an error budget)
    float_inputs = frozenset()  # input positions whose operands already hold exact float copies of small integers

    def _affine(self, node: Node, depth=0):
        """(a, t, b, ops) with node = a*t + b for one non-constant subexpression t, or None."""
        if node.op == "const" and not isinstance(node.value, bool):
            return (0.0, None, float(node.value), 0)
        if node.ty != "f" or depth > 32:
            return (1.0, node, 0.0, 0)
        op, args = node.op, node.args
        if op in ("add", "sum", "sub"):
            parts = [self._affine(x, depth + 1) for x in args]
            if any(p is None for p in parts):
                return (1.0, node, 0.0, 0)
            ts = {id(p[1]): p[1] for p in parts if p[1] is not None}
            if len(ts) > 1:
                return (1.0, node, 0.0, 0)
            sign = [1.0] * len(parts) if op != "sub" else [1.0, -1.0]
            t = next(iter(ts.values()), None)
            return (sum(sg * p[0] for sg, p in zip(sign, parts)), t, sum(sg * p[2] for sg, p in zip(sign, parts)),
                    sum(p[3] for p in parts) + len(parts) - 1)
        if op == "mul" and len(args) == 2:
            pa, pb = self._affine(args[0], depth + 1), self._affine(args[1], depth + 1)
            for x, c in ((pa, pb), (pb, pa)):
                if c[1] is None and x[1] is not None:
                    return (x[0] * c[2], x[1], x[2] * c[2], x[3] + 1)
            return (1.0, node, 0.0, 0)
        if op == "neg":
            q = self._affine(args[0], depth + 1)
            return (-q[0], q[1], -q[2], q[3] + 1)
        return (1.0, node, 0.0, 0)

    def _float(self, node: Node, dst):
        op, a = node.op, node.args
        lt = self.lt
        p = lt.fprec if lt.kind == "float" else "f"
        if self.fold and p == "f" and op in ("add", "sum", "sub", "mul", "neg"):
            ca, t, cb, n_ops = self._affine(node)
            if t is not None and t is not node and n_ops >= 2:
                x = self.operand(t, "float")
                av = self.consts.scalar(ca, lt, "float")
                if cb == 0:
                    return self.emit("fvmul", [x, av], dst)
                return self.emit("fvfma", [x, av, self.consts.scalar(cb, lt, "float")], dst)
        if op in ("trunc", "floor"):
            if op == "trunc":
                lo = (self._range(a[0]) or (0, 0))[0]
                if lo < 0:
                    raise CompileError("trunc of a possibly negative value")
            return self.emit(f"{p}floor", [self.operand(a[0], "float")], dst)
        if op in ("add", "sum", "sub"):
            terms = [(a[0], False), (a[1], True)] if op == "sub" else [(t, False) for t in a]
            return self._fadd_terms(terms, dst, p)
        if op == "mul":
            if len(a) != 2:
                raise CompileError("n-ary float product")
            return self.emit(f"{p}vmul", [self.operand(a[0], "float"), self.operand(a[1], "float")], dst)
        if op == "neg":
            return self.emit(f"{p}vpassa", [self._use(self.operand(a[0], "float"), neg=True)], dst)
        if op == "max" and len(a) == 2 and any(self._zero(t) for t in a):
            v = self.operand(next(t for t in a if not self._zero(t)), "float")
            return self.emit(f"{p}relu", [v, v], dst)
        if op in ("max", "min"):
            return self._chain(f"{p}{op}", [self.operand(t, "float") for t in a], dst)
        if op == "abs":
            q = {"d": "l", "f": "i", "h": "s"}[p]
            m = {"d": lambda: self.consts.word64(0x7FFFFFFFFFFFFFFF), "f": lambda: self.consts.word32(0x7FFFFFFF), "h": lambda: self.consts.word16(0x7FFF)}[p]()
            return self.emit(f"{q}and", [self.operand(a[0], "float"), m], dst)
        if op in ("mod", "floordiv"):
            return self._fdivmod(node, dst)
        if op == "div":
            return self._fdiv(node, dst)
        if op == "exp":
            return self._fexp(node, dst)
        if op == "tofloat":
            x = self.operand(a[0], "float")
            return self.emit("lpassa", [x], dst) if dst is not None else x
        raise CompileError(f"no float rule for {op}")

    # ------------------------------------------------------------ approximations under the error budget
    def _fdiv(self, node: Node, dst):
        """a / b = a * (1/b); 1/b from rsqrt(b)^2 refined by Newton steps (count is a search knob)."""
        if self.lt.fprec != "f":
            raise CompileError("division only for f32")
        a, b = node.args
        bo = self.operand(b, "float")
        steps = int(self.variant.get("newton", 2))
        r = self.emit("frsqrt", [bo])
        y = self.emit("fvmul", [r, r])
        one = self.consts.scalar(1.0, self.lt, "float")
        recip = a.op == "const" and a.value == 1.0
        for k in range(steps):
            e = self.emit("fvfma", [self._use(bo, neg=True), y, one])  # 1 - b*y
            y = self.emit("fvfma", [y, e, y], dst if recip and k == steps - 1 else None)  # y + y*e
        if recip:
            if steps == 0 and dst is not None:
                return self.emit("lpassa", [y], dst)
            return y
        return self.emit("fvmul", [self.operand(a, "float"), y], dst)

    def _fexp(self, node: Node, dst):
        """exp(x) = 2^n * p(r), x = n ln2 + r; the polynomial degree is a search knob."""
        if self.lt.fprec != "f":
            raise CompileError("exp only for f32")
        import numpy as np

        x = node.args[0]
        lo, hi = self._float_bounds(x)
        degree = int(self.variant.get("exp_degree", 5))
        xo = self.operand(x, "float")
        if lo < -87.0:
            xo = self.emit("fmax", [xo, self.consts.scalar(-87.0, self.lt, "float")])
        inv_ln2 = f32(1.0 / math.log(2.0))
        magic = f32(1.5 * 2 ** 23)
        t = self.emit("fvfma", [xo, self.consts.scalar(inv_ln2, self.lt, "float"), self.consts.scalar(magic, self.lt, "float")])
        nf = self.emit("fvadd", [t, self._use(self.consts.scalar(magic, self.lt, "float"), neg=True)])
        ln2_hi = f32(math.log(2.0))
        ln2_lo = f32(math.log(2.0) - ln2_hi)
        r = self.emit("fvfma", [nf, self._use(self.consts.scalar(ln2_hi, self.lt, "float"), neg=True), xo])
        if degree >= 4:
            r = self.emit("fvfma", [nf, self._use(self.consts.scalar(ln2_lo, self.lt, "float"), neg=True), r])
        coeffs = exp_coefficients(degree)
        acc = self.consts.scalar(coeffs[-1], self.lt, "float")
        for c in reversed(coeffs[:-1]):
            acc = self.emit("fvfma", [acc, r, self.consts.scalar(c, self.lt, "float")])
        scale = self.emit("ilsl", [t, self.consts.scalar(23, LaneType("int", 32))])
        return self.emit("iadd", [acc, scale], dst)

    def _float_bounds(self, node: Node):
        if node.op == "input":
            rng = self.ranges.get(node.value[0])
            if rng:
                return float(rng[0]), float(rng[1])
        r = self._range(node)
        if r:
            return float(r[0]), float(r[1])
        return -1e30, 1e30

    def _fdivmod(self, node: Node, dst):
        x, d = node.args
        if d.op != "const" or d.value <= 0 or node.ty == "f":
            raise CompileError("float-form division needs integer operands and a constant divisor")
        dv = int(d.value)
        r = self._range(x)
        if r is None or r[0] < 0 or r[1] >= 1 << 22:
            raise CompileError(f"division range {r}")
        xf = self.operand(x, "float")
        if r[1] < dv:
            res = xf if node.op == "mod" else self.consts.scalar(0.0, self.lt, "float")
            return self.emit("lpassa", [res], dst) if dst is not None else res
        rf = quotient_fraction(dv, int(r[1]))
        qf = self.emit("ffloor", [self.emit("fvmul", [xf, self.consts.scalar(rf, self.lt, "float")])])
        if node.op == "floordiv":
            return self.emit("lpassa", [qf], dst) if dst is not None else qf
        return self.emit("fvfma", [qf, self._use(self.consts.scalar(float(dv), self.lt, "float"), neg=True), xf], dst)

    def _fadd_terms(self, terms, dst, p):
        prod = None
        for i, (t, negt) in enumerate(terms):
            if t.op == "mul" and len(t.args) == 2 and self.uses.get(t.id, 1) == 1 and (t.id, "float") not in self.memo:
                prod = i
                break
        rest = [x for i, x in enumerate(terms) if i != prod]
        if prod is not None and rest:
            t, negt = terms[prod]
            c, negc = rest[0]
            x, y = t.args
            ops = [self.operand(x, "float"), self._use(self.operand(y, "float"), neg=negt), self._use(self.operand(c, "float"), neg=negc)]
            acc = self.emit(f"{p}vfma", ops, dst if len(rest) == 1 else None)
            rest = rest[1:]
        else:
            if len(rest) == 1:
                t0, n0 = rest[0]
                return self.emit(f"{p}vpassa", [self._use(self.operand(t0, "float"), neg=n0)], dst)
            (t0, n0), (t1, n1) = rest[0], rest[1]
            acc = self.emit(f"{p}vadd", [self._use(self.operand(t0, "float"), neg=n0), self._use(self.operand(t1, "float"), neg=n1)], dst if len(rest) == 2 else None)
            rest = rest[2:]
        for i, (t, n) in enumerate(rest):
            acc = self.emit(f"{p}vadd", [acc, self._use(self.operand(t, "float"), neg=n)], dst if i == len(rest) - 1 else None)
        return acc

    # ------------------------------------------------------------ flags and selects
    def flags(self, cond: Node):
        """Ops producing mask flags; returns (flag value, polarity): flag 1 means cond == polarity."""
        key = ("flags", cond.id)
        if key not in self.memo:
            self.memo[key] = self._flags(cond)
        return self.memo[key]

    def _flags(self, cond: Node):
        op = cond.op
        if op in ("ge", "le", "gt", "lt"):
            x, y = cond.args
            if op in ("le", "gt"):
                x, y = y, x
            positive = op in ("ge", "le")
            floaty = "float" in (self.rep_of(x), self.rep_of(y))
            if floaty:
                p = self.lt.fprec if self.lt.kind == "float" else "f"
                vop = self.emit(f"{p}vadd", [self.operand(x, "float"), self._use(self.operand(y, "float"), neg=True)], flags=True)
                return vop.flags_out, positive
            q, u = self.lt.iprec, "u" if self.lt.unsigned else ""
            if self._zero(y) and self._sign_on_mau():
                # the sign of a 32-bit integer is the sign bit of its pattern read as f32: a MAU
                # copy sets the flag where it is clear (leaves the ALU free)
                return self.emit("fvpassa", [self.operand(x, "int")], flags=True).flags_out, positive
            vop = self.emit(f"{u}{q}sub", [self.operand(x, "int"), self.operand(y, "int")], flags=True)
            return vop.flags_out, positive
        if op in ("eq", "ne"):
            x, y = cond.args
            for a, b in ((x, y), (y, x)):
                if self._zero(b) and a.op == "mod" and a.args[1].op == "const" and int(a.args[1].value) > 1:
                    fl = self._divisible_flags(a.args[0], int(a.args[1].value))
                    if fl is not None:
                        return fl, op == "eq"
            floaty = "float" in (self.rep_of(x), self.rep_of(y))
            rep = "float" if floaty else "int"
            fp = self.lt.fprec if self.lt.kind == "float" else "f"
            q = self.lt.iprec if rep == "int" else {"d": "l", "f": "i", "h": "s"}[fp]
            vop = self.emit(f"{q}xor", [self.operand(x, rep), self.operand(y, rep)], flags=True)
            return vop.flags_out, op == "eq"
        if op == "lnot":
            f, pol = self.flags(cond.args[0])
            return f, not pol
        raise CompileError(f"no flag rule for {op}")

    def _sign_on_mau(self):
        return self.lt.bits == 32 and self.lt.kind == "int" and not self.lt.unsigned

    def _divisible_flags(self, x: Node, m: int):
        """Flags (1 where m | x) for an integer x of a small known range: x & (m - 1) for a power
        of two; for odd m the mantissa bits of f32(x * r): a multiple gives the quotient exactly,
        anything else the repeating binary expansion of k/m below it. The bit window is found by
        trying every x of the range."""
        import numpy as np

        r = self._range(x)
        if self.lt.bits != 32 or r is None or r[0] < 0 or r[1] >= 1 << 16:
            return None
        lo, hi = int(r[0]), int(r[1])
        if m & (m - 1) == 0:
            return self.emit("iand", [self.operand(x, "int"), self.consts.scalar(m - 1, self.lt)], flags=True).flags_out
        if m % 2 == 0:
            return None
        ints = np.arange(lo, hi + 1)
        div = ints % m == 0
        xs = ints.astype(np.float32)
        r0 = np.float32(1.0 / m)
        found = []
        for rv in (r0, np.nextafter(r0, np.float32(1)), np.nextafter(r0, np.float32(0))):
            bits = (xs * rv).astype(np.float32).view(np.uint32)
            for width in (4, 6, 8):
                for pos in range(0, 23 - width + 1):
                    mask = ((1 << width) - 1) << pos
                    if np.array_equal((bits & mask) == 0, div):
                        found.append((rv, mask))
        if not found:
            return None
        # a mask another test already materialized costs no immediate; else a middle window, which
        # tends to suit other moduli too
        rv, mask = min(found, key=lambda f: (("w32", f[1]) not in self.consts.cache, abs((f[1] & -f[1]).bit_length() - 4)))
        p = self.emit("fvmul", [self.operand(x, "float"), self.consts.word32(int(np.float32(rv).view(np.uint32)), repr(float(rv)))])
        return self.emit("iand", [p, self.consts.word32(mask)], flags=True).flags_out

    def _imm_bits(self, x, dst, rep):
        """The 32-bit immediate writing constant x straight into dst, or None (LM0, T, 64-bit halves)."""
        if isinstance(x, Node):
            if x.op != "const" or isinstance(x.value, bool):
                return None
            x = x.value
        if not isinstance(dst, Mem) or dst.space in ("lm0", "t") or dst.tind or self.lt.bits not in (32, 64):
            return None
        if rep == "float":
            if self.lt.bits != 32:
                return None
            return f32_bits(float(x))
        v = int(x)
        if self.lt.bits == 64:
            v &= (1 << 64) - 1
            if v >> 32 != v & 0xFFFFFFFF:
                return None
            return v & 0xFFFFFFFF
        return v & 0xFFFFFFFF

    def select(self, node: Node, dst, rep):
        c, x, y = node.args
        r = self._relu_select(c, x, y, dst, rep)
        if r is not False:
            return r
        return self._select_values(c, x, y, dst, rep)

    @staticmethod
    def _zero_value(v):
        if isinstance(v, Node):
            return v.op == "const" and not isinstance(v.value, bool) and v.value == 0
        return not isinstance(v, bool) and isinstance(v, (int, float)) and v == 0

    @staticmethod
    def _zero(n):
        return isinstance(n, Node) and n.op == "const" and not isinstance(n.value, bool) and n.value == 0

    def _relu_select(self, c, x, y, dst, rep):
        """select(t >= 0, v, 0) as relu(t, v): the ALU passes v where the sign bit of t is clear
        (and -0 elsewhere, numerically zero). t = a - b for a comparison of a and b."""
        if rep != "float" or self.lt.kind != "float" or c.op not in ("ge", "le", "lt", "gt"):
            return False
        a, b = c.args
        if "float" not in (self.rep_of(a), self.rep_of(b)):
            return False
        if c.op in ("ge", "le"):
            if self._zero(y):
                keep = x
            elif self._zero(x):
                c_op = {"ge": "lt", "le": "gt"}[c.op]
                return self._relu_strict(c_op, a, b, y, dst)
            else:
                return False
            t_pos, t_neg = (a, b) if c.op == "ge" else (b, a)  # keep where t_pos - t_neg >= 0
        else:
            # select(a < b, x, y): keep y where a >= b
            if self._zero(x):
                keep = y
                t_pos, t_neg = (a, b) if c.op == "lt" else (b, a)
            else:
                return False
        p = self.lt.fprec
        if self._zero(t_neg):
            t = self.operand(t_pos, "float")
        else:
            t = self.emit(f"{p}vadd", [self.operand(t_pos, "float"), self._use(self.operand(t_neg, "float"), neg=True)])
        return self.emit(f"{p}relu", [t, self.operand(keep, "float")], dst)

    def _relu_strict(self, op, a, b, y, dst):
        return False

    def _select_values(self, c, x, y, dst, rep):
        flags, pol = self.flags(c)
        # one branch zero, kept where the flag is 1: a single op with a zero-flush mask
        keep = x if pol and self._zero_value(y) else (y if not pol and self._zero_value(x) else None)
        if keep is not None:
            src = self._value_operand(keep, rep)
            if dst is not None:
                self.emit("lpassa", [src], dst, flush=FlagUse(flags))
                return None
            return self.emit("lpassa", [src], flush=FlagUse(flags))
        first, second = (y, x) if pol else (x, y)
        if dst is not None:
            self._write_operand(first, dst, rep)
            bits = self._imm_bits(second, dst, rep)
            if bits is not None:
                # a constant goes straight into the output with a masked immediate
                self.prog.add(VOp("imm", [Imm("ui", "0x%08X" % bits)], dsts=[dst], unit="alu", write_mask=FlagUse(flags)))
                return None
            self.emit("lpassa", [self._value_operand(second, rep)], dst, write_mask=FlagUse(flags))
            return None
        src2 = self._value_operand(second, rep)
        base = self._value_operand(first, rep)
        if not (isinstance(base, Value) and base.home is None and not getattr(base, "nofwd", False)):
            base = self.emit("lpassa", [base])
        vop = self.op("lpassa", self._stage([self._use(src2)]), "alu", write_mask=FlagUse(flags), merge_into=base)
        return vop.out

    def _value_operand(self, x, rep):
        if isinstance(x, Node):
            return self.operand(x, rep)
        return self.consts.scalar(x, self.lt, rep)

    def _write_operand(self, x, dst, rep):
        bits = self._imm_bits(x, dst, rep)
        if bits is not None:
            self.prog.add(VOp("imm", [Imm("ui", "0x%08X" % bits)], dsts=[dst], unit="alu"))
            return
        if isinstance(x, Node):
            if x.op == "select":
                self.select(x, dst, rep)
            elif x.op in ("input", "const") or self.rep_of(x) != rep:
                self.emit("lpassa", [self.operand(x, rep)], dst)
            else:
                self.compute(x, dst)
        else:
            self.emit("lpassa", [self.consts.scalar(x, self.lt, rep)], dst)


def quotient_fraction(d: int, hi: int) -> float:
    """An f32 near 1/d with floor(x * r) == x // d for 0 <= x <= hi under any f32 rounding."""
    r = f32(1.0 / d)
    bits = f32_bits(r)
    for k in range(0, 64):
        c = struct.unpack(">f", struct.pack(">I", bits + k))[0]
        ok = True
        for x in range(0, hi + 1):
            p = x * c
            err = abs(p) * 2.0 ** -23
            if math.floor(p - err) != x // d or math.floor(p + err) != x // d:
                ok = False
                break
        if ok:
            return c
    raise CompileError(f"no f32 reciprocal for division by {d} up to {hi}")


def exp_coefficients(degree: int) -> list:
    """f32 coefficients of a near-minimax polynomial for exp(r), |r| <= ln2/2 (low degree first)."""
    import numpy as np

    h = math.log(2.0) / 2
    k = np.arange(degree + 1)
    # Chebyshev nodes give a near-minimax interpolant
    nodes = np.cos((2 * np.arange(4 * (degree + 1)) + 1) * np.pi / (8 * (degree + 1))) * h
    A = np.vander(nodes, degree + 1, increasing=True)
    coef, *_ = np.linalg.lstsq(A, np.exp(nodes), rcond=None)
    return [f32(float(c)) for c in coef]


FIXED_OF_AXIS = {"PE": "subpeid", "MAB": "mabid", "L1B": "l1bid", "L2B": "l2bid"}


def coordinate_vector(prog: VProgram, consts: Constants, lt: LaneType, c0: int, c_lane: int, coefs: dict, *, as_float: bool) -> Value:
    """c0 + c_lane*lane + sum(coef*coordinate): a per-PE constant vector built from the fixed
    operands ($subpeid, $mabid, ...), homed in GRF1 like the other constants."""
    from .machine import Fixed

    if lt.bits != 32:
        raise CompileError("location-dependent constants only for 32-bit lanes")
    terms = dict((a, k) for a, k in coefs.items() if k)
    if terms.get("PE") and terms.get("MAB") == 4 * terms["PE"]:
        terms["PEID"] = terms.pop("PE")
        terms.pop("MAB")
    lo = c0 + min(0, c_lane) + sum(min(0, k * (3 if a == "PE" else 15 if a == "MAB" else 63 if a == "PEID" else 7)) for a, k in terms.items())
    hi = c0 + max(0, c_lane) + sum(max(0, k * (3 if a == "PE" else 15 if a == "MAB" else 63 if a == "PEID" else 7)) for a, k in terms.items())
    if as_float and not (0 <= lo and hi < 1 << 23):
        raise CompileError("location-dependent float constant out of the exact integer range")
    mask = 0xFFFFFFFF
    acc = consts.word64(((c0 & mask) << 32) | ((c0 + c_lane) & mask))
    ops = []

    def add(opcode, srcs):
        op = VOp(opcode, srcs, out=Value(2), unit="alu", note="coordinate constant")
        prog.add(op)
        ops.append(op)
        return op.out

    for axis, k in terms.items():
        fixed = Fixed("peid" if axis == "PEID" else FIXED_OF_AXIS[axis])
        mag = abs(k)
        if mag & (mag - 1) == 0:
            parts = [mag.bit_length() - 1]
        else:
            bits = [i for i in range(32) if mag >> i & 1]
            if len(bits) > 2:
                raise CompileError(f"coordinate coefficient {k} needs too many shifts")
            parts = bits
        for sh in parts:
            if sh == 0 and k > 0:
                acc = add("iadd", [fixed, Use(acc)])
                continue
            t = add("ilsl", [fixed, Use(consts.word32(sh))]) if sh else add("ipassa", [fixed])
            acc = add("iadd" if k > 0 else "isub", [Use(acc), Use(t)] if k < 0 else [Use(t), Use(acc)])
    if as_float:
        magic = consts.word32(MAGIC23)
        biased = add("ior", [Use(acc), Use(magic)])
        acc = add("fvadd", [Use(biased), Use(magic, neg=True)])
        ops[-1].unit = "mau"
    if not ops:
        return acc
    bank, home_addr = consts._home()
    home = Mem(bank, 2, (home_addr,) * 4)
    v = Value(2, "coord", home=home)
    last = ops[-1]
    last.out = v
    last.dsts = [home]
    return v


def exchange_value(prog: VProgram, consts: Constants, mem: Mem, deltas: tuple) -> Value:
    """The operand as read by PE (p + deltas[p]) % 4 of the MAB, for every PE p: rotations
    across the PEs (msl: from the previous PE, msr: from the next) merged under PE masks."""
    from .machine import Fixed

    def rot(v, d):
        src = Use(v) if isinstance(v, Value) else v
        if d == 1:
            op = VOp("msr", [src], out=Value(2), unit="alu", note="exchange")
            prog.add(op)
            return op.out
        if d == 3:
            op = VOp("msl", [src], out=Value(2), unit="alu", note="exchange")
            prog.add(op)
            return op.out
        if d == 2:
            return rot(rot(v, 3), 3)
        op = VOp("lpassa", [src], out=Value(2), unit="alu", note="exchange")
        prog.add(op)
        return op.out

    groups = {}
    for p, d in enumerate(deltas):
        groups.setdefault(d, []).append(p)
    order = sorted(groups, key=lambda d: -len(groups[d]))
    base = rot(mem, order[0])
    if len(order) == 1:
        return base
    cur = base
    for d in order[1:]:
        pes = groups[d]
        val = rot(mem, d)
        flags = Value(0, "flags")
        if sorted(pes) in ([0, 2], [1, 3]) and len(order) == 2:
            # parity: (subpeid & 1) == 0 sets the flag on even PEs
            prog.add(VOp("iand", [Fixed("subpeid"), Use(consts.word32(1))], out=Value(2), flags_out=flags, unit="alu", note="exchange"))
            if pes == [1, 3]:
                merged = VOp("lpassa", [Use(cur)], out=Value(2), unit="alu", write_mask=FlagUse(flags), merge_into=val, note="exchange")
                merged.out.nofwd = True
                prog.add(merged)
                cur = merged.out
                continue
            merged = VOp("lpassa", [Use(val)], out=Value(2), unit="alu", write_mask=FlagUse(flags), merge_into=cur, note="exchange")
            merged.out.nofwd = True
            prog.add(merged)
            cur = merged.out
            continue
        for p in pes:
            flags = Value(0, "flags")
            prog.add(VOp("ixor", [Fixed("subpeid"), Use(consts.word32(p))], out=Value(2), flags_out=flags, unit="alu", note="exchange"))
            merged = VOp("lpassa", [Use(val)], out=Value(2), unit="alu", write_mask=FlagUse(flags), merge_into=cur, note="exchange")
            merged.out.nofwd = True
            prog.add(merged)
            cur = merged.out
    return cur
