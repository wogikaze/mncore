"""Scalar dataflow IR produced by tracing an ordinary Python kernel.

Nodes are hash-consed within a `Graph`, so structurally equal expressions are
the same object. Types: "i" (Python int, unbounded), "f" (real number,
evaluated in binary64 by the reference), "b" (bool).
"""

from __future__ import annotations

import math
import operator
from dataclasses import dataclass, field

from .errors import CompileError


class Node:
    __slots__ = ("op", "args", "value", "ty", "id", "shape")

    def __init__(self, op, args, value, ty, key, ident):
        self.op = op
        self.args = args
        self.value = value
        self.ty = ty
        self.id = ident
        # structural hash that ignores which element an input is (only its tensor)
        if op == "input":
            self.shape = hash(("input", value[0], ty))
        elif op == "const":
            self.shape = hash(("const", type(value).__name__, value))
        else:
            self.shape = hash((op, ty) + tuple(a.shape for a in args))

    def __hash__(self):
        return self.id

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        if self.op == "const":
            return repr(self.value)
        if self.op == "input":
            return f"{self.value[0]}{list(self.value[1])}"
        return f"{self.op}({', '.join(map(repr, self.args))})"


# op -> (arity, result type rule)
INT_OPS = {"add", "sub", "mul", "floordiv", "mod", "neg", "abs", "and", "or", "xor", "not", "shl", "shr", "min", "max", "bit_length", "pow"}
FLOAT_OPS = {"add", "sub", "mul", "div", "neg", "abs", "min", "max", "exp", "log", "sqrt", "floor", "pow", "mod", "floordiv"}
COMPARE = {"lt", "le", "gt", "ge", "eq", "ne"}


def _py(op):
    return {
        "add": operator.add,
        "sub": operator.sub,
        "mul": operator.mul,
        "div": operator.truediv,
        "floordiv": operator.floordiv,
        "mod": operator.mod,
        "and": operator.and_,
        "or": operator.or_,
        "xor": operator.xor,
        "shl": operator.lshift,
        "shr": operator.rshift,
        "lt": operator.lt,
        "le": operator.le,
        "gt": operator.gt,
        "ge": operator.ge,
        "eq": operator.eq,
        "ne": operator.ne,
        "min": min,
        "max": max,
        "pow": operator.pow,
    }[op]


def evaluate_op(op, args, ty):
    """Concrete semantics, identical to running the Python source."""
    if op in ("neg",):
        return -args[0]
    if op == "abs":
        return abs(args[0])
    if op == "not":
        return ~args[0]
    if op == "lnot":
        return not args[0]
    if op == "sum":
        total = args[0]
        for a in args[1:]:
            total = total + a
        return total
    if op == "bit_length":
        return int(args[0]).bit_length()
    if op == "exp":
        return math.exp(args[0])
    if op == "log":
        return math.log(args[0])
    if op == "sqrt":
        return math.sqrt(args[0])
    if op == "floor":
        return math.floor(args[0])
    if op == "trunc":
        return int(args[0])
    if op == "tofloat":
        return float(args[0])
    if op == "toint":
        return int(args[0])
    if op == "select":
        return args[1] if args[0] else args[2]
    if op == "gather":
        return args[1 + args[0]]
    if op == "land":
        return all(bool(a) for a in args)
    if op == "lor":
        return any(bool(a) for a in args)
    if op in ("min", "max"):
        return min(args) if op == "min" else max(args)
    return _py(op)(*args)


@dataclass
class Graph:
    nodes: dict = field(default_factory=dict)
    order: list = field(default_factory=list)

    def make(self, op, args=(), value=None, ty="i"):
        # one flat tuple per node (memory: kernels can trace millions of nodes)
        key = (op, value if op in ("const", "input") else None, ty, *(a.id for a in args))
        node = self.nodes.get(key)
        if node is None:
            node = Node(op, tuple(args), value, ty, key, len(self.order))
            self.nodes[key] = node
            self.order.append(node)
        return node

    def const(self, value):
        if isinstance(value, bool):
            return self.make("const", value=value, ty="b")
        if isinstance(value, int):
            return self.make("const", value=value, ty="i")
        if isinstance(value, float):
            if math.isnan(value):
                raise CompileError("NaN constant in kernel")
            return self.make("const", value=value, ty="f")
        raise CompileError(f"Unsupported constant {value!r}")

    def input(self, tensor, index, ty):
        return self.make("input", value=(tensor, tuple(index)), ty=ty)

    def apply(self, op, *args):
        """Build a node, folding constants and trivial identities."""
        if all(a.op == "const" for a in args):
            result = evaluate_op(op, [a.value for a in args], None)
            if isinstance(result, float) and (math.isinf(result) or math.isnan(result)):
                if math.isnan(result):
                    raise CompileError("NaN in constant folding")
            return self.const(result)
        ty = result_type(op, [a.ty for a in args])
        simplified = simplify(self, op, args, ty)
        if simplified is not None:
            return simplified
        if op in ("add", "mul", "and", "or", "xor", "min", "max", "eq", "ne", "land", "lor"):
            args = tuple(sorted(args, key=lambda a: (a.op == "const", a.shape, a.id)))
        return self.make(op, tuple(args), ty=ty)


def result_type(op, tys):
    if op in COMPARE or op in ("land", "lor", "lnot"):
        return "b"
    if op == "select":
        a, b = tys[1], tys[2]
        if "f" in (a, b):
            return "f"
        return "i" if "i" in (a, b) else "b"
    if op in ("div", "exp", "log", "sqrt", "tofloat"):
        return "f"
    if op in ("trunc", "toint", "bit_length", "floor"):
        return "i" if op != "floor" or tys[0] != "f" else "i"
    if op in ("and", "or", "xor") and all(t == "b" for t in tys):
        return "b"
    if op in ("neg", "abs", "not"):
        return "f" if tys[0] == "f" else "i"
    if "f" in tys:
        return "f"
    return "i"


def _is(node, value):
    return node.op == "const" and node.value == value and type(node.value) is not bool or (
        node.op == "const" and isinstance(node.value, bool) and node.value == value and isinstance(value, bool)
    )


def simplify(g: Graph, op, args, ty):
    if op in ("add", "sub") and len(args) == 2:
        a, b = args
        if b.op == "const" and b.value == 0 and (ty != "f" or a.ty == "f"):
            return a
        if op == "add" and a.op == "const" and a.value == 0 and (ty != "f" or b.ty == "f"):
            return b
    if op == "mul" and len(args) == 2:
        a, b = args
        for x, y in ((a, b), (b, a)):
            if x.op == "const" and x.value == 1 and (ty != "f" or y.ty == "f"):
                return y
            if x.op == "const" and x.value == 0 and ty == "i":
                return g.const(0)
    if op in ("and",) and len(args) == 2 and ty == "i":
        a, b = args
        for x, y in ((a, b), (b, a)):
            if x.op == "const" and x.value == 0:
                return g.const(0)
    if op in ("or", "xor") and len(args) == 2 and ty == "i":
        a, b = args
        for x, y in ((a, b), (b, a)):
            if x.op == "const" and x.value == 0:
                return y
    if op in ("shl", "shr") and args[1].op == "const" and args[1].value == 0:
        return args[0]
    if op == "select":
        c, a, b = args
        if c.op == "const":
            return a if c.value else b
        if a is b:
            return a
    return None


def walk(roots):
    """Nodes reachable from `roots` in dependency order."""
    seen = set()
    out = []
    stack = [(r, False) for r in reversed(list(roots))]
    while stack:
        node, expanded = stack.pop()
        if node.id in seen:
            continue
        if expanded:
            seen.add(node.id)
            out.append(node)
            continue
        stack.append((node, True))
        for arg in reversed(node.args):
            if arg.id not in seen:
                stack.append((arg, False))
    return out


def evaluate(roots, env):
    """Evaluate nodes concretely. `env` maps (tensor, index) to Python values."""
    values = {}
    for node in walk(roots):
        if node.op == "const":
            values[node.id] = node.value
        elif node.op == "input":
            values[node.id] = env[node.value]
        else:
            values[node.id] = evaluate_op(node.op, [values[a.id] for a in node.args], node.ty)
    return [values[r.id] for r in roots]
