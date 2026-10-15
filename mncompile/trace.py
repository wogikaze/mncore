"""Trace an ordinary pure Python kernel into the scalar IR.

The kernel runs on symbolic values. Conditional expressions become `select`
nodes, and branches on symbolic values inside called Python functions (for
example `colorsys.hsv_to_rgb`) are explored path by path and merged into
selects. Loops with concrete trip counts unroll. Nothing here knows about any
particular problem.
"""

from __future__ import annotations

import ast
import builtins
import functools
import inspect
import math
import textwrap
import threading
import types

from .errors import CompileError
from .ir import Graph, Node
from .strsym import Cat, Concat, ConcatStr, Dec, Sel, to_strval

_state = threading.local()


def _graph() -> Graph:
    graph = getattr(_state, "graph", None)
    if graph is None:
        raise CompileError("Symbolic value used outside tracing")
    return graph


class _NeedDecision(Exception):
    def __init__(self, cond):
        self.cond = cond


class _Recorder:
    def __init__(self, prefix):
        self.prefix = prefix
        self.depth = 0

    def decide(self, cond: "Sym") -> bool:
        if self.depth < len(self.prefix):
            choice = self.prefix[self.depth]
            self.depth += 1
            return choice
        raise _NeedDecision(cond)


def lift(value):
    if isinstance(value, Sym):
        return value.node
    if isinstance(value, (bool, int, float)):
        return _graph().const(value)
    raise CompileError(f"Cannot use {type(value).__name__} in symbolic arithmetic")


def wrap(node: Node):
    if node.op == "const":
        return node.value
    return Sym(node)


def _apply(op, *values):
    return wrap(_graph().apply(op, *(lift(v) for v in values)))


class Sym:
    __slots__ = ("node",)

    def __init__(self, node: Node):
        self.node = node

    def __repr__(self):
        return f"Sym({self.node!r})"

    # arithmetic
    def __add__(self, o): return _apply("add", self, o)
    def __radd__(self, o): return _apply("add", o, self)
    def __sub__(self, o): return _apply("sub", self, o)
    def __rsub__(self, o): return _apply("sub", o, self)
    def __mul__(self, o): return _apply("mul", self, o)
    def __rmul__(self, o): return _apply("mul", o, self)
    def __truediv__(self, o): return _apply("div", self, o)
    def __rtruediv__(self, o): return _apply("div", o, self)
    def __floordiv__(self, o): return _apply("floordiv", self, o)
    def __rfloordiv__(self, o): return _apply("floordiv", o, self)
    def __mod__(self, o): return _apply("mod", self, o)
    def __rmod__(self, o): return _apply("mod", o, self)
    def __pow__(self, o):
        if isinstance(o, int) and not isinstance(o, bool) and 0 <= o <= 64:
            result = 1
            for _ in range(o):
                result = result * self
            return result
        return _apply("pow", self, o)
    def __rpow__(self, o): return _apply("pow", o, self)
    def __neg__(self): return _apply("neg", self)
    def __pos__(self): return self
    def __abs__(self): return _apply("abs", self)
    def __invert__(self): return _apply("not", self)
    def __and__(self, o): return _apply("and", self, o)
    def __rand__(self, o): return _apply("and", o, self)
    def __or__(self, o): return _apply("or", self, o)
    def __ror__(self, o): return _apply("or", o, self)
    def __xor__(self, o): return _apply("xor", self, o)
    def __rxor__(self, o): return _apply("xor", o, self)
    def __lshift__(self, o): return _apply("shl", self, o)
    def __rlshift__(self, o): return _apply("shl", o, self)
    def __rshift__(self, o): return _apply("shr", self, o)
    def __rrshift__(self, o): return _apply("shr", o, self)
    # comparisons
    def __lt__(self, o): return _apply("lt", self, o)
    def __le__(self, o): return _apply("le", self, o)
    def __gt__(self, o): return _apply("gt", self, o)
    def __ge__(self, o): return _apply("ge", self, o)
    def __eq__(self, o): return _apply("eq", self, o)
    def __ne__(self, o): return _apply("ne", self, o)
    __hash__ = None

    def __bool__(self):
        recorder = getattr(_state, "recorder", None)
        if recorder is None:
            raise CompileError("Branch on a symbolic value outside a traceable function")
        return recorder.decide(self)

    def __index__(self):
        raise CompileError("Symbolic value used as an index; use explicit gather arithmetic")

    def bit_length(self):
        return _apply("bit_length", self)

    def is_integer(self):
        return _apply("eq", _apply("floor", self), self)


# ---------------------------------------------------------------- builtins

def _is_sym(x):
    return isinstance(x, Sym)


def _sym_int(x=0, *rest):
    if rest or not _is_sym(x):
        return builtins.int(x, *rest)
    if x.node.ty == "i":
        return x
    return _apply("trunc", x) if x.node.ty == "f" else _apply("toint", x)


def _sym_float(x=0.0):
    if not _is_sym(x):
        return builtins.float(x)
    return x if x.node.ty == "f" else _apply("tofloat", x)


def _sym_bool(x=False):
    if not _is_sym(x):
        return builtins.bool(x)
    return x if x.node.ty == "b" else _apply("ne", x, 0)


def _sym_abs(x):
    return builtins.abs(x)


def _sym_str(*args, **kwargs):
    if len(args) == 1 and not kwargs:
        x = args[0]
        if _is_sym(x):
            if x.node.ty == "i":
                return Cat((Dec(x.node),))
            raise CompileError("str() of a non-integer symbolic value")
        if isinstance(x, (Cat, Sel)):
            return x
    return builtins.str(*args, **kwargs)


def mn_join(sep, body, rng):
    items = [body(i) for i in rng]
    if isinstance(sep, str) and isinstance(rng, range) and all(type(x) is str for x in items):
        return ConcatStr(sep.join(items), Concat(sep, rng, body))
    return sep.join(items)


def _reduce_pair(op, values):
    values = list(values)
    if not values:
        raise ValueError(f"{op}() arg is an empty sequence")
    if not any(_is_sym(v) for v in values):
        return builtins.max(values) if op == "max" else builtins.min(values)
    if len(values) == 1:
        return values[0]
    return _apply(op, *values)


def _sym_sum(values, start=0):
    values = list(values)
    if not any(_is_sym(v) for v in values) and not _is_sym(start):
        return builtins.sum(values, start)
    terms = ([] if (not _is_sym(start) and start == 0) else [start]) + values
    if len(terms) == 1:
        return terms[0] + 0
    return _apply("sum", *terms)


def _sym_max(*args, **kwargs):
    if kwargs:
        return builtins.max(*args, **kwargs)
    values = args[0] if len(args) == 1 else args
    return _reduce_pair("max", values)


def _sym_min(*args, **kwargs):
    if kwargs:
        return builtins.min(*args, **kwargs)
    values = args[0] if len(args) == 1 else args
    return _reduce_pair("min", values)


def _sym_any(values):
    values = list(values)
    if not any(_is_sym(v) for v in values):
        return builtins.any(values)
    terms = [_sym_bool(v) for v in values if _is_sym(v)]
    if any(not _is_sym(v) and v for v in values):
        return True
    return terms[0] if len(terms) == 1 else _apply("lor", *terms)


def _sym_all(values):
    values = list(values)
    if not any(_is_sym(v) for v in values):
        return builtins.all(values)
    if any(not _is_sym(v) and not v for v in values):
        return False
    terms = [_sym_bool(v) for v in values if _is_sym(v)]
    return terms[0] if len(terms) == 1 else _apply("land", *terms)


def _truth(x):
    return _sym_bool(x) if _is_sym(x) else builtins.bool(x)


def mn_ifexp(test, body, orelse):
    if _is_sym(test):
        cond = _sym_bool(test)
        return _merge(cond, body(), orelse())
    return body() if test else orelse()


def mn_and(left, right):
    a = left()
    if not _is_sym(a):
        return right() if a else a
    b = right()
    if _is_sym(b) or isinstance(b, bool):
        return _apply("land", _sym_bool(a), _truth(b) if _is_sym(b) else b)
    return _merge(_sym_bool(a), b, a)


def mn_or(left, right):
    a = left()
    if not _is_sym(a):
        return a if a else right()
    b = right()
    if _is_sym(b) or isinstance(b, bool):
        return _apply("lor", _sym_bool(a), _truth(b) if _is_sym(b) else b)
    return _merge(_sym_bool(a), a, b)


def mn_not(x):
    if _is_sym(x):
        return _apply("lnot", _sym_bool(x))
    return not x


def mn_contains(item, container, negate=False):
    if not (_is_sym(item) or (isinstance(container, (list, tuple)) and any(_is_sym(c) for c in container))):
        result = item in container
        return not result if negate else result
    if not isinstance(container, (list, tuple)):
        raise CompileError("Symbolic membership requires a list or tuple")
    result = _sym_any([item == element for element in container])
    return mn_not(result) if negate else result


def mn_getitem(container, index):
    if not _is_sym(index):
        return container[index]
    if not isinstance(container, (list, tuple)):
        raise CompileError("Symbolic index into a non-sequence")
    if any(isinstance(e, (list, tuple)) for e in container):
        raise CompileError("Symbolic index must select scalars")
    if index.node.ty != "i":
        raise CompileError("Symbolic index must be an integer")
    graph = _graph()
    return wrap(graph.make("gather", (index.node, *(lift(e) for e in container)), ty=graph_type(container)))


def graph_type(values):
    tys = {lift(v).ty for v in values}
    return "f" if "f" in tys else ("i" if "i" in tys else "b")


def _merge(cond, a, b):
    # A path that falls off the end of a function where the other path returns a
    # value is treated as unreachable ("Cannot get here"); verification checks it.
    if a is None and b is not None:
        return b
    if b is None and a is not None:
        return a
    if isinstance(a, (list, tuple)) or isinstance(b, (list, tuple)):
        if not (isinstance(a, (list, tuple)) and isinstance(b, (list, tuple)) and len(a) == len(b)):
            raise CompileError("Branches return differently shaped values")
        merged = [_merge(cond, x, y) for x, y in zip(a, b)]
        return tuple(merged) if isinstance(a, tuple) else merged
    if isinstance(a, (str, Cat, Sel)) or isinstance(b, (str, Cat, Sel)):
        if a == b:
            return a
        return Sel(lift(cond), to_strval(a), to_strval(b))
    if not _is_sym(a) and not _is_sym(b) and a == b and type(a) is type(b):
        return a
    return _apply("select", cond, a, b)


# ---------------------------------------------------------------- AST transform

class _Transformer(ast.NodeTransformer):
    def visit_IfExp(self, node):
        self.generic_visit(node)
        return ast.Call(
            ast.Name("__mn_ifexp", ast.Load()),
            [node.test, _lambda(node.body), _lambda(node.orelse)],
            [],
        )

    def visit_BoolOp(self, node):
        self.generic_visit(node)
        name = "__mn_and" if isinstance(node.op, ast.And) else "__mn_or"
        result = node.values[0]
        for value in node.values[1:]:
            result = ast.Call(ast.Name(name, ast.Load()), [_lambda(result), _lambda(value)], [])
        return result

    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.Not):
            return ast.Call(ast.Name("__mn_not", ast.Load()), [node.operand], [])
        return node

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) == 1 and isinstance(node.ops[0], (ast.In, ast.NotIn)):
            return ast.Call(
                ast.Name("__mn_contains", ast.Load()),
                [node.left, node.comparators[0], ast.Constant(isinstance(node.ops[0], ast.NotIn))],
                [],
            )
        if len(node.ops) > 1:
            # a < b < c  ->  (a < b) and (b < c), evaluating b once is fine for pure code
            terms = []
            left = node.left
            for op, right in zip(node.ops, node.comparators):
                terms.append(ast.Compare(left, [op], [right]))
                left = right
            return self.visit_BoolOp(ast.BoolOp(ast.And(), terms))
        return node

    def visit_Call(self, node):
        join = self._join_pattern(node)
        if join is not None:
            sep, name, elt, it = join
            lam = ast.Lambda(
                ast.arguments(
                    posonlyargs=[], args=[ast.arg(name)], vararg=None,
                    kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[],
                ),
                self.visit(elt),
            )
            return ast.Call(
                ast.Name("__mn_join", ast.Load()),
                [self.visit(sep), lam, self.visit(it)],
                [],
            )
        self.generic_visit(node)
        return ast.Call(ast.Name("__mn_call", ast.Load()), [node.func, *node.args], node.keywords)

    @staticmethod
    def _join_pattern(node):
        """`<sep>.join(<elt> for <name> in range(...))` (or a list comp)."""
        if not isinstance(node.func, ast.Attribute) or node.func.attr != "join":
            return None
        if node.keywords or len(node.args) != 1:
            return None
        comp = node.args[0]
        if not isinstance(comp, (ast.GeneratorExp, ast.ListComp)) or len(comp.generators) != 1:
            return None
        gen = comp.generators[0]
        if gen.is_async or gen.ifs or not isinstance(gen.target, ast.Name):
            return None
        it = gen.iter
        if not (
            isinstance(it, ast.Call)
            and isinstance(it.func, ast.Name)
            and it.func.id == "range"
            and 1 <= len(it.args) <= 3
            and not it.keywords
        ):
            return None
        return node.func.value, gen.target.id, comp.elt, it

    def visit_Subscript(self, node):
        self.generic_visit(node)
        if isinstance(node.ctx, ast.Load) and not isinstance(node.slice, ast.Slice):
            return ast.Call(ast.Name("__mn_getitem", ast.Load()), [node.value, node.slice], [])
        return node


def _lambda(expr):
    return ast.Lambda(
        ast.arguments(posonlyargs=[], args=[], vararg=None, kwonlyargs=[], kw_defaults=[], kwarg=None, defaults=[]),
        expr,
    )


_OVERRIDES = {
    builtins.int: _sym_int,
    builtins.float: _sym_float,
    builtins.bool: _sym_bool,
    builtins.abs: _sym_abs,
    builtins.max: _sym_max,
    builtins.min: _sym_min,
    builtins.any: _sym_any,
    builtins.all: _sym_all,
    builtins.str: _sym_str,
    builtins.sum: _sym_sum,
    math.floor: lambda x: _apply("floor", x) if _is_sym(x) else math.floor(x),
    math.exp: lambda x: _apply("exp", x) if _is_sym(x) else math.exp(x),
    math.log: lambda x: _apply("log", x) if _is_sym(x) else math.log(x),
    math.sqrt: lambda x: _apply("sqrt", x) if _is_sym(x) else math.sqrt(x),
    math.fabs: lambda x: _apply("abs", x) if _is_sym(x) else math.fabs(x),
    math.trunc: lambda x: _sym_int(x),
}


def _contains_sym(values):
    for v in values:
        if _is_sym(v):
            return True
        if isinstance(v, (list, tuple)) and _contains_sym(v):
            return True
    return False


@functools.lru_cache(maxsize=None)
def _transformed(func):
    """Recompile a pure Python function with the symbolic transform applied."""
    try:
        source = textwrap.dedent(inspect.getsource(func))
    except (OSError, TypeError) as exc:
        raise CompileError(f"Cannot trace into {func!r}: no source") from exc
    tree = ast.parse(source)
    fn = tree.body[0]
    if not isinstance(fn, ast.FunctionDef):
        raise CompileError(f"Cannot trace into {func!r}")
    fn.decorator_list = []
    tree = ast.fix_missing_locations(_Transformer().visit(tree))
    namespace = dict(func.__globals__)
    namespace.update(_runtime())
    exec(compile(tree, inspect.getsourcefile(func) or "<traced>", "exec"), namespace)
    return namespace[fn.name]


def mn_call(func, *args, **kwargs):
    override = _OVERRIDES.get(func) if _hashable(func) else None
    if override is not None:
        return override(*args, **kwargs)
    if isinstance(func, types.FunctionType) and _contains_sym(list(args) + list(kwargs.values())):
        if getattr(func, "__mn_traced__", False) or func.__code__.co_filename == "<kernel>":
            return func(*args, **kwargs)
        return _fork_merge(_transformed(func), args, kwargs)
    return func(*args, **kwargs)


def _hashable(x):
    try:
        hash(x)
        return True
    except TypeError:
        return False


def _fork_merge(func, args, kwargs, prefix=()):
    saved = getattr(_state, "recorder", None)
    _state.recorder = _Recorder(list(prefix))
    try:
        return func(*args, **kwargs)
    except _NeedDecision as need:
        cond = _sym_bool(need.cond)
        _state.recorder = saved
        when_true = _fork_merge(func, args, kwargs, (*prefix, True))
        when_false = _fork_merge(func, args, kwargs, (*prefix, False))
        return _merge(cond, when_true, when_false)
    finally:
        _state.recorder = saved


def _runtime():
    return {
        "__mn_ifexp": mn_ifexp,
        "__mn_and": mn_and,
        "__mn_or": mn_or,
        "__mn_not": mn_not,
        "__mn_contains": mn_contains,
        "__mn_call": mn_call,
        "__mn_getitem": mn_getitem,
        "__mn_join": mn_join,
    }


def load_kernel(source: str, name: str | None = None):
    """Compile kernel source with the symbolic transform. Returns the function."""
    tree = ast.parse(source)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    if not functions:
        raise CompileError("Kernel source defines no function")
    target = name or functions[-1].name
    tree = ast.fix_missing_locations(_Transformer().visit(tree))
    namespace = {"__name__": "__mn_kernel__"}
    namespace.update(_runtime())
    exec(compile(tree, "<kernel>", "exec"), namespace)
    func = namespace[target]
    func.__mn_traced__ = True
    return func


def load_reference(source: str, name: str | None = None):
    """The kernel as plain Python, for concrete reference evaluation."""
    namespace = {"__name__": "__mn_reference__"}
    exec(compile(source, "<kernel>", "exec"), namespace)
    tree = ast.parse(source)
    functions = [n.name for n in tree.body if isinstance(n, ast.FunctionDef)]
    return namespace[name or functions[-1]]


def _nested(shape, make, prefix=()):
    if len(prefix) == len(shape):
        return make(prefix)
    return [_nested(shape, make, prefix + (i,)) for i in range(shape[len(prefix)])]


def trace(source: str, inputs, name: str | None = None):
    """Trace `source` with symbolic tensors for `inputs` (TensorSpec list).

    Returns (graph, result) where result is the kernel's return value with Sym
    leaves (possibly nested lists, tuples, strings or Python scalars).
    """
    graph = Graph()
    _state.graph = graph
    try:
        func = load_kernel(source, name)
        args = []
        for spec in inputs:
            ty = "f" if spec.dtype.is_float else "i"
            args.append(_nested(spec.shape, lambda idx, s=spec, t=ty: Sym(graph.input(s.name, idx, t))))
        result = _fork_merge(func, args, {})
    finally:
        _state.graph = None
        _state.recorder = None
    return graph, result
