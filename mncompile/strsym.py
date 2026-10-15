"""Symbolic strings: the trace-level representation of `sep.join(f(i) for i in range(...))`.

`Dec` is the decimal string of an integer IR node, `Cat` a concatenation of
plain strings and `Dec`s, and `Sel` a symbolic choice between two symbolic
strings. `ConcatStr` is the concrete result of a `str.join` whose per-item
function was also recorded symbolically as a `Concat` for `concat.py` to analyze.
"""

from __future__ import annotations

from dataclasses import dataclass

from .errors import CompileError
from .ir import Node


@dataclass(frozen=True)
class Dec:
    node: Node  # str() of an integer IR node


def _cat(parts):
    merged = []
    for p in parts:
        if isinstance(p, str):
            if not p:
                continue
            if merged and isinstance(merged[-1], str):
                merged[-1] += p
            else:
                merged.append(p)
        elif isinstance(p, Dec):
            merged.append(p)
        else:
            raise CompileError(f"concat: cannot append {type(p).__name__} to a string")
    return Cat(tuple(merged))


@dataclass(frozen=True)
class Cat:
    parts: tuple  # of str | Dec; adjacent str parts merged, no empty strs

    def __add__(self, other):
        if isinstance(other, Sel):
            return Sel(other.cond, self + other.a, self + other.b)
        if isinstance(other, (str, Cat)):
            return _cat((*self.parts, *(other.parts if isinstance(other, Cat) else (other,))))
        return NotImplemented

    def __radd__(self, other):
        if isinstance(other, str):
            return _cat((other, *self.parts))
        return NotImplemented


@dataclass(frozen=True)
class Sel:
    cond: Node  # a bool IR node
    a: "Cat | Sel"
    b: "Cat | Sel"

    def __add__(self, other):
        if isinstance(other, (str, Cat, Sel)):
            return Sel(self.cond, self.a + other, self.b + other)
        return NotImplemented

    def __radd__(self, other):
        if isinstance(other, (str, Cat)):
            return Sel(self.cond, other + self.a, other + self.b)
        return NotImplemented


def to_strval(x):
    if isinstance(x, str):
        return Cat((x,)) if x else Cat(())
    if isinstance(x, (Cat, Sel)):
        return x
    raise CompileError(f"Cannot use {type(x).__name__} as a symbolic string")


@dataclass(frozen=True)
class Concat:
    sep: str
    rng: range
    body: object  # item function, callable with a concrete or symbolic index


class ConcatStr(str):
    """A joined string that also carries its symbolic structure."""

    def __new__(cls, value, concat):
        obj = super().__new__(cls, value)
        obj.concat = concat
        return obj
