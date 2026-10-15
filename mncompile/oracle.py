"""Reference semantics: run the kernel as ordinary Python on logical tensors."""

from __future__ import annotations

import math

from .errors import CompileError
from .layout import TensorSpec
from .trace import load_reference


def nested(shape, values: dict, prefix=()):
    if len(prefix) == len(shape):
        return values[prefix]
    return [nested(shape, values, prefix + (i,)) for i in range(shape[len(prefix)])]


def flatten_output(result, spec: TensorSpec) -> dict[tuple[int, ...], object]:
    """Map a kernel's return value onto logical indices of the output tensor.

    Strings and bytes fill a String tensor from index 0; a shorter result leaves
    the remaining elements unconstrained.
    """
    out: dict[tuple[int, ...], object] = {}
    shape = spec.shape
    if spec.dtype.kind == "bytes":
        if isinstance(result, str):
            data = result.encode("latin-1")
        elif isinstance(result, (bytes, bytearray)):
            data = bytes(result)
        else:
            data = bytes(int(v) for v in _flat(result))
        if len(data) > spec.size:
            raise CompileError(f"{spec.name}: {len(data)} bytes exceed the tensor size {spec.size}")
        for i, b in enumerate(data):
            out[_unravel(i, shape)] = b
        return out

    def visit(value, prefix):
        if len(prefix) == len(shape):
            out[prefix] = value
            return
        if not isinstance(value, (list, tuple)):
            raise CompileError(f"{spec.name}: expected a nested sequence of shape {shape}")
        if len(value) != shape[len(prefix)]:
            raise CompileError(f"{spec.name}: axis {len(prefix)} has length {len(value)}, expected {shape[len(prefix)]}")
        for i, v in enumerate(value):
            visit(v, prefix + (i,))

    if len(shape) == 1 and not isinstance(result, (list, tuple)):
        raise CompileError(f"{spec.name}: kernel must return a sequence")
    visit(result, ())
    return out


def _flat(value):
    if isinstance(value, (list, tuple)):
        for v in value:
            yield from _flat(v)
    else:
        yield value


def _unravel(i, shape):
    idx = []
    for n in reversed(shape):
        i, r = divmod(i, n)
        idx.append(r)
    return tuple(reversed(idx))


def run_reference(source: str, inputs: list[TensorSpec], outputs: list[TensorSpec], values: dict):
    """`values[name][index]` -> Python value. Returns {output name: {index: value}}."""
    func = load_reference(source)
    args = [nested(spec.shape, values[spec.name]) for spec in inputs]
    result = func(*args)
    if len(outputs) == 1:
        results = [result]
    else:
        if not isinstance(result, tuple) or len(result) != len(outputs):
            raise CompileError("Kernel must return one value per output tensor")
        results = list(result)
    return {spec.name: flatten_output(r, spec) for spec, r in zip(outputs, results)}


def as_python(value, spec: TensorSpec):
    """Python value the kernel sees for a stored element."""
    if spec.dtype.is_float:
        return float(value)
    return int(value)


def check_finite(value):
    return not (isinstance(value, float) and math.isnan(value))
