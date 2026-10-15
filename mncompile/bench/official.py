"""Logical input/expected values reconstructed from an official testcase."""

from __future__ import annotations

from ..values import decode, unpack
from .testcase import parse_entries


def logical_case(problem, testcase_path):
    contract = problem.contract
    tensors = {f"in{i}": t for i, t in enumerate(contract.inputs)}
    tensors |= {f"out{i}": t for i, t in enumerate(contract.outputs)}
    inputs = {t.name: {} for t in contract.inputs}
    expected = {t.name: {} for t in contract.outputs}
    atol = {t.name: t.atol for t in contract.outputs}
    for entry in parse_entries(testcase_path.read_text()):
        spec = tensors[entry.tensor]
        for lane, index in enumerate(entry.indices):
            index = tuple(index) + (0,) * (len(spec.shape) - len(index))
            if entry.kind == "get":
                value = entry.values[lane] if spec.dtype.kind != "bytes" else ord(entry.values[lane])
                expected[spec.name][index] = value
                atol[spec.name] = max(atol[spec.name], entry.atol)
            else:
                word = entry.payload[0]
                inputs[spec.name][index] = decode(unpack(word, spec.dtype, lane), spec.dtype)
    return inputs, expected, atol
