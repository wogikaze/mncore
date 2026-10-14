"""Exact floating predicates; approximation of the branch condition is forbidden."""

import ast
import subprocess
from dataclasses import asdict
from fractions import Fraction as Q

from .compiler import Compilation, CompileError, llvm_number
from .maps import Tensor, measure


def compile_threshold(
    source: str, *, inputs: dict[str, Tensor], output: Tensor, opt="opt", assembler=None
):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected an elementwise threshold function")
    fn = module.body[0]
    if (
        len(fn.args.args) != 1
        or fn.args.posonlyargs
        or fn.args.kwonlyargs
        or fn.args.vararg
        or fn.args.kwarg
        or fn.args.defaults
        or fn.decorator_list
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
    ):
        raise CompileError("Expected a pure one-input threshold map")
    parameter = fn.args.args[0].arg
    array = fn.body[0].value
    if not isinstance(array, ast.ListComp) or len(array.generators) != 1:
        raise CompileError("Expected a list comprehension")
    generator = array.generators[0]
    selection = array.elt
    if (
        generator.ifs
        or generator.is_async
        or not isinstance(generator.target, ast.Name)
        or not isinstance(generator.iter, ast.Name)
        or generator.iter.id != parameter
        or not isinstance(selection, ast.IfExp)
    ):
        raise CompileError("Expected a threshold selection for each input element")
    condition = selection.test
    true, false = selection.body, selection.orelse
    if (
        not isinstance(condition, ast.Compare)
        or len(condition.ops) != 1
        or not isinstance(condition.ops[0], ast.GtE)
        or not isinstance(condition.left, ast.Name)
        or condition.left.id != generator.target.id
        or len(condition.comparators) != 1
        or not isinstance(condition.comparators[0], ast.Constant)
        or type(condition.comparators[0].value) not in (int, float)
        or not isinstance(true, ast.Call)
        or not isinstance(true.func, ast.Name)
        or true.func.id != "float"
        or true.keywords
        or len(true.args) != 1
        or not isinstance(true.args[0], ast.Constant)
        or true.args[0].value != "inf"
        or not isinstance(false, ast.Constant)
        or type(false.value) not in (int, float)
        or false.value != 0
        or set(inputs) != {parameter}
    ):
        raise CompileError('Expected float("inf") if value >= threshold else 0')
    threshold = condition.comparators[0].value
    if threshold not in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        raise CompileError(
            "Exact Half-constant threshold currently requires a positive power of two in [1,256]"
        )
    data = inputs[parameter]
    if (
        data.dtype != output.dtype
        or data.dtype != "f32"
        or not output.allow_infinity
        or data.allow_infinity
        or data.minimum < 0
        or data.memory != "m"
        or output.memory != "n"
        or data.offset % 4
        or output.offset % 4
        or data.elements != output.elements
        or data.elements % 4
    ):
        raise CompileError(
            "Threshold maps require nonnegative Float input and an infinity-capable Float output"
        )
    ir = (
        "define float @threshold(float %x) {\n"
        f"  %mask = fcmp oge float %x, {llvm_number(Q(threshold))}\n"
        "  %selected = select i1 %mask, float 0x7FF0000000000000, float 0.0\n"
        "  ret float %selected\n}\n"
    )
    optimized = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=ir,
        text=True,
        capture_output=True,
    )
    if optimized.returncode:
        raise CompileError(optimized.stderr)
    lines = [f'imm h"{-float(threshold)!r}" $t', 'imm ui"0x7fffffff" $lls0v']
    previous = None

    def vector(tensor, base, remaining):
        groups = min(16, remaining) // 4
        addresses = [tensor.offset + base + 4 * (cycle % groups) for cycle in range(4)]
        return f"$ll{tensor.memory}[" + ",".join(map(str, addresses)) + "]"

    def store(base, remaining, mask):
        return f"ipassa $lls0 {vector(output, base, remaining)}/$llimr{mask}"

    for group, base in enumerate(range(0, data.elements, 16)):
        mask = group % 2 + 1
        coefficient = "$t"
        statement = (
            f"hvadd {coefficient} {vector(data, base, data.elements - base)} $omr{mask}"
        )
        if previous:
            statement += "; " + store(*previous)
        lines.append(statement)
        previous = (base, data.elements - base, mask)
    lines.append(store(*previous))
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": fn.name,
        "reference": "exact nonnegative Float threshold -> infinity or zero",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "threshold": threshold,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "Float inputs are finite MN-Core normal values or signed zero",
            "output LM words are initially zero",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected exact Half-constant comparison pipeline",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "select",
            "predicate": "ge",
            "threshold": threshold,
            "true": "infinity",
            "false": 0,
        },
        report,
    )
