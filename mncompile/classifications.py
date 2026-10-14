"""Finite-domain integer classification lowered to parallel ALU/MAU packets."""

import ast
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def parse_mod_classification(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected an integer classification function")
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
        raise CompileError("Expected a pure one-input integer classification")
    parameter = fn.args.args[0].arg
    array = fn.body[0].value
    if not isinstance(array, ast.ListComp) or len(array.generators) != 1:
        raise CompileError("Expected an elementwise classification comprehension")
    generator = array.generators[0]
    if (
        generator.ifs
        or generator.is_async
        or not isinstance(generator.target, ast.Name)
        or not isinstance(generator.iter, ast.Name)
        or generator.iter.id != parameter
    ):
        raise CompileError("Expected a map over the input tensor")
    node, codes = array.elt, {}
    for divisor in (15, 3, 5):
        if not isinstance(node, ast.IfExp):
            raise CompileError("Expected modulo-15, modulo-3, modulo-5 selections")
        test = node.test
        if (
            not isinstance(test, ast.Compare)
            or len(test.ops) != 1
            or not isinstance(test.ops[0], ast.Eq)
            or len(test.comparators) != 1
            or not isinstance(test.comparators[0], ast.Constant)
            or test.comparators[0].value != 0
            or not isinstance(test.left, ast.BinOp)
            or not isinstance(test.left.op, ast.Mod)
            or not isinstance(test.left.left, ast.Name)
            or test.left.left.id != generator.target.id
            or not isinstance(test.left.right, ast.Constant)
            or test.left.right.value != divisor
            or not isinstance(node.body, ast.Constant)
            or type(node.body.value) is not int
            or not 0 <= node.body.value < 2**32
        ):
            raise CompileError(
                "Expected bounded UInt32 modulo classification with constant output codes"
            )
        codes[divisor] = node.body.value
        node = node.orelse
    if not isinstance(node, ast.Name) or node.id != generator.target.id:
        raise CompileError(
            "Nonmatching classification values must pass through unchanged"
        )
    return fn.name, parameter, codes


def compile_mod_classification(
    source: str, *, inputs: dict[str, Tensor], output: Tensor, opt="opt", assembler=None
):
    name, parameter, codes = parse_mod_classification(source)
    if set(inputs) != {parameter}:
        raise CompileError("Classification bindings do not match source inputs")
    data = inputs[parameter]
    if (
        data.dtype != output.dtype
        or data.dtype != "u32"
        or data.elements != output.elements
        or data.elements % 8
        or data.memory != "m"
        or output.memory != "n"
        or data.offset % 2
        or output.offset % 2
        or data.minimum < 1
        or data.maximum > 32768
    ):
        raise CompileError(
            "Modulo classification currently supports UInt32 values in [1,32768] in complete 8-element groups"
        )
    lines = ["define i32 @classify(i32 %x) {"]
    for divisor in (15, 3, 5):
        lines.extend(
            [
                f"  %r{divisor} = urem i32 %x, {divisor}",
                f"  %p{divisor} = icmp eq i32 %r{divisor}, 0",
            ]
        )
    lines.extend(
        [
            f"  %tail = select i1 %p5, i32 {codes[5]}, i32 %x",
            f"  %mid = select i1 %p3, i32 {codes[3]}, i32 %tail",
            f"  %result = select i1 %p15, i32 {codes[15]}, i32 %mid",
            "  ret i32 %result",
            "}",
        ]
    )
    ir = "\n".join(lines) + "\n"
    optimized = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=ir,
        text=True,
        capture_output=True,
    )
    if optimized.returncode:
        raise CompileError(optimized.stderr)
    packets = []
    for base in range(0, data.elements, 8):
        m, n = data.offset + base, output.offset + base
        packets.extend(
            [
                'imm ui"0x3eaaaaab" $lr32/1000',
                f"iadd $lm{m}v $aluf $nowrite; l1bmd+0 $lm{m}v $lbi",
                f'imm ui"0x78" $t; fvadd $aluf -$lr32 $ls0v; l1bmd $lbi $ln{n}v',
                'imm ui"0x3e4ccccd" $ls40; fvmul $mauf $lr32 $nowrite',
                "iand $mauf $t $omr1; fvmul $ls0v $aluf $nowrite",
                "iand $mauf $t $omr2; fvpassa/$imr1 $lr32 $nowrite",
                f'imm ui"{codes[5]:#010x}" $ln{n}v/$imr2; fvpassa/$imr2 $mauf $nowrite',
                f'imm ui"{codes[3]:#010x}" $ln{n}v/$imr1; fvadd $mauf -$ls40 $omr3',
                f'imm ui"{codes[15]:#010x}" $ln{n}v/$imr3',
            ]
        )
    vsm = "\n".join(packets) + "\n"
    report = {
        "function": name,
        "reference": "UInt32 modulo-3/5 classification with constant codes",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "codes": codes,
        "preconditions": [],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected bounded reciprocal-and-mask classification schedule",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "modulo_classification",
            "divisors": [15, 3, 5],
            "codes": codes,
        },
        report,
    )
