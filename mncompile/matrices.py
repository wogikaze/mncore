"""Exact bounded-integral matrix products stored in Float tensors."""

import ast
import math
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def square_parameter(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a matrix-square function")
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
        raise CompileError("Expected a pure one-input matrix-square function")
    parameter = fn.args.args[0].arg
    canonical = ast.parse(
        f"[[[sum(matrix[k][i] * matrix[j][k] for k in range(len(matrix))) for j in range(len(matrix))] for i in range(len(matrix))] for matrix in {parameter}]",
        mode="eval",
    ).body
    if ast.dump(fn.body[0].value) != ast.dump(canonical):
        raise CompileError(
            "Expected the transposed square of each matrix using a sum of products"
        )
    return fn.name, parameter


def compile_matrix_square(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    atol: float,
    opt="opt",
    assembler=None,
):
    name, parameter = square_parameter(source)
    if set(inputs) != {parameter}:
        raise CompileError("Matrix bindings do not match the function")
    data = inputs[parameter]
    if (
        data.dtype != "f32"
        or output.dtype != "f32"
        or data.memory != "m"
        or output.memory != "n"
        or data.elements != 64
        or output.elements != 64
        or data.offset % 2
        or output.offset % 2
        or row_partition != "l2b_pe_word"
        or data.minimum < 0
        or data.maximum > 100
        or not data.integral_values
        or not math.isfinite(atol)
        or atol < 0
    ):
        raise CompileError(
            "Exact Half matrix lowering requires explicitly integral Float inputs in 0..100 and the 16x16 PE/word layout"
        )
    m, n = data.offset, output.offset
    packets = [
        f"hmwrite $llm{m + 16 * i}vr $ly{4 * i}; hbfe/9 $llm{m + 16 * i}vr $ls{8 * i}v"
        for i in range(4)
    ]
    packets += [
        "hmread $lly0 $nowrite; hmwrite $lls0v $llx0",
        "hmread $lly8 $nowrite; hmwrite $lls16v $llx8; hbfe/9 $mreadf $lls32v",
        f"hmmul $lx $aluf $lln{n}v8; hbfe/9 $mreadf $lls48v",
        f"hmmul $lx $ls34v4 $lln{n + 4}v8",
        f"hmmul $lx $ls48v $lln{n + 32}v",
        f"hmmul $lx $ls56v $lln{n + 48}v",
    ]
    ir = (
        "define i32 @matrix_term(float %a, float %b) {\n"
        "  %x = fptoui float %a to i32\n  %y = fptoui float %b to i32\n"
        "  %p = mul i32 %x, %y\n  ret i32 %p\n}\n"
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
    vsm = "\n".join(packets) + "\n"
    report = {
        "function": name,
        "reference": "exact integral matrix square, transposed",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "16x16 matrices distributed over PE/local-row/word, replicated across MAB/L1B",
            "every Float input is an integer in 0..100",
            "standalone zero-initialized scratch",
        ],
        "numerical_argument": "Block-float scaling preserves integer inputs <=100; exact products and sums <=160000 fit accumulator and Float precision.",
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected bounded-integral block-matrix schedule",
    }
    semantic = {
        "schema_version": 1,
        "op": "transpose_matmul",
        "operands": [parameter, parameter],
        "matrix_shape": [16, 16],
        "integral_values": True,
        "max_dot_product": 160000,
        "layout": row_partition,
    }
    return Compilation(vsm, optimized.stdout, semantic, report)
