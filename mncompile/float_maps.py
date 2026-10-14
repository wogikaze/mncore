"""Floating array maps with error-controlled selection of machine idioms."""

import math
import subprocess
from dataclasses import asdict
from fractions import Fraction as Q

from .compiler import Compilation, CompileError, Expr, constant, optimize
from .maps import Tensor, measure, parse_map


def scalar_expression(node):
    if node.op == "input":
        return Expr("input")
    if node.op == "const":
        return constant(node.value)
    if node.op in {"add", "sub", "mul"}:
        return Expr(node.op, tuple(scalar_expression(arg) for arg in node.args))
    raise CompileError(f"Unsupported floating map operation: {node.op}")


def compile_float_map(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    atol: float,
    opt="opt",
    assembler=None,
):
    name, params, scalar = parse_map(source)
    if len(params) != 1 or set(params) != set(inputs):
        raise CompileError("Floating maps currently require one input tensor")
    data = inputs[params[0]]
    if not math.isfinite(atol) or atol < 0:
        raise CompileError("Expected a finite nonnegative error budget")
    original = scalar_expression(scalar)
    llvm, expression = optimize(original, opt)
    if data.dtype == output.dtype == "f32":
        return compile_affine_float(
            name,
            params[0],
            data,
            output,
            original,
            expression,
            llvm,
            atol,
            opt,
            assembler,
        )
    if (
        data.dtype != "h16"
        or output.dtype != "h16"
        or data.elements != output.elements
        or data.memory != "m"
        or output.memory != "n"
        or data.offset % 4
        or output.offset % 4
        or data.elements % 16
        or max(abs(data.minimum), abs(data.maximum)) > 1
    ):
        raise CompileError(
            "Half doubling currently supports complete 16-element groups in LM0 -> LM1, domain [-1, 1]"
        )
    if expression.polynomial() != (Q(0), Q(2)):
        raise CompileError(
            "No Half map instruction-selection rule for this expression yet"
        )
    # Baseline: four Half lanes per cycle, exact multiplication by two and
    # rounding back to Half. Every normal input in [-1,1] doubles exactly.
    baseline = ['imm h"2.0" $t']
    for word in range(0, data.elements // 2, 8):
        coefficient = "$aluf" if word == 0 else "$t"
        baseline.append(
            f"hvmulr $lm{data.offset + word}v {coefficient} $ln{output.offset + word}v"
        )
    candidates = [("native-half-multiply", Q(0), "\n".join(baseline) + "\n", [])]
    if data.elements == 192:
        m = lambda index: data.offset + index
        n = lambda index: output.offset + index
        # Three initial tiles preserve raw lower halves. Subsequent MAU tiles
        # precompute the missing halves. ALU's inverse leaky-ReLU increments
        # a Half exponent and preserves a second long word, completing 128-bit
        # tiles. Its -0 output also supplies the remaining predicate constants.
        lines = [
            f"hpassa $llm{m(0)}v $llr0v; hvaddr $llm{m(0)}v $llm{m(0)}ve $ln{n(0)}v4",
            f"hpassa $llm{m(16)}v $llr16v; hvaddr $llm{m(16)}v $llm{m(16)}ve $ln{n(16)}v4",
            f"hilrelud $msb1 $lr2v4 $ln{n(2)}v4 $lls256v; hvaddr $lm{m(66)}v4 $lm{m(66)}v4e $lr66v4",
            f"hpassa $llm{m(32)}v $llr32v; hvaddr $llm{m(32)}v $llm{m(32)}ve $ln{n(32)}v4",
            f"hilrelud $msb1 $lr18v4 $ln{n(18)}v4; hvaddr $lm{m(50)}v4 $lm{m(50)}v4e $ls50v4; l1bmd $ls258v4 $lbi",
            f"hilrelud $msb1 $lr34v4 $ln{n(34)}v4; hvaddr $lm{m(48)}v4 $lm{m(48)}v4e $nowrite; l1bmd $ls258v4 $lbi; l1bmd $lbi $lr64v4 $ls80v4",
            f"hrelu $lls48v $mauf $lln{n(48)}v; hvaddr $lm{m(82)}v4 $lm{m(82)}v4e $ls82v4",
            f"hilrelud $llr64v $lm{m(64)}v4 $lln{n(64)}v",
            f"hilrelud $lls80v $lm{m(80)}v4 $lln{n(80)}v",
        ]
        # Exponent increment maps +/-0 to +/-minimum-normal rather than zero.
        # This deliberate approximation is only selected when budget permits.
        candidates.append(
            (
                "half-exponent-increment-tiles",
                Q(1, 2**30),
                "\n".join(lines) + "\n",
                ["GRF scratch is initially zero (standalone Challenge machine)"],
            )
        )
    records, feasible = [], []
    for label, error, vsm, preconditions in candidates:
        cost = measure(vsm, assembler)
        records.append(
            {
                "name": label,
                "lines": cost,
                "error_bound": str(error),
                "feasible": error <= Q(atol),
            }
        )
        if error <= Q(atol):
            feasible.append((cost, error, label, vsm, preconditions))
    cost, error, label, vsm, preconditions = min(
        feasible, key=lambda candidate: candidate[:3]
    )
    report = {
        "function": name,
        "reference": "real-valued elementwise MN-Core Half doubling",
        "lines": cost,
        "atol": atol,
        "error_bound": str(error),
        "error_bound_float": float(error),
        "chosen": label,
        "candidates": records,
        "fast_math": False,
        "inputs": {params[0]: asdict(data)},
        "output": asdict(output),
        "preconditions": ["Half inputs are finite MN-Core normal values or signed zero"]
        + preconditions,
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "minimum over generated Half multiply and exponent-increment candidates",
        "llvm_version": subprocess.check_output(
            [opt, "--version"], text=True
        ).splitlines()[0],
    }
    return Compilation(
        vsm,
        llvm,
        {
            "schema_version": 1,
            "source": original.to_dict(),
            "selected": expression.to_dict(),
        },
        report,
    )


def compile_affine_float(
    name, parameter, data, output, original, expression, llvm, atol, opt, assembler
):
    polynomial = expression.polynomial()
    if len(polynomial) != 2:
        raise CompileError(
            "The tiled Float map currently supports positive power-of-two affine kernels"
        )
    bias, coefficient = polynomial
    if coefficient.denominator != 1:
        raise CompileError(
            "The tiled affine coefficient must be an integer power of two"
        )
    c = int(coefficient)
    if (
        c < 1
        or c > 256
        or c & (c - 1)
        or bias != c * c
        or data.minimum < 0
        or data.maximum > 1
        or data.memory != "m"
        or output.memory != "n"
        or data.offset % 4
        or output.offset % 4
        or data.elements != output.elements
        or data.elements % 8
    ):
        raise CompileError(
            "Expected (x+c)*c, power-of-two c in [1,256], input [0,1], complete Float groups"
        )
    # Products by c are exact; only the addition rounds. The mixed-precision
    # route converts *the constant*, which is exactly representable in Half.
    # It keeps x in Float and accumulates in Float, never rounding x to Half.
    error = Q(1, 2**24) * (c * c + c)
    if error > Q(atol):
        raise CompileError("Affine Float rounding bound exceeds the error budget")
    baseline = [f'imm f"{c}.0" $lr128v', "fvmul $aluf $aluf $ls256v"]
    for word in range(0, data.elements, 8):
        constant_bias = "$mauf" if word == 0 else "$ls256v"
        baseline.append(
            f"fvfma $lm{data.offset + word}v $lr128v {constant_bias} $ln{output.offset + word}v"
        )
    candidates = [("float-affine-fma", "\n".join(baseline) + "\n", [])]
    if data.elements == 128:
        m, n = lambda word: data.offset + word, lambda word: output.offset + word
        lines = [
            f'imm f"{c * c}.0" $lr[256,258,260,262] $ls[256,258,260,262]',
            f'imm f"{c}.0" $lr[128,130,132,134] $ls[128,130,132,134]; l1bmd $aluf $lb0',
            f"isub $lr256v $aluf $t; hvadd $alufr $llm[{m(0)},{m(4)},{m(8)},{m(12)}] $llr[0,4,8,12]",
            f"iadd $aluf $mauf $ln[{n(0)},{n(4)},{n(8)},{n(12)}]; hvadd $lls128r $llm[{m(16)},{m(20)},{m(24)},{m(28)}] $llr[16,20,24,28]",
            f"iadd $t $lr[2,6,10,14] $ln[{n(2)},{n(6)},{n(10)},{n(14)}]; hvadd $lls128r $llm[{m(32)},{m(36)},{m(40)},{m(44)}] $llr[32,36,40,44]; l1bmd $lb0 $nowrite",
            f"iadd $t $lr[18,22,26,30] $lr[18,22,26,30]; fvfma $lm[{m(80)},{m(84)},{m(88)},{m(92)}] $ls128 $lbf $ln[{n(80)},{n(84)},{n(88)},{n(92)}]; l1bmd $lb0 $nowrite",
            f"iadd $t $lr[34,38,42,46] $lr[34,38,42,46]; fvfma $lm[{m(82)},{m(86)},{m(90)},{m(94)}] $ls128 $lbf $ln[{n(82)},{n(86)},{n(90)},{n(94)}]",
            f"iadd $llr[16,20,24,28] $t $lln[{n(16)},{n(20)},{n(24)},{n(28)}]; hvadd $lls128r $llm[{m(48)},{m(52)},{m(56)},{m(60)}] $llr[48,52,56,60]",
            f"iadd $llr[32,36,40,44] $t $lln[{n(32)},{n(36)},{n(40)},{n(44)}]; hvadd $lls128r $llm[{m(64)},{m(68)},{m(72)},{m(76)}] $llr[64,68,72,76]; l1bmd $lb0 $nowrite",
            f"iadd $t $lr[50,54,58,62] $lr[50,54,58,62]; fvfma $lm[{m(96)},{m(100)},{m(104)},{m(108)}] $ls128 $lbf $ln[{n(96)},{n(100)},{n(104)},{n(108)}]; l1bmd $lb0 $nowrite",
            f"iadd $t $lr[66,70,74,78] $lr[66,70,74,78]; fvfma $lm[{m(98)},{m(102)},{m(106)},{m(110)}] $ls128 $lbf $ln[{n(98)},{n(102)},{n(106)},{n(110)}]; l1bmd $lb0 $nowrite",
            f"iadd $llr[48,52,56,60] $t $lln[{n(48)},{n(52)},{n(56)},{n(60)}]; fvfma $lm[{m(114)},{m(118)},{m(122)},{m(126)}] $ls128 $lbf $lr[114,118,122,126]",
            f"iadd $llr[64,68,72,76] $t $lln[{n(64)},{n(68)},{n(72)},{n(76)}]; fvfma $lm[{m(112)},{m(116)},{m(120)},{m(124)}] $ls128 $lbf $nowrite",
            f"frelu $llr112v $mauf $lln{n(112)}v",
        ]
        candidates.append(
            (
                "float-affine-half-constant-tiles",
                "\n".join(lines) + "\n",
                ["GRF scratch is initially zero (standalone Challenge machine)"],
            )
        )
    scored = [
        (measure(vsm, assembler), label, vsm, preconditions)
        for label, vsm, preconditions in candidates
    ]
    cost, label, vsm, preconditions = min(scored, key=lambda candidate: candidate[:2])
    report = {
        "function": name,
        "reference": "real-valued Float affine polynomial",
        "lines": cost,
        "atol": atol,
        "error_bound": str(error),
        "error_bound_float": float(error),
        "chosen": label,
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "Float inputs are finite MN-Core normal values or signed zero"
        ]
        + preconditions,
        "candidates": [
            {"name": key, "lines": count, "error_bound": str(error), "feasible": True}
            for count, key, _, _ in scored
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "minimum over generated native-FMA and mixed-unit affine candidates",
        "llvm_version": subprocess.check_output(
            [opt, "--version"], text=True
        ).splitlines()[0],
    }
    return Compilation(
        vsm,
        llvm,
        {
            "schema_version": 1,
            "source": original.to_dict(),
            "selected": expression.to_dict(),
        },
        report,
    )
