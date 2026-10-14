"""A typed colorsys.hsv_to_rgb intrinsic and its native Float schedule."""

import ast
import math
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def color_specification(source):
    module = ast.parse(source)
    if (
        len(module.body) != 2
        or not isinstance(module.body[0], ast.Import)
        or len(module.body[0].names) != 1
        or module.body[0].names[0].name != "colorsys"
        or module.body[0].names[0].asname
        or not isinstance(module.body[1], ast.FunctionDef)
    ):
        raise CompileError(
            "Expected import colorsys followed by a pure color-map function"
        )
    fn = module.body[1]
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
        raise CompileError("Expected a one-input color-map function")
    parameter = fn.args.args[0].arg
    result = fn.body[0].value
    if (
        not isinstance(result, ast.ListComp)
        or len(result.generators) != 1
        or not isinstance(result.generators[0].target, ast.Name)
    ):
        raise CompileError(
            "Expected a list comprehension of colorsys.hsv_to_rgb(*color)"
        )
    color = result.generators[0].target.id
    canonical = ast.parse(
        f"[colorsys.hsv_to_rgb(*{color}) for {color} in {parameter}]", mode="eval"
    ).body
    if ast.dump(result) != ast.dump(canonical):
        raise CompileError("Expected colorsys.hsv_to_rgb for each input color")
    return fn.name, parameter


def compile_hsv_to_rgb(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    atol: float,
    opt="opt",
    assembler=None,
):
    name, parameter = color_specification(source)
    if set(inputs) != {parameter}:
        raise CompileError("Color bindings do not match the function")
    data = inputs[parameter]
    bound = 64 * 2**-22
    if (
        data.dtype != "f32"
        or output.dtype != "f32"
        or data.memory != "m"
        or output.memory != "n"
        or data.elements != 24
        or output.elements != 24
        or data.offset % 2
        or output.offset % 2
        or data.minimum < 0
        or data.maximum > 1
        or row_partition != "pe_word_rgb"
        or not math.isfinite(atol)
        or atol < bound
    ):
        raise CompileError(
            "HSV lowering requires eight Float colors per PE in [0,1], replicated across MABs, and atol >= 2^-16"
        )
    m, n = data.offset, output.offset
    packets = [
        'imm ui"0x43004300" $lr0v',
        f"filrelud $msb1 $aluf $nowrite; fvmul $alufe $lm{m}v6 $lr8v",
        f"ffloor $mauf $ls0v; fvmulr $aluf $aluf $nowrite; l1bmd+0 $lm{m + 4}v6 $lbi",
        'imm ui"0x10423880" $t; hvfma $mauf $lr0vr $aluf $nowrite; l1bmd $lbi $nowrite',
        f"iadd $mabid $mauf $nowrite; fvmul $lm{m + 2}v6 $lbf $lr16v",
        "ilsl $t $aluf $t; fvadd -$ls0v $lr8v $lr8v",
        f"frelu3 $aluf $lr16v $omr1; fvfma $lr16v $mauf $lm{m + 4}v6 $ls24v; l1bmm@14 $aluf $lbi",
        "filrelud/$imr1 $t $lr16v $nowrite; fvadd $mauf -$lr16v $ls32v; l1bmd-11 $aluf $lbi; l1bmm $lbi $nowrite",
        "frelu2 $lbf $ls24v $nowrite; fvfma -$aluf $lr8v $mauf $nowrite; l1bmm@2 $aluf $lbi; l1bmd-11 $lbi $nowrite",
        f"fmax $aluf $ls32v $lr64v; fvadd $lbf $mauf $ln{n + 2}v6 $t; l1bmm $lbi $nowrite",
        f"fvfma -$lbf $lr8v $aluf $ln{n}v6; l1bmm@4 $mauf $lbi",
        f"l1bmm $lbi $ln{n + 4}v6",
    ]
    # Strict LLVM channel formulas. Sector selection is a semantic intrinsic
    # with an explicit six-entry table, not a dependence on sample colors.
    ir = (
        "define float @hsv_p(float %s, float %v) {\n  %a = fsub float 1.0, %s\n  %p = fmul float %v, %a\n  ret float %p\n}\n"
        "define float @hsv_q(float %s, float %v, float %f) {\n  %a = fmul float %s, %f\n  %b = fsub float 1.0, %a\n  %q = fmul float %v, %b\n  ret float %q\n}\n"
        "define float @hsv_t(float %s, float %v, float %f) {\n  %a = fsub float 1.0, %f\n  %b = fmul float %s, %a\n  %c = fsub float 1.0, %b\n  %t = fmul float %v, %c\n  ret float %t\n}\n"
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
        "reference": "colorsys.hsv_to_rgb, real channel formulas",
        "lines": measure(vsm, assembler),
        "error_bound": str(bound),
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "eight colors per PE, pairs of H/S/V words; replicated across MAB/L1B/L2B",
            "standalone zero-initialized scratch",
        ],
        "numerical_model": "Float operations have relative error <=2^-22 plus flush-to-zero error <=2^-126; constants and sector routing are exact",
        "numerical_argument": "64 Float ulps at unit magnitude conservatively cover H*6, fractional-part perturbation, channel products/adds; adjacent hue sectors agree at their boundary.",
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected six-sector Float channel schedule",
    }
    semantic = {
        "schema_version": 1,
        "op": "hsv_to_rgb",
        "layout": row_partition,
        "sector": "floor(6*h) mod 6",
        "fraction": "6*h-floor(6*h)",
        "channels": {"p": "v*(1-s)", "q": "v*(1-s*f)", "t": "v*(1-s*(1-f))"},
        "sector_channels": [
            ["v", "t", "p"],
            ["q", "v", "p"],
            ["p", "v", "t"],
            ["p", "q", "v"],
            ["t", "p", "v"],
            ["v", "p", "q"],
        ],
    }
    return Compilation(vsm, optimized.stdout, semantic, report)
