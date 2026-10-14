"""Whole-vector bit permutations using MAB-parallel sampling and OR reduction."""

import ast
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def parse_bit_reverse(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a bit reversal function")
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
        raise CompileError("Expected a pure one-input bit reversal")
    parameter = fn.args.args[0].arg
    result = fn.body[0].value
    if not isinstance(result, ast.ListComp) or len(result.generators) != 1:
        raise CompileError("Expected reversed words with reversed bits")
    outer = result.generators[0]
    if (
        outer.ifs
        or outer.is_async
        or not isinstance(outer.target, ast.Name)
        or not isinstance(outer.iter, ast.Call)
        or not isinstance(outer.iter.func, ast.Name)
        or outer.iter.func.id != "reversed"
        or outer.iter.keywords
        or len(outer.iter.args) != 1
        or not isinstance(outer.iter.args[0], ast.Name)
        or outer.iter.args[0].id != parameter
        or not isinstance(result.elt, ast.Call)
        or not isinstance(result.elt.func, ast.Name)
        or result.elt.func.id != "sum"
        or result.elt.keywords
        or len(result.elt.args) != 1
        or not isinstance(result.elt.args[0], ast.GeneratorExp)
    ):
        raise CompileError(
            "Expected sum of reversed bit positions for each reversed word"
        )
    terms = result.elt.args[0]
    if len(terms.generators) != 1:
        raise CompileError("Expected one bit-position generator")
    inner = terms.generators[0]
    if (
        inner.ifs
        or inner.is_async
        or not isinstance(inner.target, ast.Name)
        or not isinstance(inner.iter, ast.Call)
        or not isinstance(inner.iter.func, ast.Name)
        or inner.iter.func.id != "range"
        or inner.iter.keywords
        or len(inner.iter.args) != 1
        or not isinstance(inner.iter.args[0], ast.Constant)
        or inner.iter.args[0].value != 64
    ):
        raise CompileError("Expected range(64) bit positions")
    expected = ast.parse(
        f"((({outer.target.id} >> {inner.target.id}) & 1) << (63 - {inner.target.id}))",
        mode="eval",
    ).body
    if ast.dump(terms.elt) != ast.dump(expected):
        raise CompileError("Expected a 64-bit bit-reversal expression")
    return fn.name, parameter


def compile_bit_reverse(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    opt="opt",
    assembler=None,
):
    name, parameter = parse_bit_reverse(source)
    if set(inputs) != {parameter}:
        raise CompileError("Bit reversal bindings do not match source inputs")
    data = inputs[parameter]
    if (
        row_partition != "pe"
        or data.dtype != output.dtype
        or data.dtype != "u64"
        or data.elements != 4
        or output.elements != 4
        or data.memory != "m"
        or output.memory != "n"
    ):
        raise CompileError(
            "Bit reversal currently supports a 16-word UInt64 vector interleaved across four PEs"
        )
    ir = (
        "declare i64 @llvm.bitreverse.i64(i64)\n"
        "define i64 @reverse_bits(i64 %x) {\n  %v = call i64 @llvm.bitreverse.i64(i64 %x)\n  ret i64 %v\n}\n"
        "define i64 @reverse_index(i64 %i) {\n  %v = sub i64 15, %i\n  ret i64 %v\n}\n"
    )
    optimized = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=ir,
        text=True,
        capture_output=True,
    )
    if optimized.returncode or "@llvm.bitreverse.i64" not in optimized.stdout:
        raise CompileError("Unsupported optimized bit-reversal primitive")
    destination = (
        "$ln[" + ",".join(str(output.offset + word) for word in (6, 4, 2, 0)) + "]"
    )
    lines = [
        "spassa $mabid $lr16/1000",
        f"sbsl $lm{data.offset}v $aluf $nowrite; l1bmd-1 $aluf $lbi",
        "sand $msb1 $aluf $nowrite; l1bmrsor $lr16 $lbi; l1bmd-1 $lbi $nowrite",
        "sbsl $aluf $lbf $nowrite; l1bmm $lbi $nowrite",
        "sand $peid $lbf $omr1; l1bmrsbor $aluf $lbi",
        'imm s"0x3e10" $nowrite; l1bmm $lbi $nowrite',
        "ibsl $lbf $aluf $nowrite; hvmulr $aluf $aluf $nowrite",
        "lbsl $aluf $mauf $lr8v",
        f"msr $aluf {destination}",
        f"msl $lr8v {destination}/$imr1",
    ]
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": name,
        "reference": "reverse all 1024 bits of a 16-word UInt64 vector",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "row_partition": row_partition,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "input vector is replicated across the sixteen MABs within each L1B",
            "LM base registers initially zero",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected MAB-parallel bit permutation schedule",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "vector_bit_reverse",
            "word_bits": 64,
            "global_elements": 16,
            "layout": "four PEs interleaved; MAB replication",
            "verification_strategy": "1024 single-bit inputs plus all-zero and random vectors",
        },
        report,
    )
