"""Triangular integer comparisons and exact bounded-count reductions."""

import ast
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def inversion_parameter(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected an inversion-count function")
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
        raise CompileError("Expected a pure one-input inversion-count function")
    parameter = fn.args.args[0].arg
    # Compare canonical ASTs after replacing user-bound variable names. The
    # pattern contains the complete triangular iteration, not a problem name.
    result = fn.body[0].value
    if not isinstance(result, ast.ListComp) or len(result.generators) != 1:
        raise CompileError("Expected one inversion count for each row")
    outer = result.generators[0]
    if (
        not isinstance(outer.target, ast.Name)
        or not isinstance(outer.iter, ast.Name)
        or outer.iter.id != parameter
        or outer.ifs
        or outer.is_async
        or not isinstance(result.elt, ast.Call)
        or not isinstance(result.elt.func, ast.Name)
        or result.elt.func.id != "sum"
        or result.elt.keywords
        or len(result.elt.args) != 1
        or not isinstance(result.elt.args[0], ast.GeneratorExp)
    ):
        raise CompileError("Expected a sum of triangular comparisons for each row")
    terms = result.elt.args[0]
    if len(terms.generators) != 2 or not all(
        isinstance(gen.target, ast.Name) for gen in terms.generators
    ):
        raise CompileError("Expected two triangular index generators")
    row = outer.target.id
    left, right = (gen.target.id for gen in terms.generators)
    expected = ast.parse(
        f"sum({row}[{left}] > {row}[{right}] for {left} in range(len({row})) for {right} in range({left}+1,len({row})))",
        mode="eval",
    ).body
    if ast.dump(result.elt) != ast.dump(expected):
        raise CompileError(
            "Expected sum(row[left] > row[right] for left in range(len(row)) for right in range(left+1,len(row)))"
        )
    return fn.name, parameter


def small_packets(data, output):
    m = data.offset
    negative = (m + 4064) % 4096
    return [
        "lpackbit $mabid $ls0 $lmb",
        'imm ui"0xbf003f00" $nowrite',
        "lpackbit $subpeid $ls0 $lt; hvpassa $aluf $lr0v $omr1; hmwrite $aluf $lx0",
        f"lpassa $lm{m} $nowrite",
        f"lsub $aluf $lmt{negative}v8 $r0v/$imr1",
        'imm ui"0x4800fc00" $nowrite',
        "hmfma $lx $llr[4,4,4,0]r $aluf $lls0v",
        "l1bmriiadd $mauf $lb0",
        f"l1bmm $lbi $n{output.offset + 1}/$imr1",
    ]


def large_packets(data, output):
    m = lambda address: (data.offset + address) % 4096
    indirect = lambda addresses: (
        "$lmt[" + ",".join(str(m(address)) for address in addresses) + "]"
    )
    c = f"$ln{output.offset + 64}"
    return [
        "ipackbit $l2bid $ls128 $mb",
        f'imm ui"0x49800010" {c}v $ls64v',
        "ipackbit $l1bid $ls128 $t; fvmul $aluf $aluf $lr2v4",
        f"spassa $lm{m(64)}v16 $ls168v; hvpassa -$mauf $omr3",
        f"isub $aluf {indirect([4080] * 4)} $omr1; fvadd $lr2v4 $ls64v $lr0v4 $ls0v4",
        f"isub $ls168 $lmt{m(0)}v16 $omr2; fvadd $mauf -{c} $lr0v4/$imr1 $ls0v4/$imr1; l1bmd $lmt{m(0)}v16 $lbi",
        f"isub $ls170 $lmt{m(0)}v16 $omr1; fvadd $lr2v4 -{c} $lr2v4/$imr2; l1bmd $lbi $nowrite; l1bmd $lmt{m(0)}v16 $lbi",
        f"isub $ls172 $lbf $omr2; fvadd $lr0v4 -{c} $lr0v4/$imr1 $ls0v4/$imr1; l1bmd $lbi $nowrite; l1bmd $lm{m(0)}v16 $lbi",
        f"isub $ls174 $lbf $omr1; fvadd $lr2v4 -{c} $lr2v4/$imr2; l1bmd $lbi $ls160v",
        f"isub $ls[170,172,172,174] {indirect([64, 64, 80, 64])} $omr2; fvadd $lr0v4 -{c} $lr0v4/$imr1 $ls0v4/$imr1",
        f"isub $ls[174,174,160,162] {indirect([80, 96, 4080, 4080])} $omr1; fvadd $lr2v4 -{c} $lr2v4/$imr2",
        f"isub $ls[162,164,164,164] {indirect([0, 4080, 0, 16])} $omr2; fvadd $lr0v4 -{c} $lr0v4/$imr1 $ls0v4/$imr1",
        f"isub $ls[166,166,166,166] {indirect([4080, 0, 16, 32])} $omr1; fvadd $lr2v4 -{c} $lr2v4/$imr2",
        f"fvadd $lr0v4 -{c} $lr0v4/$imr1 $ls0v4/$imr1",
        "fvadd $lr2v4 $ls[256,256,256,0] $lr16v",
        "fvadd $mauf $lr[256,2,12,2] $lr24v",
        "fvadd $mauf $lr[256,4,22,256] $lr32v",
        "fvadd $mauf $lr[256,8,256,256] $nowrite",
        "fvadd/$imr3 $mauf $lr[256,36,256,256] $lr48v",
        "l1bmd $mauf $lb0",
        "nop",
        "nop",
        "l2bmriiadd $lb64 $lc0",
        "nop",
        "mvriiadd/n64 $lc0 $p0@0",
        "mvb/n64 $p0@0 $lc0",
        "nop",
        "nop",
        "l2bmb $lc0 $lb192",
        "nop",
        f"l1bmd $lb0 $ln{output.offset}/0001",
    ]


def compile_inversions(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    opt="opt",
    assembler=None,
):
    name, parameter = inversion_parameter(source)
    if set(inputs) != {parameter}:
        raise CompileError("Inversion bindings do not match source inputs")
    data = inputs[parameter]
    if (
        data.memory != "m"
        or output.memory != "n"
        or data.minimum < 0
        or data.dtype != output.dtype
    ):
        raise CompileError(
            "Inversion kernels require nonnegative integer rows in LM0 -> LM1"
        )
    if (
        data.dtype == "u64"
        and data.elements == 16
        and output.elements == 1
        and row_partition == "l2b_l1b"
        and data.maximum <= 2**32 - 1
    ):
        length = 16
        packets = small_packets(data, output)
        layout = "one row per L2B/L1B, replicated across MABs and PEs"
        padding = (
            "16 zero UInt64 values immediately preceding the input, wrapping within LM0"
        )
    elif (
        data.dtype == "u32"
        and data.elements == 128
        and output.elements == 2
        and row_partition == "mab_pe_word"
        and data.maximum <= 100
        and data.offset % 2 == output.offset % 2 == 0
    ):
        length = 64
        packets = large_packets(data, output)
        layout = "two interleaved rows per MAB/PE, replicated across L1Bs and L2Bs"
        padding = "zero-filled LM0 padding preceding the input"
    else:
        raise CompileError(
            "No inversion-count lowering for this row length, integer range, or layout"
        )
    bits = data.bits
    ir = f"define i{bits} @inversion_term(i{bits} %left, i{bits} %right) {{\n  %v = icmp ugt i{bits} %left, %right\n  %n = zext i1 %v to i{bits}\n  ret i{bits} %n\n}}\n"
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
        "reference": "strict inversion count for each integer row",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "row_length": length,
        "row_partition": row_partition,
        "preconditions": [
            layout,
            padding,
            "standalone zero-initialized scratch and output memory",
        ],
        "clobbers": [
            "LM0 base register",
            "T",
            "GRF/matrix/L1BM/L2BM/PDM scratch",
            "LM1 scratch at output offset + 64 for large rows",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected triangular-comparison and bounded-count reduction schedule",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "row_inversions",
            "row_length": length,
            "term": "unsigned_gt",
            "iteration": "0 <= left < right < row_length",
            "layout": layout,
        },
        report,
    )
