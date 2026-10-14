"""Structured array primitives with explicit logical/physical layout contracts."""

import ast
import math
import subprocess
from dataclasses import asdict
from fractions import Fraction as Q

from .compiler import Compilation, CompileError
from .maps import Scalar, Tensor, measure, optimize_map


def compile_square_sum(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    atol: float,
    opt="opt",
    assembler=None,
) -> Compilation:
    try:
        module = ast.parse(source)
    except SyntaxError as exc:
        raise CompileError(str(exc)) from exc
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a sum-of-squares function")
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
        raise CompileError("Expected a pure one-input sum-of-squares function")
    parameter = fn.args.args[0].arg
    result = fn.body[0].value
    valid = isinstance(result, ast.ListComp) and len(result.generators) == 1
    if valid:
        outer = result.generators[0]
        valid = (
            not outer.ifs
            and not outer.is_async
            and isinstance(outer.target, ast.Name)
            and isinstance(outer.iter, ast.Name)
            and outer.iter.id == parameter
            and isinstance(result.elt, ast.Call)
            and isinstance(result.elt.func, ast.Name)
            and result.elt.func.id == "sum"
            and len(result.elt.args) == 1
            and not result.elt.keywords
        )
    if valid:
        terms = result.elt.args[0]
        valid = isinstance(terms, ast.GeneratorExp) and len(terms.generators) == 1
    if valid:
        inner = terms.generators[0]
        valid = (
            not inner.ifs
            and not inner.is_async
            and isinstance(inner.target, ast.Name)
            and isinstance(inner.iter, ast.Name)
            and inner.iter.id == outer.target.id
            and isinstance(terms.elt, ast.BinOp)
            and isinstance(terms.elt.op, ast.Mult)
            and isinstance(terms.elt.left, ast.Name)
            and isinstance(terms.elt.right, ast.Name)
            and terms.elt.left.id == terms.elt.right.id == inner.target.id
        )
    if not valid or set(inputs) != {parameter}:
        raise CompileError(
            "Expected sum(value*value for value in row) for each input row"
        )
    data = inputs[parameter]
    if (
        row_partition != "l2b_pe"
        or data.dtype != output.dtype
        or data.dtype != "f64"
        or data.memory != "m"
        or output.memory != "n"
        or data.elements != 128
        or output.elements != 1
        or max(abs(data.minimum), abs(data.maximum)) > 1
        or not math.isfinite(atol)
        or atol < 0
    ):
        raise CompileError(
            "Square-sum currently supports 128 Doubles in [-1,1] per L2B/PE row"
        )
    # At most 128 products and 127 additions per logical result. Bound 512
    # rounding/alignment events of magnitude <=128 with 4x headroom:
    # 4*512*128*2^-52 = 2^-34. Dropped Double partial products (<2^-72
    # relative) and underflow are much smaller than this conservative margin.
    error = Q(1, 2**34)
    if error > Q(atol):
        raise CompileError("Double square-sum bound exceeds the error budget")
    ir = "define double @square(double %x) {\n  %v = fmul double %x, %x\n  ret double %v\n}\n"
    optimized = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=ir,
        text=True,
        capture_output=True,
    )
    if optimized.returncode or "fmul double %x, %x" not in optimized.stdout:
        raise CompileError("Unsupported optimized square term")
    m, n = data.offset, output.offset
    lines = [
        "ipackbit $mabid $ls0v $t",
        "nop",
        f"dvmulu $lmt{m}v32 $lmt{m}v32 $nowrite",
        f"dvfmad $lmt{m}v32 $lmt{m}v32 $mauf $nowrite",
        f"dvfmau $lmt{m + 128}v32 $lmt{m + 128}v32 $mauf $nowrite",
        f"dvfmad $lmt{m + 128}v32 $lmt{m + 128}v32 $mauf $nowrite",
        "l1bmrdfadd $mauf $lb0",
        "l1bmm $lbi $lr0v $ls0v",
        "dvadd $lbf $ls[4,4,4,0] $nowrite",
        "dvadd $mauf $ls2 $nowrite",
        f"dvadd $mauf $ls4 $ln{n}/0001",
    ]
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": fn.name,
        "reference": "real-valued row sum of squares",
        "lines": measure(vsm, assembler),
        "atol": atol,
        "error_bound": str(error),
        "error_bound_float": float(error),
        "fast_math": False,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "row_partition": row_partition,
        "preconditions": [
            "Double inputs are finite MN-Core normal values or signed zero",
            "input row is replicated across MABs/L1Bs; MAB ID partitions its reduction",
            "GRF scratch is initially zero",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected 128-element MAB-parallel reduction schedule",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "row_sum",
            "term": "square",
            "length": 128,
            "row_partition": row_partition,
            "parallel_axis": "mab",
        },
        report,
    )


def gather_names(source):
    try:
        module = ast.parse(source)
    except SyntaxError as exc:
        raise CompileError(str(exc)) from exc
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a gather function")
    fn = module.body[0]
    if (
        len(fn.args.args) != 2
        or fn.args.posonlyargs
        or fn.args.kwonlyargs
        or fn.args.vararg
        or fn.args.kwarg
        or fn.args.defaults
        or fn.decorator_list
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
    ):
        raise CompileError("Expected a pure two-input gather comprehension")
    outer = fn.body[0].value
    if (
        not isinstance(outer, ast.ListComp)
        or len(outer.generators) != 1
        or not isinstance(outer.elt, ast.ListComp)
    ):
        raise CompileError("Expected rows containing indexed elements")
    row = outer.generators[0]
    inner = outer.elt
    if (
        row.ifs
        or row.is_async
        or not isinstance(row.target, ast.Tuple)
        or len(row.target.elts) != 2
        or not all(isinstance(n, ast.Name) for n in row.target.elts)
        or not isinstance(row.iter, ast.Call)
        or not isinstance(row.iter.func, ast.Name)
        or row.iter.func.id != "zip"
        or row.iter.keywords
        or len(row.iter.args) != 2
        or not all(isinstance(n, ast.Name) for n in row.iter.args)
        or len(inner.generators) != 1
    ):
        raise CompileError("Expected rows paired by zip")
    indexed = inner.generators[0]
    if (
        indexed.ifs
        or indexed.is_async
        or not isinstance(indexed.target, ast.Name)
        or not isinstance(indexed.iter, ast.Name)
        or indexed.iter.id != row.target.elts[1].id
        or not isinstance(inner.elt, ast.Subscript)
        or not isinstance(inner.elt.value, ast.Name)
        or inner.elt.value.id != row.target.elts[0].id
        or not isinstance(inner.elt.slice, ast.Name)
        or inner.elt.slice.id != indexed.target.id
    ):
        raise CompileError("Expected row[index] for each index in its row")
    params = {arg.arg for arg in fn.args.args}
    names = tuple(arg.id for arg in row.iter.args)
    if len(set(names)) != 2 or set(names) != params:
        raise CompileError("Gather inputs must match function parameters")
    return fn.name, names


def compile_gather(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    opt="opt",
    assembler=None,
) -> Compilation:
    name, (data_name, index_name) = gather_names(source)
    if set(inputs) != {data_name, index_name}:
        raise CompileError("Gather bindings do not match function inputs")
    data, indices = inputs[data_name], inputs[index_name]
    if (
        row_partition != "mab"
        or data.dtype != "f64"
        or indices.dtype != "u64"
        or output.dtype != "f64"
        or data.memory != "m"
        or output.memory != "n"
        or output.elements != indices.elements
        or indices.elements % 16
        or indices.minimum < 0
        or indices.maximum >= data.elements
        or data.offset % 2
        or indices.offset % 4
        or output.offset % 4
    ):
        raise CompileError(
            "Gather currently supports Double rows on MABs, UInt64 indices, and 16-element output tiles"
        )
    # LLVM selects the per-element word-address calculation. The typed gather
    # primitive retains its bounds/layout contract across collective lowering.
    index = Scalar("input", name="index")
    address_ir, address = optimize_map(
        Scalar("add", (index, index)), ("index",), 64, opt
    )
    if address != Scalar("shl", (index, Scalar("const", value=1))):
        raise CompileError("Unsupported optimized gather address calculation")
    read_ir = "define double @gather(ptr %row, i64 %index) {\n  %p = getelementptr double, ptr %row, i64 %index\n  %v = load double, ptr %p\n  ret double %v\n}\n"
    process = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=read_ir,
        text=True,
        capture_output=True,
    )
    if process.returncode:
        raise CompileError(process.stderr)
    lines = []
    for base in range(0, indices.elements, 16):
        first, second = indices.offset + 2 * base, indices.offset + 2 * (base + 8)
        out = output.offset + 2 * base
        lines.extend(
            [
                f"ladd $l{indices.memory}{first}v4j1 $l{indices.memory}{first}v4j1 $t",
                f"ladd $l{indices.memory}{second}v4j1 $l{indices.memory}{second}v4j1 $nowrite",
                f"dvpassa $lmt{data.offset} $ln{out + 2}v4; lpassa $aluf $t",
                f"msl $mauf $ln{out}v4",
                f"dvpassa $lmt{data.offset} $ln{out + 18}v4",
                f"msl $mauf $ln{out + 16}v4",
            ]
        )
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": name,
        "reference": "row-wise Double gather",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "row_partition": row_partition,
        "inputs": {key: asdict(tensor) for key, tensor in inputs.items()},
        "output": asdict(output),
        "preconditions": [
            "Double inputs are finite MN-Core normal values or zero; zero signs are equivalent"
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected 16-element gather microkernel; global shortestness is not established",
    }
    read_body = "\n".join(
        line
        for line in process.stdout.splitlines()
        if not line.startswith(("source_filename =", "; ModuleID ="))
    )
    llvm = address_ir.replace("@kernel", "@word_address") + "\n" + read_body + "\n"
    semantic = {
        "schema_version": 1,
        "op": "gather",
        "data": data_name,
        "indices": index_name,
        "address": address.to_dict(),
        "layout": "one row per MAB; source/index rows broadcast to its PEs",
    }
    return Compilation(vsm, llvm, semantic, report)
