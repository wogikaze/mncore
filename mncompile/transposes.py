"""Transpose recognition and cyclic routing across the MAB axis."""

import ast
import math
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Scalar, Tensor, measure, optimize_map


def transpose_parameter(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a transpose function")
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
        raise CompileError("Expected a pure one-input transpose function")
    parameter = fn.args.args[0].arg
    result = fn.body[0].value
    if not isinstance(result, ast.ListComp) or len(result.generators) != 1:
        raise CompileError("Expected list(column) for column in zip(*x)")
    generator = result.generators[0]
    if (
        generator.ifs
        or generator.is_async
        or not isinstance(generator.target, ast.Name)
        or not isinstance(generator.iter, ast.Call)
        or not isinstance(generator.iter.func, ast.Name)
        or generator.iter.func.id != "zip"
        or generator.iter.keywords
        or len(generator.iter.args) != 1
        or not isinstance(generator.iter.args[0], ast.Starred)
        or not isinstance(generator.iter.args[0].value, ast.Name)
        or generator.iter.args[0].value.id != parameter
        or not isinstance(result.elt, ast.Call)
        or not isinstance(result.elt.func, ast.Name)
        or result.elt.func.id != "list"
        or result.elt.keywords
        or len(result.elt.args) != 1
        or not isinstance(result.elt.args[0], ast.Name)
        or result.elt.args[0].id != generator.target.id
    ):
        raise CompileError("Expected list(column) for column in zip(*x)")
    return fn.name, parameter


def evaluate_index(node, value):
    if node.op == "input":
        return value
    if node.op == "const":
        return node.value
    a, b = (evaluate_index(arg, value) for arg in node.args)
    operations = {
        "and": lambda: a & b,
        "or": lambda: a | b,
        "shl": lambda: a << b,
        "lshr": lambda: a >> b,
        "add": lambda: a + b,
        "mul": lambda: a * b,
    }
    if node.op not in operations:
        raise CompileError(
            f"Unsupported optimized transpose index operation: {node.op}"
        )
    return operations[node.op]() & (2**64 - 1)


def compile_transpose(
    source: str,
    *,
    inputs: dict[str, Tensor],
    output: Tensor,
    row_partition: str,
    opt="opt",
    assembler=None,
):
    name, parameter = transpose_parameter(source)
    if set(inputs) != {parameter}:
        raise CompileError("Transpose bindings do not match the source argument")
    data = inputs[parameter]
    if row_partition == "local":
        return compile_local_transpose(name, parameter, data, output, opt, assembler)
    if (
        row_partition != "mab"
        or data.dtype != output.dtype
        or data.dtype != "f64"
        or data.elements != 16
        or output.elements != 16
        or data.memory != "m"
        or output.memory != "n"
        or data.allow_infinity
        or output.allow_infinity
    ):
        raise CompileError(
            "Cyclic transpose currently supports a 16x16 Double matrix with one row per MAB"
        )
    index = Scalar("input", name="index")
    constant = lambda value: Scalar("const", value=value)
    equation = Scalar(
        "or",
        (
            Scalar("shl", (Scalar("and", (index, constant(15))), constant(4))),
            Scalar("lshr", (index, constant(4))),
        ),
    )
    llvm, optimized = optimize_map(equation, ("index",), 64, opt)
    permutation = [evaluate_index(optimized, value) for value in range(256)]
    if permutation != [16 * (value % 16) + value // 16 for value in range(256)]:
        raise CompileError("LLVM transpose index map did not preserve the permutation")
    # The verified permutation determines the cyclic displacement of each
    # diagonal. Schedule two diagonals per turnaround and keep six diagonals
    # in L1BM to finish the far half of the 16-way transpose.
    wrap = 4096
    flat_m = lambda addresses: (
        "$lmt[" + ",".join(str((data.offset + a) % wrap) for a in addresses) + "]"
    )
    flat_n = lambda addresses: (
        "$ln[" + ",".join(str((output.offset + a) % wrap) for a in addresses) + "]"
    )
    lines = ["ipackbit $mabid $ls0 $t $nb", "nop"]
    for displacement in range(1, 10):
        sources = [2 * displacement, wrap - 32 + 2 * displacement, 0, 0]
        if 2 <= displacement <= 7:
            sources[2:] = [16 + 2 * displacement, wrap - 16 + 2 * displacement]
            block = (
                128 + 384 * (displacement // 2 - 1)
                if displacement % 2 == 0
                else 384 * ((displacement - 3) // 2)
            )
            destination = f"$lb{block}"
        else:
            destination = "$lbi"
        statement = f"l1bmd+{displacement} {flat_m(sources)} {destination}"
        if displacement == 1:
            statement += f"; dvpassa {flat_m(sources)} $ln{output.offset}/0010"
        else:
            previous = displacement - 1
            statement += f"; l1bmd+{previous} $lbi {flat_n([wrap - 2 * previous, 32 - 2 * previous, 0, 0])}/1100"
        lines.append(statement)
    lines.append(
        f"l1bmd+9/1100 $lbi {flat_n([wrap - 18, 14, wrap - 18, wrap - 18])}/1100"
    )
    for tile in range(3):
        addresses = [
            wrap - 22 - 4 * tile,
            10 - 4 * tile,
            wrap - 20 - 4 * tile,
            12 - 4 * tile,
        ]
        lines.append(f"l1bmd+8 $lb{128 + 384 * tile} {flat_n(addresses)}")
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": name,
        "reference": "16x16 Double matrix transpose",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "row_partition": row_partition,
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": [
            "Double inputs are finite MN-Core normal values or signed zero; zero signs are equivalent",
            "GRF scratch and LM0 base register initially zero",
        ],
        "clobbers": [
            "T",
            "LM1 base register (2*MAB id)",
            "L1BM scratch",
            "forwarding registers",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected cyclic MAB transpose schedule",
    }
    return Compilation(
        vsm,
        llvm,
        {
            "schema_version": 1,
            "op": "transpose",
            "shape": [16, 16],
            "selected_index": optimized.to_dict(),
            "permutation": permutation,
        },
        report,
    )


def compile_local_transpose(name, parameter, data, output, opt, assembler):
    size = math.isqrt(data.elements)
    if (
        size * size != data.elements
        or size < 2
        or size & (size - 1)
        or data.elements % 4
        or data.dtype not in {"f64", "u64", "i64"}
        or output.dtype != data.dtype
        or output.elements != data.elements
        or data.memory == output.memory
    ):
        raise CompileError(
            "Local transpose requires a square power-of-two array of 64-bit elements in separate LM banks"
        )
    log = size.bit_length() - 1
    index = Scalar("input", name="index")
    constant = lambda value: Scalar("const", value=value)
    equation = Scalar(
        "or",
        (
            Scalar("shl", (Scalar("and", (index, constant(size - 1))), constant(log))),
            Scalar("lshr", (index, constant(log))),
        ),
    )
    llvm, optimized = optimize_map(equation, ("index",), 64, opt)
    permutation = [evaluate_index(optimized, value) for value in range(data.elements)]
    if permutation != [
        size * (value % size) + value // size for value in range(data.elements)
    ]:
        raise CompileError("Invalid optimized local transpose permutation")
    lines = []
    for first in range(0, data.elements, 4):
        sources = [data.offset + 2 * index for index in range(first, first + 4)]
        destinations = [
            output.offset + 2 * permutation[index] for index in range(first, first + 4)
        ]
        src = f"$l{data.memory}[" + ",".join(map(str, sources)) + "]"
        dst = f"$l{output.memory}[" + ",".join(map(str, destinations)) + "]"
        lines.append(f"lpassa {src} {dst}")
    vsm = "\n".join(lines) + "\n"
    report = {
        "function": name,
        "reference": "bit-preserving local matrix transpose",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "shape": [size, size],
        "row_partition": "local",
        "inputs": {parameter: asdict(data)},
        "output": asdict(output),
        "preconditions": ["LM base registers are initially zero"],
        "clobbers": ["ALU forwarding"],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "baseline direct address permutation; 128-bit packing optimization remains",
    }
    return Compilation(
        vsm,
        llvm,
        {
            "schema_version": 1,
            "op": "transpose",
            "shape": [size, size],
            "selected_index": optimized.to_dict(),
            "permutation": permutation,
        },
        report,
    )
