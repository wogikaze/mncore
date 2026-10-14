"""Compile-time sequences and their hierarchical MN-Core materialization."""

import ast
import struct
import subprocess
from dataclasses import asdict, dataclass

from .compiler import Compilation, CompileError
from .maps import measure


@dataclass(frozen=True)
class GlobalTensor:
    dtype: str
    group: int
    offset: int
    elements: int
    minimum: int = 0
    maximum: int = 255

    def __post_init__(self):
        if (
            self.dtype not in {"i32", "u32", "bytes"}
            or not 0 <= self.group < 4
            or self.offset < 0
            or self.elements < 1
        ):
            raise CompileError("Invalid DRAM output layout")
        bits = 8 if self.dtype == "bytes" else 32
        if self.offset + (self.elements * bits + 63) // 64 > 2**29:
            raise CompileError("DRAM output exceeds one group's capacity")


def range_specification(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a sequence generator function")
    fn = module.body[0]
    if (
        fn.args.args
        or fn.args.posonlyargs
        or fn.args.kwonlyargs
        or fn.args.vararg
        or fn.args.kwarg
        or fn.args.defaults
        or fn.decorator_list
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
    ):
        raise CompileError("Expected a constant sequence generator with no inputs")
    result = fn.body[0].value
    if (
        not isinstance(result, ast.Call)
        or not isinstance(result.func, ast.Name)
        or result.func.id != "list"
        or len(result.args) != 1
        or result.keywords
        or not isinstance(result.args[0], ast.Call)
    ):
        raise CompileError("Expected list(range(...))")
    sequence = result.args[0]
    if (
        not isinstance(sequence.func, ast.Name)
        or sequence.func.id != "range"
        or sequence.keywords
        or not 1 <= len(sequence.args) <= 3
        or not all(
            isinstance(arg, ast.Constant) and type(arg.value) is int
            for arg in sequence.args
        )
    ):
        raise CompileError("Expected a range with compile-time integer bounds")
    values = [arg.value for arg in sequence.args]
    if len(values) == 1:
        start, stop, step = 0, values[0], 1
    else:
        start, stop = values[:2]
        step = values[2] if len(values) == 3 else 1
    return fn.name, start, stop, step


def compile_range(
    source: str, *, inputs: dict, output: GlobalTensor, opt="opt", assembler=None
):
    name, start, stop, step = range_specification(source)
    count = stop - start
    if (
        inputs
        or start != 1
        or step != 1
        or not 1 <= count <= 32768
        or output.elements != count
        or output.dtype not in {"i32", "u32"}
        or output.group != 0
        or output.offset != 0
    ):
        raise CompileError(
            "The hierarchical range generator supports prefixes of range(1,32769) in group-0 DRAM"
        )
    ir = (
        "define void @arange(ptr %output) {\nentry:\n  br label %loop\nloop:\n"
        "  %i = phi i32 [ 1, %entry ], [ %next, %loop ]\n  %index = sub i32 %i, 1\n"
        "  %wide = zext i32 %index to i64\n  %p = getelementptr i32, ptr %output, i64 %wide\n"
        f"  store i32 %i, ptr %p\n  %next = add i32 %i, 1\n  %done = icmp eq i32 %i, {count}\n"
        "  br i1 %done, label %exit, label %loop\nexit:\n  ret void\n}\n"
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
    # Physical affine-index construction: use hardware IDs to form lane/block
    # bases, concatenate/reduce across L1B/L2B/group, then expand the result
    # through indirect DRAM transfers. No input values or testcase are read.
    packets = [
        'imm ui"0x3fc1c208" $llt $s1',
        "ilsl $mabid $aluf $nowrite; hvpassar -$aluf $omr1; l1bmr4ior $aluf $lb1024",
        "slsl/$imr1 $l1bid $lltr $lr0v; fvpassa -$llt $nowrite; l1bmr4fmin $aluf $lbi",
        "ipackbit $peid $mauf $t; fvmul $t $t $lr8; l1bmm4 $lbi $nowrite",
        "iadd $lr0 $lbf $ls0v/$imr1; l1bmd+0 $aluf $lb0; l2bmriiadd $lb1024 $lc1024",
        "iadd $t $lr0v $nowrite; l1bmd+0 $aluf $lb256",
        "ibsl/$imr1 $ls0 $lr8 $nowrite; l1bmd+0 $aluf $lb512; l2bmdars $lc1024@.0 $dar0; l2bmdarw",
        "l1bmd+0 $aluf $lb768; l2bm@1 $lb0 $lc128; l2bmdarw",
        "l2bmr2fmin $lb256 $lc256; l2bmdarw",
        "l2bm@1 $lb512 $lc192; l2bmdarw",
        "l2bmr2fmin $lb768 $lc768",
        "nop",
        "mvd/n256 $lc768 $p0@0",
        "mvp/n256 $lc128@0.0 $d0@0",
        "mvp/n18432nd8 $di0@0 $lc0@0.0",
        "mvp/n2048 $p0@0 $lc0@0.1",
        "mvr2iiadd/n2048 $lc0@0 $p0@0",
        "mvb/n2048 $p0@0 $lc0",
        "mvd/n2048 $lc0 $p0@0",
        "mvp/n16384 $p0@0 $lc2048@0.1",
        "mvr2iiadd/n16384 $lc2048 $d0",
    ]
    vsm = "\n".join(packets) + "\n"
    report = {
        "function": name,
        "reference": f"range(1,{stop})",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {},
        "output": asdict(output),
        "allocated_elements": 32768,
        "preconditions": ["standalone zero-initialized Challenge machine"],
        "clobbers": [
            "DRAM prefixes in all groups up to 32768 Int elements",
            "PE/L1BM/L2BM/PDM/DAR scratch",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected hierarchical prefix generator; small output sizes are not yet optimized",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "arange",
            "start": start,
            "stop": stop,
            "step": step,
            "logical_elements": count,
            "physical_elements": 32768,
        },
        report,
    )


def literal_specification(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a literal output function")
    fn = module.body[0]
    if (
        fn.args.args
        or fn.args.posonlyargs
        or fn.args.kwonlyargs
        or fn.args.vararg
        or fn.args.kwarg
        or fn.args.defaults
        or fn.decorator_list
        or len(fn.body) != 1
        or not isinstance(fn.body[0], ast.Return)
        or not isinstance(fn.body[0].value, ast.Constant)
        or type(fn.body[0].value.value) not in (str, bytes)
    ):
        raise CompileError(
            "Expected a no-input function returning a string or bytes literal"
        )
    value = fn.body[0].value.value
    return fn.name, value.encode("utf-8") if isinstance(value, str) else value


def unscale_half(bits, power=7):
    if bits == 0:
        return 0
    exponent = (bits >> 9) & 63
    if not power < exponent < 63:
        raise CompileError(
            "Literal halfword cannot be encoded by the exact power-of-two reduction"
        )
    return bits - (power << 9)


def cast_scaled_byte(word):
    value = struct.unpack(">d", word.to_bytes(4, "big") * 2)[0]
    try:
        bits = int.from_bytes(struct.pack(">f", value), "big")
    except OverflowError:
        bits = 0x7F800000
    if bits & 0x7F800000 == 0:
        bits = 0
    half = bits >> 16
    exponent = (half >> 9) & 63
    scaled = 0 if exponent == 0 else 0x7E00 if exponent + 7 >= 63 else half + (7 << 9)
    return scaled >> 8


def constant_llvm(name, value, opt):
    escaped = "".join(f"\\{byte:02X}" for byte in value)
    ir = (
        f'@data = private constant [{len(value)} x i8] c"{escaped}"\n'
        "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1 immarg)\n"
        f"define void @{name}(ptr %output) {{\n"
        f"  call void @llvm.memcpy.p0.p0.i64(ptr %output, ptr @data, i64 {len(value)}, i1 false)\n"
        "  ret void\n}\n"
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
    return optimized.stdout


def compile_literal(
    source: str, *, inputs: dict, output: GlobalTensor, opt="opt", assembler=None
):
    name, value = literal_specification(source)
    if (
        inputs
        or output.dtype != "bytes"
        or output.group != 0
        or output.offset != 0
        or output.elements != len(value)
    ):
        raise CompileError(
            "Literal output bindings must describe its UTF-8 bytes in group-0 DRAM"
        )
    if len(value) != 13 or any(byte >= 128 for byte in value):
        raise CompileError(
            "The compact literal packer currently supports compatible 13-byte ASCII literals"
        )
    words = []
    for index in range(0, 12, 4):
        high = int.from_bytes(value[index : index + 2], "big")
        low = int.from_bytes(value[index + 2 : index + 4], "big")
        words.append((unscale_half(high) << 16) | unscale_half(low))
    if words[0] & 0x7F800000 == 0 or cast_scaled_byte(words[0]) != value[12]:
        raise CompileError(
            "Literal does not satisfy the derived final-byte packing constraint"
        )
    first, second, third = words
    packets = [
        f'imm ui"{first:#010x}" $lr0 $t',
        "idec $subpeid $omr1; dvpassar $aluf $r1",
        f'imm ui"{third:#010x}" $r0/$imr1; fvadd -$aluf -$t $omr2',
        f'imm ui"{second:#010x}" $r1v2/$imr2',
        "l1bmrhfadd $lr[16,16,16,0] $lb36",
        "nop",
        "nop",
        "l2bmrhfadd $lb16 $lc32",
        "mvp/n64 $lc64@0.0 $d0@0",
    ]
    vsm = "\n".join(packets) + "\n"
    report = {
        "function": name,
        "reference": "compile-time literal UTF-8 bytes",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {},
        "output": asdict(output),
        "allocated_bytes": 512,
        "literal_hex": value.hex(),
        "preconditions": ["standalone zero-initialized Challenge machine"],
        "clobbers": [
            "group-0 DRAM first 512 bytes (logical output is only 13 bytes)",
            "PE/L1BM/L2BM scratch",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected three-immediate literal packing schedule; other literal families remain unsupported",
    }
    return Compilation(
        vsm,
        constant_llvm(name, value, opt),
        {
            "schema_version": 1,
            "op": "literal_bytes",
            "hex": value.hex(),
            "unscaled_words": words,
            "reduction_scale": 128,
            "derived_last_byte": cast_scaled_byte(words[0]),
        },
        report,
    )
