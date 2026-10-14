"""A deliberately small, inspectable error-budgeted compiler.

The source denotes a real polynomial evaluated at finite MN-Core Float inputs.
All error bounds are rational; LLVM is used without fast-math. Its optimized
arithmetic graph is lowered to VSM, rather than kept as an unrelated artifact.
"""

from __future__ import annotations

import ast
import json
import math
import re
import shutil
import struct
import subprocess
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

Poly = tuple[Q, ...]
MIN_NORMAL = Q(1, 2**126)
MAX_FLOAT = Q((2**24 - 1) * 2**104)
# Loose bound covering Float RNE (2^-24), dropped multiplication partial
# products (<2^-36 relative), and fvadd's adder alignment. See README.
ROUND_REL = Q(1, 2**22)


class CompileError(ValueError):
    pass


def trim(p: Poly) -> Poly:
    while len(p) > 1 and p[-1] == 0:
        p = p[:-1]
    return p


def add(a: Poly, b: Poly, sign: int = 1) -> Poly:
    return trim(
        tuple(
            (a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)
            for i in range(max(len(a), len(b)))
        )
    )


def mul(a: Poly, b: Poly) -> Poly:
    if len(a) + len(b) - 2 > 16:
        raise CompileError("Polynomial degree exceeds the initial limit of 16")
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(tuple(out))


@dataclass(frozen=True)
class Expr:
    op: str
    args: tuple[Expr, ...] = ()
    value: Q = Q(0)

    def polynomial(self) -> Poly:
        if self.op == "input":
            return (Q(0), Q(1))
        if self.op == "const":
            return (self.value,)
        a, b = (x.polynomial() for x in self.args)
        return (
            mul(a, b) if self.op == "mul" else add(a, b, -1 if self.op == "sub" else 1)
        )

    def to_dict(self) -> dict:
        return {
            "op": self.op,
            "value": str(self.value),
            "args": [a.to_dict() for a in self.args],
        }


X = Expr("input")


def constant(value: Q | float) -> Expr:
    return Expr("const", value=Q(value))


def parse_source(source: str) -> tuple[str, Expr]:
    """Parse a pure one-input function without executing any source code."""
    try:
        module = ast.parse(source)
    except SyntaxError as exc:
        raise CompileError(f"Invalid Python source: {exc}") from exc
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Source must contain exactly one function definition")
    fn = module.body[0]
    args = fn.args
    if (
        len(args.args) != 1
        or args.posonlyargs
        or args.kwonlyargs
        or args.vararg
        or args.kwarg
        or args.defaults
        or fn.decorator_list
    ):
        raise CompileError(
            "Expected one positional argument, no defaults or decorators"
        )
    env = {args.args[0].arg: X}

    def expr(node: ast.AST) -> Expr:
        if isinstance(node, ast.Name) and node.id in env:
            return env[node.id]
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            if not math.isfinite(node.value):
                raise CompileError("Constants must be finite")
            return constant(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = expr(node.operand)
            return (
                value
                if isinstance(node.op, ast.UAdd)
                else Expr("mul", (constant(-1), value))
            )
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                if (
                    not isinstance(node.right, ast.Constant)
                    or type(node.right.value) is not int
                    or not 0 <= node.right.value <= 16
                ):
                    raise CompileError(
                        "Powers require a constant integer exponent in [0, 16]"
                    )
                value, out = expr(node.left), constant(1)
                for _ in range(node.right.value):
                    out = Expr("mul", (out, value))
                return out
            operation = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}.get(
                type(node.op)
            )
            if operation:
                return Expr(operation, (expr(node.left), expr(node.right)))
        raise CompileError(
            f"Unsupported expression at line {getattr(node, 'lineno', '?')}: {ast.dump(node)}"
        )

    for index, statement in enumerate(fn.body):
        if (
            isinstance(statement, ast.Assign)
            and len(statement.targets) == 1
            and isinstance(statement.targets[0], ast.Name)
        ):
            env[statement.targets[0].id] = expr(statement.value)
        elif (
            isinstance(statement, ast.Return)
            and index == len(fn.body) - 1
            and statement.value
        ):
            result = expr(statement.value)
            result.polynomial()  # Enforce the degree limit before invoking LLVM.
            return fn.name, result
        else:
            raise CompileError(
                "Only local assignments followed by a final return are supported"
            )
    raise CompileError("Missing return")


def horner(p: Poly) -> Expr:
    out = constant(p[-1])
    for coefficient in reversed(p[:-1]):
        out = Expr("mul", (out, X))
        if coefficient:
            out = Expr("add", (out, constant(coefficient)))
    return out


def llvm_number(q: Q) -> str:
    try:
        value = float(q)
    except OverflowError as exc:
        raise CompileError("Constant exceeds LLVM double range") from exc
    if not math.isfinite(value):
        raise CompileError("Constant exceeds LLVM double range")
    return "0x" + struct.pack(">d", value).hex().upper()


def optimize(expr: Expr, opt: str) -> tuple[str, Expr]:
    lines, memo = [], {}

    def emit(node: Expr) -> str:
        if node.op == "input":
            return "%x"
        if node.op == "const":
            return llvm_number(node.value)
        if node in memo:
            return memo[node]
        a, b = (emit(arg) for arg in node.args)
        name = f"%v{len(lines)}"
        lines.append(f"  {name} = f{node.op} double {a}, {b}")
        memo[node] = name
        return name

    result = emit(expr)
    source = (
        "define double @kernel(double %x) {\nentry:\n"
        + "\n".join(lines)
        + f"\n  ret double {result}\n}}\n"
    )
    process = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=source,
        text=True,
        capture_output=True,
    )
    if process.returncode:
        raise CompileError(f"LLVM optimization failed: {process.stderr}")
    optimized = process.stdout
    values = {"%x": X}

    def operand(text: str) -> Expr:
        text = text.strip()
        if text in values:
            return values[text]
        if text.startswith("0x"):
            value = struct.unpack(">d", bytes.fromhex(text[2:]))[0]
        else:
            try:
                value = float(text)
            except ValueError as exc:
                raise CompileError(f"Unsupported LLVM operand: {text}") from exc
        if not math.isfinite(value):
            raise CompileError("Non-finite LLVM constant")
        return constant(value)

    for line in optimized.splitlines():
        if match := re.fullmatch(
            r"\s*(%[\w.]+) = f(add|sub|mul) double ([^,]+), ([^,]+)\s*", line
        ):
            name, operation, a, b = match.groups()
            values[name] = Expr(operation, (operand(a), operand(b)))
        elif match := re.fullmatch(r"\s*(%[\w.]+) = fneg double (.+)", line):
            values[match[1]] = Expr("sub", (constant(0), operand(match[2])))
        elif match := re.fullmatch(r"\s*ret double (.+)", line):
            return optimized, operand(match[1])
        elif re.match(r"\s*%.*=", line):
            raise CompileError(
                f"Unsupported optimized LLVM instruction: {line.strip()}"
            )
    raise CompileError("LLVM did not return a supported scalar kernel")


def f32(q: Q) -> Q:
    try:
        value = struct.unpack(">f", struct.pack(">f", float(q)))[0]
    except (OverflowError, struct.error) as exc:
        raise CompileError("Constant overflows MN-Core Float") from exc
    if not math.isfinite(value):
        raise CompileError("Constant overflows MN-Core Float")
    value = Q(value)
    return Q(0) if abs(value) < MIN_NORMAL else value


def magnitude(p: Poly, radius: Q) -> Q:
    return sum((abs(c) * radius**i for i, c in enumerate(p)), Q(0))


def round_bound(size: Q) -> Q:
    bound = ROUND_REL * size + MIN_NORMAL
    if size + bound > MAX_FLOAT:
        raise CompileError(
            "Cannot exclude intermediate Float overflow on the declared domain"
        )
    return bound


def arithmetic_error(expr: Expr, radius: Q) -> Q:
    """Whole-domain bound, conditional on the documented MN Float model."""
    memo = {}

    def visit(node: Expr) -> Q:
        if node in memo:
            return memo[node]
        if node.op == "input":
            error = Q(0)
        elif node.op == "const":
            error = abs(node.value - f32(node.value))
        else:
            a, b = node.args
            ea, eb = visit(a), visit(b)
            ma, mb = (
                magnitude(a.polynomial(), radius),
                magnitude(b.polynomial(), radius),
            )
            if node.op == "mul":
                propagated = ma * eb + mb * ea + ea * eb
                error = propagated + round_bound((ma + ea) * (mb + eb))
            else:
                error = ea + eb + round_bound(ma + ea + mb + eb)
        memo[node] = error
        return error

    return visit(expr)


def emit_vsm(expr: Expr, words: int) -> str:
    """Conservative GRF allocation; no spills, FMA fusion or cross-PE moves yet."""
    output = []
    # Keep the coefficient in T across chunks: one immediate instruction for
    # the entire local vector, rather than one per group of eight Floats.
    if (
        expr.op == "mul"
        and any(a.op == "input" for a in expr.args)
        and any(a.op == "const" for a in expr.args)
    ):
        coefficient = next(a for a in expr.args if a.op == "const")
        output.append(f'imm f"{float(f32(coefficient.value))!r}" $t')
        for base in range(0, words, 8):
            operand = "$aluf" if base == 0 else "$t"
            output.append(f"fvmul {operand} $lm{base}v $ln{base}v")
        return "\n".join(output) + "\n"
    for base in range(0, words, 8):
        registers, lines = {}, []

        def emit(
            node: Expr,
            final: bool = False,
            *,
            base=base,
            registers=registers,
            lines=lines,
        ) -> str:
            if node.op == "input":
                return f"$lm{base}v"
            if node in registers:
                return registers[node]
            sources = [emit(arg) for arg in node.args]
            slot = len(registers) * 8
            if slot >= 512:
                raise CompileError("GRF allocation exceeds 256 long words")
            destination = f"$ln{base}v" if final else f"$lr{slot}v"
            registers[node] = destination
            if node.op == "const":
                lines.append(f'imm f"{float(f32(node.value))!r}" {destination}')
            else:
                lhs, rhs = sources
                if node.op == "sub":
                    rhs = "-" + rhs
                lines.append(f"fpassa {lhs} $nowrite")
                lines.append(
                    f"fv{'mul' if node.op == 'mul' else 'add'} $aluf {rhs} {destination}"
                )
            if not final:
                lines.extend(["nop", "nop"])
            return destination

        if expr.op == "input":
            lines.append(f"fpassa $lm{base}v $ln{base}v")
        else:
            emit(expr, final=True)
        output.extend(lines)
    return "\n".join(output) + "\n"


@dataclass
class Compilation:
    vsm: str
    llvm_ir: str
    semantic_ir: dict
    report: dict

    def write(self, output: Path | str) -> None:
        directory = Path(output)
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "kernel.vsm").write_text(self.vsm, encoding="utf-8")
        (directory / "kernel.ll").write_text(self.llvm_ir, encoding="utf-8")
        (directory / "semantic.json").write_text(
            json.dumps(self.semantic_ir, indent=2) + "\n", encoding="utf-8"
        )
        (directory / "report.json").write_text(
            json.dumps(self.report, indent=2) + "\n", encoding="utf-8"
        )


def compile_source(
    source: str,
    *,
    domain: tuple[float, float],
    atol: float,
    words: int = 8,
    opt: str = "opt",
    assembler: str | None = None,
) -> Compilation:
    if (
        len(domain) != 2
        or not all(math.isfinite(x) for x in domain)
        or domain[0] > domain[1]
        or max(abs(x) for x in domain) > MAX_FLOAT
    ):
        raise CompileError("Expected an ordered finite Float input domain")
    if not math.isfinite(atol) or atol < 0:
        raise CompileError("atol must be finite and nonnegative")
    if type(words) is not int or words <= 0 or words % 8 or words > 4096:
        raise CompileError("words must be a positive multiple of 8, at most 4096")
    if shutil.which(opt) is None:
        raise CompileError(f"LLVM opt not found: {opt}")
    name, original = parse_source(source)
    polynomial = original.polynomial()
    radius = max(abs(Q(x)) for x in domain)
    candidates = [("source", original)]
    candidates += [
        (f"horner-degree-{degree}", horner(trim(polynomial[: degree + 1])))
        for degree in range(len(polynomial))
    ]
    records, feasible = [], []
    for label, expr in candidates:
        try:
            llvm, optimized = optimize(expr, opt)
            approximation = magnitude(
                add(polynomial, optimized.polynomial(), -1), radius
            )
            rounding = arithmetic_error(optimized, radius)
            bound = approximation + rounding
            vsm = emit_vsm(optimized, words)
            count = len(vsm.splitlines())
            if assembler:
                assembled = subprocess.run(
                    [assembler, "--instruction-mode", "flat"],
                    check=False,
                    input=vsm,
                    text=True,
                    capture_output=True,
                )
                if assembled.returncode:
                    raise CompileError(
                        f"Assembler rejected candidate: {assembled.stderr.strip()}"
                    )
                count = sum(
                    line.startswith(("j ", "m "))
                    for line in assembled.stdout.splitlines()
                )
                if count == 0:
                    raise CompileError("Assembler produced no instruction words")
            record = {
                "name": label,
                "lines": count,
                "error_bound": str(bound),
                "approximation_bound": str(approximation),
                "arithmetic_bound": str(rounding),
                "feasible": bound <= Q(atol),
            }
            records.append(record)
            if record["feasible"]:
                feasible.append((count, bound, label, vsm, llvm, optimized))
        except CompileError as exc:
            records.append({"name": label, "feasible": False, "rejection": str(exc)})
    if not feasible:
        raise CompileError(
            "No candidate meets the error budget; " + json.dumps(records)
        )
    count, bound, label, vsm, llvm, optimized = min(feasible, key=lambda item: item[:3])
    report = {
        "function": name,
        "domain": list(domain),
        "atol": atol,
        "words_per_pe": words,
        "reference": "real polynomial at finite normal-or-zero MN-Core Float inputs",
        "chosen": label,
        "lines": count,
        "error_bound": str(bound),
        "error_bound_float": float(bound),
        "bound_kind": "rational whole-domain bound conditional on MN Float operation model",
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "minimum over the enumerated source and truncated Horner candidates only",
        "llvm_version": subprocess.check_output(
            [opt, "--version"], text=True
        ).splitlines()[0],
        "fast_math": False,
        "candidates": records,
    }
    return Compilation(
        vsm,
        llvm,
        {
            "schema_version": 1,
            "source": original.to_dict(),
            "selected": optimized.to_dict(),
            "polynomial": [str(c) for c in polynomial],
        },
        report,
    )
