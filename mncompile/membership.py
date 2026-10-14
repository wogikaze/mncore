"""Bounded integer membership rewritten to distributed dense lookup tables."""

import ast
import subprocess
from dataclasses import asdict

from .compiler import Compilation, CompileError
from .maps import Tensor, measure


def membership_names(source):
    module = ast.parse(source)
    if len(module.body) != 1 or not isinstance(module.body[0], ast.FunctionDef):
        raise CompileError("Expected a membership function")
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
        raise CompileError("Expected a pure two-input membership map")
    result = fn.body[0].value
    if not isinstance(result, ast.ListComp) or len(result.generators) != 1:
        raise CompileError("Expected a list comprehension")
    generator = result.generators[0]
    if (
        generator.ifs
        or generator.is_async
        or not isinstance(generator.target, ast.Name)
        or not isinstance(generator.iter, ast.Name)
        or not isinstance(result.elt, ast.Call)
        or not isinstance(result.elt.func, ast.Name)
        or result.elt.func.id != "int"
        or result.elt.keywords
        or len(result.elt.args) != 1
        or not isinstance(result.elt.args[0], ast.Compare)
    ):
        raise CompileError("Expected int(value in members) for each query")
    test = result.elt.args[0]
    if (
        len(test.ops) != 1
        or not isinstance(test.ops[0], ast.In)
        or len(test.comparators) != 1
        or not isinstance(test.left, ast.Name)
        or test.left.id != generator.target.id
        or not isinstance(test.comparators[0], ast.Name)
    ):
        raise CompileError("Expected an input-tensor membership test")
    names = generator.iter.id, test.comparators[0].id
    if len(set(names)) != 2 or set(names) != {arg.arg for arg in fn.args.args}:
        raise CompileError("Membership tensors must match function parameters")
    return fn.name, names


def compile_membership(
    source: str, *, inputs: dict[str, Tensor], output: Tensor, opt="opt", assembler=None
):
    name, (queries_name, members_name) = membership_names(source)
    if set(inputs) != {queries_name, members_name}:
        raise CompileError("Membership bindings do not match source inputs")
    queries, members = inputs[queries_name], inputs[members_name]
    if (
        queries.dtype != members.dtype
        or queries.dtype != output.dtype
        or queries.dtype != "u64"
        or queries.elements != members.elements
        or queries.elements != output.elements
        or queries.elements != 16
        or queries.memory != "m"
        or members.memory != "n"
        or output.memory != "n"
        or min(queries.minimum, members.minimum) < 0
        or max(queries.maximum, members.maximum) > 1000
        or queries.offset + 32 > 1024
        or not (
            output.offset >= members.offset + 32 or output.offset + 32 <= members.offset
        )
    ):
        raise CompileError(
            "Dense membership currently supports 16 local UInt64 queries and members in [0,1000] with nonoverlapping B/output layouts"
        )
    ir = "define i64 @membership_term(i64 %query, i64 %candidate) {\n  %equal = icmp eq i64 %query, %candidate\n  %value = zext i1 %equal to i64\n  ret i64 %value\n}\n"
    optimized = subprocess.run(
        [opt, "-S", "-passes=instcombine,early-cse,dce", "-o", "-", "-"],
        check=False,
        input=ir,
        text=True,
        capture_output=True,
    )
    if optimized.returncode:
        raise CompileError(optimized.stderr)
    a, b, c = queries.offset, members.offset, output.offset
    packets = [
        f"lpassa $ln{b}v $t; l1bmm@0 $llm{a}v $llbi",
        'imm h"1.5" $llr4v; l1bmm $llbi $lls0v',
        f"fvpassa $aluf $mt1024; lpassa $ln{b + 8}v $t",
        "hbfn/9 $llr4v $llr24v",
        f"hvpassa $r4 $mt1024; lpassa $ln{b + 16}v $t",
        "hmwrite $llr24 $lx0",
        f"hvpassa $r4 $mt1024; lpassa $ln{b + 24}v $t",
        "nop",
        "hvpassa $r4 $mt1024; lpassa $ls0v $t",
        "nop",
        "linc $lr96v $ls96v; l1bmd $ls8v $lbi",
        "hmmul $lx $mt1024 $r0v; l1bmd $lbi $t",
        f"l1bmd $lm{a + 16}v $lbi",
        "hmmul $lx $mt1024 $r4v; l1bmd $lbi $t",
        f"l1bmd $lm{a + 24}v $lbi",
        "hmmul $lx $mt1024 $r16v; l1bmrior $lr0v $lbi; l1bmd $lbi $t",
        f"l1bmm $lbi $n{c + 1}v4",
        f"hmmul $lx $mt1024 $r20v; l1bmrior $r16v $lbi; land $lbf $ls96 $ln{c + 2}v4",
        f"l1bmrior $mauf $lbi; l1bmm $lbi $n{c + 17}v2",
        f"l1bmm $lbi $n{c + 25}v2",
    ]
    vsm = "\n".join(packets) + "\n"
    report = {
        "function": name,
        "reference": "integer membership using a dense bounded lookup set",
        "lines": measure(vsm, assembler),
        "error_bound": "0",
        "fast_math": False,
        "inputs": {queries_name: asdict(queries), members_name: asdict(members)},
        "output": asdict(output),
        "preconditions": [
            "queries are one row per L2B/L1B replicated across MABs/PEs",
            "members span MAB/PE and are replicated across L1B/L2B",
            "standalone zero-initialized scratch/output memory",
        ],
        "clobbers": [
            "LM0 dense table at words 1024..2024",
            "T/GRF/matrix/L1BM scratch",
        ],
        "cost_kind": "assembled j+m words"
        if assembler
        else "emitted instruction lines (not assembled)",
        "optimality": "selected dense-universe lookup and membership reduction schedule",
    }
    return Compilation(
        vsm,
        optimized.stdout,
        {
            "schema_version": 1,
            "op": "membership",
            "universe": [0, 1000],
            "global_members": 1024,
            "queries_per_l2b_l1b": 16,
            "lookup_word_base": 1024,
        },
        report,
    )
