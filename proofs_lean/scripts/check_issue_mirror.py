"""Guard the Lean PE-issue projection against Rust parser enum drift.

This checks constructor inventories and the declared projection buckets. It
does not prove Rust parser behavior or semantic correspondence.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
VSM = (REPO / "viz/core/src/vsm.rs").read_text()
ISSUE = (REPO / "viz/core/src/issue.rs").read_text()
BLOCK = (REPO / "viz/core/src/blockop.rs").read_text()
LEAN = (REPO / "proofs_lean/ProofsLean/Issue.lean").read_text()


def rust_variants(source: str, name: str) -> set[str]:
    match = re.search(rf"\benum\s+{re.escape(name)}\s*\{{(.*?)\n\}}", source, re.S)
    if not match:
        raise ValueError(f"Rust enum {name} not found")
    body = re.sub(r"(?m)^\s*///.*$", "", match.group(1))
    body = re.sub(r"(?m)^\s*//.*$", "", body)
    return set(re.findall(r"(?m)^\s*([A-Z][A-Za-z0-9_]*)\s*(?:\{|\(|,)", body))


def lean_constructors(name: str) -> set[str]:
    match = re.search(rf"inductive\s+{re.escape(name)}\s+where(.*?)(?=\n(?:inductive|structure|def|theorem|end)\b)", LEAN, re.S)
    if not match:
        raise ValueError(f"Lean inductive {name} not found")
    return set(re.findall(r"\|\s*([A-Za-z][A-Za-z0-9_]*)", match.group(1)))


def enum_matches(source: str, rust_name: str, lean_name: str, mapping: dict[str, str]) -> None:
    actual = rust_variants(source, rust_name)
    expected = set(mapping)
    if actual != expected:
        raise ValueError(
            f"{rust_name} inventory drift: missing mapping={sorted(actual - expected)}, "
            f"stale mapping={sorted(expected - actual)}"
        )
    constructors = lean_constructors(lean_name)
    missing = set(mapping.values()) - constructors
    if missing:
        raise ValueError(f"{lean_name} lacks mapped constructors: {sorted(missing)}")


def validate() -> None:
    enum_matches(VSM, "Op", "ParsedOp", {
        "Alu": "alu", "Imm": "immediate", "Zero": "zero", "Mau": "mau",
        "MatWrite": "matrixWrite", "MatRead": "matrixRead", "Wait": "wait",
        "Noforward": "noforward", "L1": "l1bm", "L2": "l2bm", "Other": "other",
    })
    enum_matches(VSM, "Operand", "ParsedOperand", {
        "Mem": "mem", "Bar": "bar", "Forward": "forward", "Fixed": "fixed",
        "Omr": "omr", "Mat": "matrix", "Nowrite": "nowrite", "L1bm": "l1bm",
        "L2bm": "l2bm", "Dar": "dar", "Raw": "raw",
    })
    enum_matches(VSM, "MemKind", "Bank", {
        "Lm0": "lm0", "Lm1": "lm1", "Grf0": "grf0", "Grf1": "grf1", "T": "t",
        "L1bm": "l1bm", "L2bm": "l2bm", "Pdm": "pdm", "Dram": "dram", "Omr": "omr",
    })
    enum_matches(VSM, "FwdKind", "ParsedForward", {
        "Aluf": "aluf", "Mauf": "mauf", "Lbf": "lbf", "Mreadf": "mreadf",
    })
    enum_matches(VSM, "FixedKind", "ParsedFixed", {
        "L2bid": "l2bid", "L1bid": "l1bid", "Mabid": "mabid", "Peid": "peid",
        "Subpeid": "subpeid", "Msb1": "msb1",
    })
    enum_matches(VSM, "MauKind", "CalcKind", {
        "Fma": "fma", "Mul": "mul", "Add": "add", "Passa": "passa",
    })
    enum_matches(VSM, "Prec", "ParsedPrecision", {
        "D": "d", "F": "f", "G": "g", "H": "h", "L": "l", "I": "i", "S": "s",
    })
    enum_matches(BLOCK, "RrnOp", "ParsedRrnOp", {
        "Fadd": "fadd", "Max": "max", "Min": "min", "Iadd": "iadd",
        "Band": "band", "And": "and", "Bor": "bor", "Or": "or",
    })
    enum_matches(VSM, "AluOp", "ParsedOp", {
        name: "alu" for name in (
            "Msl", "Msr", "Passa", "Inc", "Dec", "Not", "Lnot", "Rsqrt", "Floor",
            "Ftoi", "Bfe", "Bfn", "Max", "Min", "Packbit", "And", "Or", "Xor",
            "Add", "Sub", "Lsl", "Lsr", "Bsl", "Bsr", "Relu", "Relu0", "Relu1",
            "Relu2", "Relu3", "Lrelud", "Lreluo", "Ilrelud",
        )
    })
    enum_matches(VSM, "AluOp", "ParsedAluName", {
        name: name[0].lower() + name[1:] for name in (
            "Msl", "Msr", "Passa", "Inc", "Dec", "Not", "Lnot", "Rsqrt", "Floor",
            "Ftoi", "Bfe", "Bfn", "Max", "Min", "Packbit", "And", "Or", "Xor",
            "Add", "Sub", "Lsl", "Lsr", "Bsl", "Bsr", "Relu", "Relu0", "Relu1",
            "Relu2", "Relu3", "Lrelud", "Lreluo", "Ilrelud",
        )
    })
    enum_matches(VSM, "MaskSource", "ParsedMask", {
        "Pattern": "pattern", "Entry": "entry",
    })
    enum_matches(BLOCK, "L1Op", "ParsedL1Op", {
        "Pbcast": "pbcast", "Mbcast": "mbcast", "Mwrite": "mwrite",
        "M4bcast": "m4bcast", "M4write": "m4write", "Reduce": "reduce",
        "Reduce4": "reduce4", "Distrib": "distrib", "Gather": "gather",
    })
    enum_matches(BLOCK, "L2Op", "ParsedL2Op", {
        "Bcast": "bcast", "Bcast2": "bcast2", "Distrib": "distrib",
        "FromL1b": "fromL1b", "Reduce": "reduce", "Reduce2": "reduce2",
        "Gather": "gather", "Imcast": "imcast", "Dars": "dars", "Darw": "darw",
    })
    enum_matches(BLOCK, "L1Op", "ParsedOp", {
        "Pbcast": "l1bm", "Mbcast": "l1bm", "Mwrite": "l1bm", "M4bcast": "l1bm",
        "M4write": "l1bm", "Reduce": "l1bm", "Reduce4": "l1bm",
        "Distrib": "l1bm", "Gather": "l1bm",
    })
    enum_matches(BLOCK, "L2Op", "ParsedOp", {
        "Bcast": "l2bm", "Bcast2": "l2bm", "Distrib": "l2bm", "FromL1b": "l2bm",
        "Reduce": "l2bm", "Reduce2": "l2bm", "Gather": "l2bm", "Imcast": "l2bm",
        "Dars": "l2bm", "Darw": "l2bm",
    })
    enum_matches(VSM, "Line", "ParsedLine", {
        "Pe": "pe", "Nop": "nop", "Mv": "mv", "MaskDirective": "maskDirective",
        "DebugSet": "debugSet", "DebugGet": "debugGet", "DramSet": "dramSet",
    })
    for variant in ("Alu", "Imm", "Zero", "Mau", "MatWrite", "MatRead", "Wait",
                    "Noforward", "L1", "L2", "Other"):
        if not re.search(rf"Op::{variant}\b", ISSUE):
            raise ValueError(f"issue.rs does not classify Op::{variant}")
    print("PASS: Rust/Lean issue projection constructor inventories match.")


if __name__ == "__main__":
    validate()
