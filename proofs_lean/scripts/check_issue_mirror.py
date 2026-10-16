"""Guard the Lean PE-issue projection against Rust parser enum drift.

This checks constructor inventories, ALU source counts, the Rust/Lean parser
source-limit rules, and declared projection buckets. It does not prove Rust
parser behavior or semantic correspondence.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
VSM = (REPO / "viz/core/src/vsm.rs").read_text()
ISSUE = (REPO / "viz/core/src/issue.rs").read_text()
BLOCK = (REPO / "viz/core/src/blockop.rs").read_text()
MV = (REPO / "viz/core/src/mv.rs").read_text()
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


def rust_struct_fields(source: str, name: str) -> set[str]:
    match = re.search(rf"\bstruct\s+{re.escape(name)}\s*\{{(.*?)\n\}}", source, re.S)
    if not match:
        raise ValueError(f"Rust struct {name} not found")
    body = re.sub(r"(?m)^\s*///.*$", "", match.group(1))
    return set(re.findall(r"(?m)^\s*pub\s+([A-Za-z_][A-Za-z0-9_]*)\s*:", body))


def lean_struct_fields(name: str) -> set[str]:
    match = re.search(rf"structure\s+{re.escape(name)}\s+where(.*?)(?=\n(?:inductive|structure|def|theorem|end)\b)", LEAN, re.S)
    if not match:
        raise ValueError(f"Lean structure {name} not found")
    return set(re.findall(r"(?m)^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:", match.group(1)))


def rust_struct_field_types(source: str, name: str) -> dict[str, str]:
    match = re.search(rf"\bstruct\s+{re.escape(name)}\s*\{{(.*?)\n\}}", source, re.S)
    if not match:
        raise ValueError(f"Rust struct {name} not found")
    body = re.sub(r"(?m)^\s*///.*$", "", match.group(1))
    return dict(re.findall(r"(?m)^\s*pub\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^,]+),", body))


def lean_struct_field_types(name: str) -> dict[str, str]:
    match = re.search(rf"structure\s+{re.escape(name)}\s+where(.*?)(?=\n(?:inductive|structure|def|theorem|end)\b)", LEAN, re.S)
    if not match:
        raise ValueError(f"Lean structure {name} not found")
    return dict(re.findall(r"(?m)^\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+)$", match.group(1)))


def enum_matches(source: str, rust_name: str, lean_name: str,
                 mapping: dict[str, str | None]) -> None:
    actual = rust_variants(source, rust_name)
    expected = set(mapping)
    if actual != expected:
        raise ValueError(
            f"{rust_name} inventory drift: missing mapping={sorted(actual - expected)}, "
            f"stale mapping={sorted(expected - actual)}"
        )
    constructors = lean_constructors(lean_name)
    missing = {name for name in mapping.values() if name is not None} - constructors
    if missing:
        raise ValueError(f"{lean_name} lacks mapped constructors: {sorted(missing)}")


def struct_fields_match(source: str, rust_name: str, lean_name: str,
                        mapping: dict[str, str]) -> None:
    actual = rust_struct_fields(source, rust_name)
    if actual != set(mapping):
        raise ValueError(f"{rust_name} field drift: missing mapping={sorted(actual - set(mapping))}, "
                         f"stale mapping={sorted(set(mapping) - actual)}")
    lean = lean_struct_fields(lean_name)
    missing = set(mapping.values()) - lean
    if missing:
        raise ValueError(f"{lean_name} lacks mapped fields: {sorted(missing)}")


def struct_field_types_match(source: str, rust_name: str, lean_name: str,
                             mapping: dict[str, tuple[str, str, str]]) -> None:
    rust_types = rust_struct_field_types(source, rust_name)
    lean_types = lean_struct_field_types(lean_name)
    for rust_field, (lean_field, expected_rust_type, expected_lean_type) in mapping.items():
        if rust_field not in rust_types:
            raise ValueError(f"{rust_name} lacks field {rust_field}")
        if rust_types[rust_field] != expected_rust_type:
            raise ValueError(f"{rust_name}.{rust_field} type drift: expected {expected_rust_type}, "
                             f"found {rust_types[rust_field]}")
        if lean_field not in lean_types:
            raise ValueError(f"{lean_name} lacks field {lean_field}")
        if lean_types[lean_field] != expected_lean_type:
            raise ValueError(f"{lean_name}.{lean_field} type drift: expected {expected_lean_type}, "
                             f"found {lean_types[lean_field]}")


def enum_struct_variant_matches(source: str, rust_enum: str, lean_enum: str,
                                rust_variant: str, lean_variant: str,
                                fields: tuple[tuple[str, str, str, str], ...]) -> None:
    enum_match = re.search(rf"\benum\s+{re.escape(rust_enum)}\s*\{{(.*?)\n\}}", source, re.S)
    if not enum_match:
        raise ValueError(f"Rust enum {rust_enum} not found")
    variant_match = re.search(rf"(?m)^\s*{re.escape(rust_variant)}\s*\{{([^}}]*)\}}", enum_match.group(1))
    if not variant_match:
        raise ValueError(f"Rust {rust_enum}::{rust_variant} payload not found")
    rust_fields = dict(re.findall(r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^,]+)", variant_match.group(1)))
    lean_enum_match = re.search(
        rf"inductive\s+{re.escape(lean_enum)}\s+where(.*?)(?=\n(?:inductive|structure|def|theorem|end)\b)",
        LEAN, re.S)
    if not lean_enum_match:
        raise ValueError(f"Lean enum {lean_enum} not found")
    lean_line = re.search(rf"(?m)^\s*\|\s*{re.escape(lean_variant)}\s+(.+)$", lean_enum_match.group(1))
    if not lean_line:
        raise ValueError(f"Lean {lean_enum}::{lean_variant} payload not found")
    lean_payload = lean_line.group(1).strip()
    expected_parts = []
    for rust_field, lean_field, rust_type, lean_type in fields:
        if rust_fields.get(rust_field, "").strip() != rust_type:
            raise ValueError(f"Rust {rust_enum}::{rust_variant}.{rust_field} type drift")
        expected_parts.append(f"({lean_field} : {lean_type})")
    expected = " ".join(expected_parts)
    if lean_payload != expected:
        raise ValueError(f"Lean {lean_enum}::{lean_variant} payload drift: expected {expected}, "
                         f"found {lean_payload}")


def rust_alu_input_counts() -> dict[str, int]:
    match = re.search(r"const ALU_OPS:.*?= &\[(.*?)\n\];", VSM, re.S)
    if not match:
        raise ValueError("Rust ALU_OPS table not found")
    rows = re.findall(r'\("([a-z0-9]+)",\s*AluOp::([A-Za-z0-9_]+),\s*AluType::[A-Za-z0-9_]+,\s*(\d+)\)', match.group(1))
    counts = {variant[0].lower() + variant[1:]: int(count) for _, variant, count in rows}
    names = {name for name, _, _ in rows}
    if len(counts) != len(rows) or len(names) != len(rows):
        raise ValueError("duplicate Rust ALU opcode or variant in ALU_OPS")
    return counts


def lean_alu_input_counts() -> dict[str, int]:
    match = re.search(r"def ParsedAluName\.inputCount.*?\n(?=theorem\b)", LEAN, re.S)
    if not match:
        raise ValueError("Lean ParsedAluName.inputCount definition not found")
    counts: dict[str, int] = {}
    for group, count in re.findall(r"\|\s*((?:\.[A-Za-z][A-Za-z0-9_]*(?:\s*\|\s*)?)+)\s*=>\s*(\d+)", match.group(0)):
        for name in re.findall(r"\.([A-Za-z][A-Za-z0-9_]*)", group):
            if name in counts:
                raise ValueError(f"duplicate Lean ALU input count for {name}")
            counts[name] = int(count)
    return counts


def validate_alu_input_counts() -> None:
    rust, lean = rust_alu_input_counts(), lean_alu_input_counts()
    if rust != lean:
        raise ValueError(f"ALU input count drift: rust-only={rust.items() - lean.items()}, "
                         f"lean-only={lean.items() - rust.items()}")


def validate_parser_source_limits() -> None:
    """Guard the complete Rust parse_expr source split against the Lean limit table."""
    rust_match = re.search(r"let n_in = match &op\s*\{(.*?)\n\s*\};", VSM, re.S)
    if not rust_match:
        raise ValueError("Rust parse_expr source-count match not found")
    lean_match = re.search(
        r"def ParsedOp\.parserSourceLimit : ParsedOp → Nat(.*?)(?=\ntheorem\b)", LEAN, re.S)
    if not lean_match:
        raise ValueError("Lean ParsedOp.parserSourceLimit definition not found")
    compact = lambda source: re.sub(r"\s+", "", source)
    rust, lean = compact(rust_match.group(1)), compact(lean_match.group(1))
    rust_rules = (
        "Op::Alu{name,..}=>name.inputs(),",
        "Op::Mau{matrix,kind,..}=>match(matrix,kind){(_,MauKind::Fma)=>3,(_,MauKind::Mul)|(false,MauKind::Add)=>2,_=>1,},",
        "Op::MatWrite{..}|Op::MatRead{..}=>1,",
        "_=>0,",
    )
    lean_rules = (
        "|.aluname..=>name.inputCount",
        "|.immediate..|.zero|.wait..|.noforward=>0",
        "|.mau_matrixkind..=>matchmatrix,kindwith|_,.fma=>3|_,.mul=>2|false,.add=>2|_,_=>1",
        "|.matrixWrite..|.matrixRead..=>1",
        "|.l1bm..|.l2bm..=>1",
    )
    missing_rust = [rule for rule in rust_rules if rule not in rust]
    missing_lean = [rule for rule in lean_rules if rule not in lean]
    if missing_rust or missing_lean:
        raise ValueError(f"parser source-limit rule drift: Rust={missing_rust}, Lean={missing_lean}")


def validate_mask_application_rules() -> None:
    rust_check = re.search(r"pub fn check\(exprs: &\[Expr\]\).*?\n\}", ISSUE, re.S)
    rust_masks = re.search(r"fn mask_applications_agree\(exprs: &\[Expr\]\).*?\n\}", ISSUE, re.S)
    if not rust_check or "mask_applications_agree(exprs)" not in rust_check.group(0):
        raise ValueError("Rust issue checker omits the mask-application rule")
    if not rust_masks:
        raise ValueError("Rust mask-application rule implementation is missing")
    rust_body = rust_masks.group(0)
    if "mask.ll" not in rust_body or "MaskSource::Entry" not in rust_body:
        raise ValueError("Rust mask-application rule must compare widths and variable entries")
    legal = re.search(r"def Legal \(xs : List Expr\) : Prop :=(.*?)(?=\n(?:theorem|\/--|noncomputable)\b)", LEAN, re.S)
    projection = re.search(r"def ParsedExpr\.toIssueExpr.*?\n(?=theorem\b)", LEAN, re.S)
    if not legal or "maskWidthsAgree xs" not in legal.group(1) or "maskEntriesAgree xs" not in legal.group(1):
        raise ValueError("Lean Legal omits mask width or variable-entry agreement")
    if not projection or "maskApplications := e.maskApplications" not in projection.group(0):
        raise ValueError("Lean issue projection omits parsed mask applications")


def validate_mask_register_write_rule() -> None:
    rust_check = re.search(r"pub fn check\(exprs: &\[Expr\]\).*?\n\}", ISSUE, re.S)
    if not rust_check or "mask_writes > 1" not in rust_check.group(0):
        raise ValueError("Rust issue checker omits the mask-register single-write-port rule")
    legal = re.search(r"def Legal \(xs : List Expr\) : Prop :=(.*?)(?=\n(?:theorem|\/--|noncomputable)\b)", LEAN, re.S)
    projection = re.search(r"def ParsedExpr\.toIssueExpr.*?\n(?=theorem\b)", LEAN, re.S)
    if not legal or "maskRegisterWritesUnique xs" not in legal.group(1):
        raise ValueError("Lean Legal omits mask-register write uniqueness")
    if not projection or "omrWrites := e.maskRegisterWrites" not in projection.group(0):
        raise ValueError("Lean projection omits mask-register destination writes")


def validate_lbf_write_rule() -> None:
    rust_check = re.search(r"pub fn check\(exprs: &\[Expr\]\).*?\n\}", ISSUE, re.S)
    if not rust_check or "lbf_writes > 1" not in rust_check.group(0):
        raise ValueError("Rust issue checker omits the single-LBF-write rule")
    legal = re.search(r"def Legal \(xs : List Expr\) : Prop :=(.*?)(?=\n(?:theorem|\/--|noncomputable)\b)", LEAN, re.S)
    projection = re.search(r"def ParsedExpr\.toIssueExpr.*?\n(?=theorem\b)", LEAN, re.S)
    if not legal or "lbfWritesUnique xs" not in legal.group(1):
        raise ValueError("Lean Legal omits LBF write uniqueness")
    if not projection or "lbfWrites := if e.writesLbf then 1 else 0" not in projection.group(0):
        raise ValueError("Lean projection omits implicit LBF writes")


def validate_output_conflict_rules() -> None:
    rust_check = re.search(r"pub fn check\(exprs: &\[Expr\]\).*?\n\}", ISSUE, re.S)
    if not rust_check or "e.dsts.len() != 1" not in rust_check.group(0):
        raise ValueError("Rust issue checker omits `$nowrite` destination exclusivity")
    if "std::ptr::eq" in rust_check.group(0):
        raise ValueError("Rust issue checker must reject duplicate banks within one expression")
    legal = re.search(r"def Legal \(xs : List Expr\) : Prop :=(.*?)(?=\n(?:theorem|\/--|noncomputable)\b)", LEAN, re.S)
    projection = re.search(r"def ParsedExpr\.toIssueExpr.*?\n(?=theorem\b)", LEAN, re.S)
    if not legal or "nowriteOutputsUnique xs" not in legal.group(1):
        raise ValueError("Lean Legal omits `$nowrite` destination exclusivity")
    if "(e.writes.map Access.bank).Nodup" not in LEAN:
        raise ValueError("Lean issue predicate omits within-expression destination uniqueness")
    if not projection or "nowriteOutputValid := e.nowriteOutputValid" not in projection.group(0):
        raise ValueError("Lean projection omits `$nowrite` output validation")


def validate() -> None:
    validate_alu_input_counts()
    validate_parser_source_limits()
    validate_mask_application_rules()
    validate_mask_register_write_rule()
    validate_lbf_write_rule()
    validate_output_conflict_rules()
    parse_expr = re.search(r"fn parse_expr\(part: &str\).*?\n\}", VSM, re.S)
    if not parse_expr or "classify(&opcode).ok_or_else" not in parse_expr.group(0):
        raise ValueError("unknown PE opcode must fail parse_expr classification")
    if "Op::Other" in parse_expr.group(0):
        raise ValueError("parse_expr must not construct the API-only Op::Other variant")
    enum_matches(VSM, "Op", "ParsedOp", {
        "Alu": "alu", "Imm": "immediate", "Zero": "zero", "Mau": "mau",
        "MatWrite": "matrixWrite", "MatRead": "matrixRead", "Wait": "wait",
        # `Op::Other` is an API-only fallback: parse_expr returns Err for unknown opcodes.
        "Noforward": "noforward", "L1": "l1bm", "L2": "l2bm", "Other": None,
    })
    enum_matches(VSM, "Operand", "ParsedOperand", {
        "Mem": "mem", "Bar": "bar", "Forward": "forward", "Fixed": "fixed",
        "Omr": "omr", "Mat": "matrix", "Nowrite": "nowrite", "L1bm": "l1bm",
        "L2bm": "l2bm", "Dar": "dar", "Raw": None,
    })
    if "Operand::Raw(tok.to_string())" not in VSM:
        raise ValueError("Rust Raw operand fallback changed; reassess the legal-operand boundary")
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
    enum_matches(MV, "MvKind", "ParsedMvKind", {
        "P": "copy", "B": "broadcast", "B2": "broadcast2", "B4": "broadcast4",
        "D": "distribute", "R": "reduce", "R2": "reduce2", "R4": "reduce4",
        "Nop": "nop",
    })
    enum_matches(MV, "MvOperand", "ParsedMvOperand", {
        "Pdm": "pdm", "Dram": "dram", "L2bm": "l2bm",
    })
    enum_struct_variant_matches(MV, "MvOperand", "ParsedMvOperand", "Pdm", "pdm", (
        ("addr", "address", "u64", "Fin (2 ^ 64)"),
        ("group", "group", "Option<u8>", "Option (Fin 256)"),
    ))
    enum_struct_variant_matches(MV, "MvOperand", "ParsedMvOperand", "Dram", "dram", (
        ("addr", "address", "u64", "Fin (2 ^ 64)"),
        ("group", "group", "Option<u8>", "Option (Fin 256)"),
        ("indirect", "indirect", "bool", "Bool"),
    ))
    enum_struct_variant_matches(MV, "MvOperand", "ParsedMvOperand", "L2bm", "l2bm", (
        ("addr", "address", "u64", "Fin (2 ^ 64)"),
        ("group", "group", "Option<u8>", "Option (Fin 256)"),
        ("l2b", "l2b", "Option<u8>", "Option (Fin 256)"),
    ))
    struct_fields_match(MV, "Mv", "ParsedMv", {
        "kind": "kind", "size": "size", "tag": "tag", "nd": "nd",
        "priority": "priority", "src": "source", "dst": "destination", "text": "text",
    })
    struct_field_types_match(MV, "Mv", "ParsedMv", {
        "kind": ("kind", "MvKind", "ParsedMvKind"),
        "size": ("size", "u64", "Fin (2 ^ 64)"),
        "tag": ("tag", "Option<u8>", "Option (Fin 256)"),
        "nd": ("nd", "Option<u32>", "Option (Fin (2 ^ 32))"),
        "priority": ("priority", "u8", "Fin 256"),
        "src": ("source", "Option<MvOperand>", "Option ParsedMvOperand"),
        "dst": ("destination", "Option<MvOperand>", "Option ParsedMvOperand"),
        "text": ("text", "String", "String"),
    })
    for variant in ("Alu", "Imm", "Zero", "Mau", "MatWrite", "MatRead", "Wait",
                    "Noforward", "L1", "L2", "Other"):
        if not re.search(rf"Op::{variant}\b", ISSUE):
            raise ValueError(f"issue.rs does not classify Op::{variant}")
    print("PASS: Rust/Lean instruction constructors, source limits, and mask-issue rules match; Op::Other is parser-unreachable.")


if __name__ == "__main__":
    validate()
