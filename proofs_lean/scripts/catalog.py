"""Inventory withdrawn claims and explicit formalization gaps. No promotion heuristics."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ARCHIVE = ROOT / "archive/2026-10-15-arithmetic-claims"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def archive_valid() -> None:
    hashes = json.loads((ARCHIVE / "sha256.json").read_text())
    for relative, expected in hashes.items():
        if digest(ARCHIVE / relative) != expected:
            raise ValueError(f"archived source changed: {relative}")


def problem_catalog() -> dict:
    archive_valid()
    table = (ARCHIVE / "ProofsLean/Table.lean").read_text()
    legacy = re.findall(r'\{name := "([^"]+)", ref := (\d+), gen := (\d+), verdict := \.(\w+)\}', table)
    dirs = []
    for parent in (REPO / "problems/challenge", REPO / "problems"):
        dirs.extend(sorted((p for p in parent.glob("[0-9]*.*") if (p / "problem.md").exists()),
                           key=lambda p: int(p.name.split(".")[0])))
    if len(legacy) != 73 or len(dirs) != 73:
        raise ValueError("the audit must cover all 25 Challenge and 48 MNIST problems")
    progress = json.loads((REPO / "mncompile/benchmarks/results/progress.json").read_text())
    scores = {r["problem"]: r for r in progress["problems"]}
    observations = {}
    for path in sorted((ROOT / "evidence").glob("*/judge.json")):
        record = json.loads(path.read_text())
        if record["proves_optimality"] or record["proves_all_input_correctness"]:
            raise ValueError(f"execution evidence cannot establish a universal theorem: {path}")
        if digest(path.parent / record["solution"]) != record["solution_sha256"]:
            raise ValueError(f"frozen witness changed: {path}")
        for case in record["cases"]:
            if digest(REPO / case["path"]) != case["sha256"]:
                raise ValueError(f"observed testcase changed: {path}")
        accepted = bool(record["cases"]) and all(c["judge"]["accepted"] for c in record["cases"])
        observations.setdefault(record["problem"], []).append({
            "source": path.relative_to(REPO).as_posix(), "sha256": digest(path),
            "evidence_kind": record["evidence_kind"], "accepted": accepted,
            "score": max(c["judge"]["score"] for c in record["cases"]) if accepted else None,
        })
    problems = []
    for directory, (name, ref, gen, verdict) in zip(dirs, legacy):
        if directory.name.split(".")[0] != name.split(".")[0]:
            raise ValueError(f"legacy table mapping mismatch: {name}, {directory}")
        row = scores[directory.name]
        problem_id = directory.relative_to(REPO).as_posix()
        extra = observations.get(problem_id, [])
        kernel = REPO / "mncompile/benchmarks/results" / directory.name / "kernel.vsm"
        problems.append({
            "id": problem_id,
            "specification_sha256": digest(directory / "problem.md"),
            "legacy": {"name": name, "reference_lines": int(ref), "generated_lines": int(gen),
                       "verdict": verdict, "claim_status": "withdrawn"},
            "formal_status": "unproven",
            "formal_specification": None,
            "full_isa_certificate": None,
            "restricted_model_certificate": None,
            "additional_official_observations": extra,
            "known_testcase_upper_bound": min([row["lines"]] + [o["score"] for o in extra if o["accepted"]]),
            "observed_upper_bound": {
                "score": row.get("lines"), "mode": row.get("mode", "general"),
                "kernel_sha256": digest(kernel),
                "source": "mncompile/benchmarks/results/progress.json",
                "evidence_kind": "stored_official_judge_record_not_a_formal_proof",
                "accepted": row["status"] == "accepted",
            },
        })
    return {
        "schema_version": 1,
        "full_isa_optimality_proven": 0,
        "restricted_mncore_optimality_proven": 0,
        "legacy_claims_withdrawn": sum(p["legacy"]["verdict"] == "optimalProven" for p in problems),
        "program_count": len(problems),
        "scope": "All 73 problems remain open for formal optimality; Accepted programs are upper bounds only.",
        "problems": problems,
    }


def coverage_catalog() -> dict:
    path = REPO / "mncompile/machine.py"
    tree = ast.parse(path.read_text())
    namespace = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in ("ALU_OPS", "ALU_PRECISIONS", "UNSIGNED_OK"):
                namespace[name] = ast.literal_eval(node.value)
    definitions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in ("alu_opcodes", "mau_opcodes")]
    exec(compile(ast.Module(body=definitions, type_ignores=[]), str(path), "exec"), namespace)
    spellings = sorted(set(namespace["alu_opcodes"]() + namespace["mau_opcodes"]()))
    areas = [
        "instruction_encoding_and_all_legal_operands", "parallel_issue_and_memory_port_legality",
        "integer_16_32_64_and_signedness", "floating_16_32_64_rounding_and_special_values",
        "block_floating_conversion_and_mantissa_width", "wide_access_and_lsb_passthrough",
        "immediates_fixed_operands_and_zero", "masks_flush_and_mask_directives",
        "forwarding_lifetime_and_latency", "t_indirect_madpe_and_address_mapping",
        "matrix_registers_and_matrix_operations", "pe_rotations_and_coordinate_operands",
        "l1bm_transfers_turnaround_and_reductions", "l2bm_transfers_and_reductions",
        "mv_dram_pdm_all_transfer_and_reduction_modes", "dar_tags_wait_and_completion",
        "initial_state_and_zero_memory", "scoring_and_zero_cost_directive_normalization",
        "reference_binary_conformance", "all_73_formal_problem_specifications",
    ]
    fragment_source = ROOT / "ProofsLean/IntegerALU.lean"
    reference = ROOT / "evidence/integer-alu/reference.json"
    experiment = None
    if reference.exists():
        record = json.loads(reference.read_text())
        vectors = reference.with_name("vectors.tsv")
        if digest(vectors) != record["vectors_sha256"]:
            raise ValueError("integer ALU reference vectors changed")
        if record["cases"] != len(vectors.read_text().splitlines()):
            raise ValueError("integer ALU reference case count mismatch")
        if record["matched"] != record["cases"] or record["differences"]:
            raise ValueError("integer ALU reference comparison has unresolved differences")
        for item in record["sources"]:
            source = REPO / item["path"]
            optional_tool = item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3",
                "judge/judge-py/mncore2_emuenv/gpfn3_package_main")
            if optional_tool and not source.exists():
                continue  # Official proprietary binaries are not distributed in CI.
            if digest(source) != item["sha256"]:
                raise ValueError(f"stale integer ALU comparison: {item['path']}")
        if any(record[key] for key in ("proves_universal_conformance", "proves_isa_completeness", "proves_optimality")):
            raise ValueError("finite comparison cannot promote a universal claim")
        experiment = {"path": reference.relative_to(REPO).as_posix(),
                      "sha256": digest(reference), "cases": record["cases"],
                      "scope": record["scope"], "formal_conformance_proof": False}
    return {
        "schema_version": 1,
        "isa_exhaustiveness_proven": False,
        "full_semantics_implemented": False,
        "compiler_syntax_source": "mncompile/machine.py",
        "compiler_syntax_sha256": digest(path),
        "inventory_scope": "Compiler-generated ALU/MAU spelling candidates only; not an authoritative complete ISA or legality model.",
        "datapath_fragments": [{
            "source": fragment_source.relative_to(REPO).as_posix(), "sha256": digest(fragment_source),
            "implemented": "16/32/64-bit inc/dec/add/sub/not/lnot/and/or/xor/integer max/min/passa; lane packing, replicated flags and LSB bypass",
            "scope": "Already-read and already-reduced buses only; not VSM instruction execution or legality",
            "missing": "Operand decoding/access/reduction, masks, timing/forwarding, parallel issue, all other ISA operations",
            "reference_experiment": experiment,
        }],
        "syntax_candidates": [{"spelling": name, "formal_step_semantics": "unimplemented"} for name in spellings],
        "obligations": [{"area": area, "status": "partial_datapath_only" if area in (
            "integer_16_32_64_and_signedness", "wide_access_and_lsb_passthrough") else "unimplemented"} for area in areas],
    }


def render(value: dict) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, data in (("audit.json", problem_catalog()), ("coverage.json", coverage_catalog())):
        path = ROOT / name
        text = render(data)
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f"stale or fabricated {name}; run proofs_lean/scripts/catalog.py")
        else:
            path.write_text(text)
    print("All 73 problems audited; full-ISA optimality certificates: 0.")


if __name__ == "__main__":
    main()
