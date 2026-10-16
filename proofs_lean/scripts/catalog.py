"""Inventory withdrawn claims and explicit formalization gaps. No promotion heuristics."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from collections import Counter
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


def datapath_experiment(directory: str, spelling_column: int, allow_unknown: bool = False) -> dict | None:
    reference = ROOT / "evidence" / directory / "reference.json"
    experiment = None
    if reference.exists():
        record = json.loads(reference.read_text())
        vectors = reference.with_name("vectors.tsv")
        if digest(vectors) != record["vectors_sha256"]:
            raise ValueError("datapath reference vectors changed")
        if record["cases"] != len(vectors.read_text().splitlines()):
            raise ValueError("datapath reference case count mismatch")
        counts = dict(Counter(row.split("\t")[spelling_column] for row in vectors.read_text().splitlines()))
        if counts != record["cases_per_spelling"]:
            raise ValueError("datapath spelling coverage mismatch")
        unresolved = sum(bool(row.get("unresolved")) for row in record.get("records", [])) if allow_unknown else 0
        differences = record.get("differences", [row for row in record.get("records", [])
                                                  if not row["matched"] and not (allow_unknown and row.get("unresolved"))])
        if record["matched"] + unresolved != record["cases"] or differences:
            raise ValueError("datapath reference comparison has unresolved differences")
        if "records" in record:
            if len(record["records"]) != record["cases"]:
                raise ValueError("reference execution record count mismatch")
            if record["matched"] != sum(bool(row["matched"]) for row in record["records"]):
                raise ValueError("reference match count mismatch")
            if allow_unknown and record.get("unresolved") != unresolved:
                raise ValueError("reference unresolved count mismatch")
            for vector, row in zip(vectors.read_text().splitlines(), record["records"]):
                if vector.split("\t")[:3] != [row["unit"], row["scenario"], row["expected"]]:
                    raise ValueError("forwarding record is detached from its expected vector")
                if digest(reference.parent / row["program"]) != row["program_sha256"]:
                    raise ValueError("forwarding reference program changed")
                if allow_unknown and row.get("unresolved"):
                    if row["expected"] != "unknown" or row["matched"]:
                        raise ValueError("unknown semantics cannot be promoted to a passing comparison")
                    continue
                if not row["assembler_accepted"] or row["expected"] != row["observed"] or not row["values_match"]:
                    raise ValueError("unknown/assembly failure cannot be a passing forwarding comparison")
                if row["observed"] == "failure":
                    if row["returncode"] in (0, None) or "forwarding register failed" not in row["diagnostic"]:
                        raise ValueError("unrecognized failure cannot establish a forwarding counterexample")
                elif row["observed"] != "ok" or row["returncode"] != 0:
                    raise ValueError("unclassified forwarding outcome")
        for item in record["sources"]:
            source = REPO / item["path"]
            optional_tool = item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3",
                "judge/judge-py/mncore2_emuenv/gpfn3_package_main")
            if optional_tool and not source.exists():
                continue  # Official proprietary binaries are not distributed in CI.
            if digest(source) != item["sha256"]:
                raise ValueError(f"stale datapath comparison: {item['path']}")
        if any(record[key] for key in ("proves_universal_conformance", "proves_isa_completeness", "proves_optimality")):
            raise ValueError("finite comparison cannot promote a universal claim")
        experiment = {"path": reference.relative_to(REPO).as_posix(),
                      "sha256": digest(reference), "cases": record["cases"],
                      "matched_cases": record["matched"], "unresolved_cases": unresolved,
                      "scope": record["scope"], "formal_conformance_proof": False}
    return experiment


def rotation_discrepancy() -> dict:
    directory = ROOT / "evidence/untyped-alu/initial-manual-assumption"
    for name, expected in json.loads((directory / "sha256.json").read_text()).items():
        if digest(directory / name) != expected:
            raise ValueError(f"changed rotation discrepancy snapshot: {name}")
    record = json.loads((directory / "reference.json").read_text())
    vectors = (directory / "vectors.tsv").read_text().splitlines()
    if digest(directory / "vectors.tsv") != record["vectors_sha256"]:
        raise ValueError("rotation discrepancy vectors changed")
    snapshots = {"proofs_lean/ProofsLean/IntegerALU.lean": "IntegerALU.lean",
                 "proofs_lean/ProofsLean/UntypedALU.lean": "UntypedALU.lean",
                 "proofs_lean/UntypedProbe.lean": "UntypedProbe.lean",
                 "proofs_lean/scripts/check_untyped_reference.py": "check_untyped_reference.py"}
    for item in record["sources"]:
        source = directory / snapshots[item["path"]] if item["path"] in snapshots else REPO / item["path"]
        if not source.exists() and item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3", "judge/judge-py/mncore2_emuenv/gpfn3_package_main"):
            continue
        if digest(source) != item["sha256"]:
            raise ValueError(f"rotation discrepancy source changed: {source}")
    if (record["cases"], record["matched"], len(record["differences"])) != (384, 256, 128):
        raise ValueError("unexpected discrepancy counts")
    for row in record["differences"]:
        if row["oracle"] != vectors[row["index"]]:
            raise ValueError("discrepancy row is detached from its vector")
        fields = row["oracle"].split("\t")
        if fields[1] not in ("msl", "msr") or int(fields[7]) == 0:
            raise ValueError("rotation discrepancy must exercise a nonzero input LSB")
        if row["observed"] != [int(fields[6]), 0, int(fields[8])]:
            raise ValueError("unexpected rotation discrepancy shape")
    return {
        "operations": ["msl", "msr"], "status": "open",
        "manual_reading": "General one-long-word ALU rule says local first-input LSB passes through",
        "reference_observation": "MSB rotates; LSB is zero even for nonzero llr input",
        "canonical_partial_step": "unknown",
        "evidence": (directory / "reference.json").relative_to(REPO).as_posix(),
        "snapshot_manifest_sha256": digest(directory / "sha256.json"),
    }


def mask_model_correction() -> dict:
    directory = ROOT / "evidence/masks/initial-simulator-assumption"
    for name, expected in json.loads((directory / "sha256.json").read_text()).items():
        if digest(directory / name) != expected:
            raise ValueError(f"changed mask-error snapshot: {name}")
    record = json.loads((directory / "reference.json").read_text())
    vectors = (directory / "vectors.tsv").read_text().splitlines()
    if digest(directory / "vectors.tsv") != record["vectors_sha256"]:
        raise ValueError("mask-error vectors changed")
    for item in record["sources"]:
        snapshot = directory / Path(item["path"]).name
        source = snapshot if snapshot.exists() else REPO / item["path"]
        if not source.exists() and item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3", "judge/judge-py/mncore2_emuenv/gpfn3_package_main"):
            continue
        if digest(source) != item["sha256"]:
            raise ValueError(f"mask-error source changed: {source}")
    if (record["cases"], record["matched"], len(record["differences"])) != (768, 756, 12):
        raise ValueError("unexpected mask-error counts")
    if record["manual_profile_disagreements"]:
        raise ValueError("this correction is not a manual/reference discrepancy")
    for row in record["differences"]:
        if row["oracle"] != vectors[row["index"]]:
            raise ValueError("mask error is detached from its vector")
        fields = row["oracle"].split("\t")
        if fields[1] != "l" or fields[2] not in ("write", "both", "directive") or int(fields[5]) != 0:
            raise ValueError("unexpected mask error shape")
        if row["observed"] != [int(fields[13]), int(fields[14]), int(fields[12])]:
            raise ValueError("mask correction does not match observed manual behavior")
    return {
        "operations": ["long write mask"], "status": "corrected_local_simulator_and_lean_model",
        "error": "Legacy local simulator suppressed LSB write for all-zero long mask; official binary writes it",
        "evidence": (directory / "reference.json").relative_to(REPO).as_posix(),
        "snapshot_manifest_sha256": digest(directory / "sha256.json"),
        "corrected_simulator_source_sha256": digest(REPO / "viz/core/src/machine.rs"),
    }


def forwarding_findings() -> dict:
    directory = ROOT / "evidence/forwarding/initial-uniform-assumption"
    for name, expected in json.loads((directory / "sha256.json").read_text()).items():
        if digest(directory / name) != expected:
            raise ValueError(f"changed forwarding-error snapshot: {name}")
    record = json.loads((directory / "reference.json").read_text())
    if (record["cases"], record["matched"]) != (39, 31):
        raise ValueError("unexpected initial forwarding comparison")
    vectors = (directory / "vectors.tsv").read_text().splitlines()
    if digest(directory / "vectors.tsv") != record["vectors_sha256"] or len(record["records"]) != len(vectors):
        raise ValueError("changed forwarding vectors")
    for vector, row in zip(vectors, record["records"]):
        if vector.split("\t")[:3] != [row["unit"], row["scenario"], row["expected"]]:
            raise ValueError("detached initial forwarding record")
        if digest(directory / row["program"]) != row["program_sha256"]:
            raise ValueError("changed initial forwarding program")
    for item in record["sources"]:
        candidate = directory / Path(item["path"]).name
        source = candidate if candidate.exists() else REPO / item["path"]
        if not source.exists() and item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3", "judge/judge-py/mncore2_emuenv/gpfn3_package_main"):
            continue
        if digest(source) != item["sha256"]:
            raise ValueError("changed initial forwarding source")
    bad = [row for row in record["records"] if not row["matched"]]
    if Counter(row["unit"] for row in bad) != {"alu": 1, "mread": 2, "lbf": 5}:
        raise ValueError("unexpected initial forwarding mismatches")
    second = ROOT / "evidence/forwarding/matrix-retention-assumption"
    for name, expected in json.loads((second / "sha256.json").read_text()).items():
        if digest(second / name) != expected:
            raise ValueError("changed matrix-retention hypothesis snapshot")
    second_record = json.loads((second / "reference.json").read_text())
    if (second_record["cases"], second_record["matched"], second_record["unresolved"]) != (40, 33, 5):
        raise ValueError("unexpected matrix-retention hypothesis counts")
    return {"evidence": (directory / "reference.json").relative_to(REPO).as_posix(),
            "snapshot_manifest_sha256": digest(directory / "sha256.json"),
            "withdrawn_retention_hypothesis_manifest_sha256": digest(second / "sha256.json"),
            "corrected_simulator_source_sha256": digest(REPO / "viz/core/src/machine.rs"),
            "corrected_model_error": "Flags-only mask-register writes do not force invalid forwarding data",
            "open_manual_reference_difference": "Absent matrix-read output observed as zero, not a disabled-producer error",
            "unresolved_encoding_cases": "Five whole VSM cases rejected by type inference; encoded-fragment behavior observed separately, but whole-program legality/decoding correspondence remains unproven"}


def encoded_lbf_experiment() -> dict | None:
    reference = ROOT / "evidence/lbf-encoded/reference.json"
    if not reference.exists():
        return None
    record = json.loads(reference.read_text())
    vectors = reference.with_name("vectors.tsv")
    if digest(vectors) != record["vectors_sha256"] or len(vectors.read_text().splitlines()) != record["cases"]:
        raise ValueError("encoded LBF vectors changed")
    if record["matched"] != record["cases"] or len(record["records"]) != record["cases"]:
        raise ValueError("unresolved encoded LBF comparisons")
    for vector, row in zip(vectors.read_text().splitlines(), record["records"]):
        if vector.split("\t")[:3] != [row["unit"], row["scenario"], row["expected"]]:
            raise ValueError("encoded LBF record detached from vector")
        directory = reference.parent / row["directory"]
        for name, expected in row["artifacts"].items():
            if digest(directory / name) != expected:
                raise ValueError(f"encoded LBF artifact changed: {name}")
        template = (directory / "template.asm").read_text().splitlines()
        driver = (directory / "driver.asm").read_text().splitlines()
        positions = [i for i, line in enumerate(template) if line.startswith("j ")]
        if len(positions) < 2:
            raise ValueError("encoded template lacks producer/consumer")
        insert = positions[0] + 1
        if (directory / "encoded.asm").read_text() != "\n".join(template[:insert] + driver + template[insert:]) + "\n":
            raise ValueError("encoded stream is not an unchanged word splice")
        template_source = (directory / "template.vsm").read_text().splitlines()
        at = template_source.index("l1bmm $lb0 $nowrite") + 1
        driver_source = (directory / "driver.vsm").read_text().splitlines()
        if (directory / "intended.vsm").read_text() != "\n".join(template_source[:at] + driver_source + template_source[at:]) + "\n":
            raise ValueError("intended VSM does not match source fragments")
        def words(name):
            lines = (directory / name).read_text().splitlines()
            if any(line.startswith("m ") for line in lines):
                raise ValueError("unexpected MV instruction")
            result = [line for line in lines if line.startswith("j ")]
            if any(not re.fullmatch(r"j [01]{426}", line) for line in result):
                raise ValueError("unexpected PE word width")
            return result
        encoded, full = words("encoded.asm"), words("full.asm")
        if not full or encoded[:len(full)] != full or not row["full_prefix_words_identical"]:
            raise ValueError("whole assembler output prefix differs from fragments")
        if row["full_vsm_accepted"]:
            if row["full_assembler_returncode"] != 0 or full != encoded:
                raise ValueError("accepted whole VSM differs from encoded stream")
        elif row["full_assembler_returncode"] == 0 or "ValueTypeFromUOpNode" not in (directory / "full.stderr.txt").read_text():
            raise ValueError("unclassified whole VSM rejection")
        if not row["matched"] or not row["fragment_assembly_accepted"] or row["returncode"] != 0 or not row["values_match"]:
            raise ValueError("encoded observation not verified")
    for item in record["sources"]:
        source = REPO / item["path"]
        if not source.exists() and item["path"] in (
                "judge/judge-py/mncore2_emuenv/assemble3", "judge/judge-py/mncore2_emuenv/gpfn3_package_main"):
            continue
        if digest(source) != item["sha256"]:
            raise ValueError(f"stale encoded experiment: {item['path']}")
    for key in ("whole_vsm_legality_proven", "decoder_correspondence_proven", "proves_universal_conformance", "proves_isa_completeness", "proves_optimality"):
        if record[key]:
            raise ValueError("fragment execution cannot prove whole VSM legality or optimality")
    return {"path": reference.relative_to(REPO).as_posix(), "sha256": digest(reference),
            "cases": record["cases"], "matched_cases": record["matched"],
            "whole_vsm_rejections": sum(not row["full_vsm_accepted"] for row in record["records"]),
            "scope": record["scope"], "whole_vsm_legality_proven": False,
            "decoder_correspondence_proven": False, "formal_conformance_proof": False}


def isa_bounds_experiment() -> dict:
    directory = ROOT / "evidence/isa-bounds"
    script = ROOT / "scripts/check_isa_parser_bounds.py"
    reference = directory / "reference.json"
    record = json.loads(reference.read_text())
    for item in record["tool_hashes"]:
        path = REPO / item["path"]
        if item["path"] == "judge/judge-py/mncore2_emuenv/assemble3" and not path.exists():
            continue  # Official proprietary binaries are not distributed in CI.
        if digest(path) != item["sha256"]:
            raise ValueError(f"stale ISA boundary experiment: {item['path']}")
    if not all(row["matches_expected"] for row in record["observations"]):
        raise ValueError("ISA boundary experiment contains an unexpected assembler result")
    if len(record["observations"]) != 511:
        raise ValueError("ISA boundary experiment case count changed")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": script.relative_to(REPO).as_posix(),
        "generator_sha256": digest(script),
        "probes": len(record["observations"]),
        "accepted": sum(row["accepted"] for row in record["observations"]),
        "rejected": sum(not row["accepted"] for row in record["observations"]),
        "findings": record["findings"],
        "scope": record["scope"],
        "formal_isa_completeness_proof": False,
    }


def answer_parser_gap_audit() -> dict:
    reference = ROOT / "evidence/parser-gap-audit/answers.json"
    record = json.loads(reference.read_text())
    if record["answer_files"] != 73:
        raise ValueError("parser-gap audit must cover all 73 checked-in answers")
    if record["opcode_candidate_source"]["candidate_count"] != 184:
        raise ValueError("parser-gap audit must cover all 184 syntax candidates")
    if record["parse_errors"] or record["raw_operand_occurrences"] or record["other_opcode_occurrences"]:
        raise ValueError("checked-in answers contain parser errors or structural fallbacks")
    for item in [*record["input_hashes"], record["scanner"], record["opcode_candidate_source"]]:
        if digest(REPO / item["path"]) != item["sha256"]:
            raise ValueError(f"stale parser-gap audit input: {item['path']}")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": "proofs_lean/scripts/check_parser_gap_reference.py",
        "generator_sha256": digest(ROOT / "scripts/check_parser_gap_reference.py"),
        "answers": record["answer_files"],
        "syntax_candidates": len(record["opcode_candidate_results"]),
        "parsed_syntax_candidates": sum(
            row["result"]["parsed"] for row in record["opcode_candidate_results"]
        ),
        "unparsed_syntax_candidates": [
            row["spelling"] for row in record["opcode_candidate_results"]
            if not row["result"]["parsed"]
        ],
        "raw_operands_in_syntax_candidates": sum(
            len(expression["raw_operands"])
            for row in record["opcode_candidate_results"]
            for expression in row["result"].get("expressions", [])
        ),
        "unique_opcode_spellings": len(record["parsed_operator_spellings"]),
        "raw_operand_occurrences": len(record["raw_operand_occurrences"]),
        "other_opcode_occurrences": len(record["other_opcode_occurrences"]),
        "parse_errors": len(record["parse_errors"]),
        "scope": record["scope"],
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
    untyped_source = ROOT / "ProofsLean/UntypedALU.lean"
    memory_source = ROOT / "ProofsLean/PEMemory.lean"
    masked_memory_source = ROOT / "ProofsLean/MaskedPEMemory.lean"
    address_properties = ROOT / "ProofsLean/AddressProperties.lean"
    mask_source = ROOT / "ProofsLean/Masks.lean"
    forwarding_source = ROOT / "ProofsLean/Forwarding.lean"
    encoded_forwarding = ROOT / "ProofsLean/EncodedForwarding.lean"
    issue_source = ROOT / "ProofsLean/Issue.lean"
    parsed_integer_source = ROOT / "ProofsLean/ParsedIntegerStep.lean"
    return {
        "schema_version": 1,
        "isa_exhaustiveness_proven": False,
        "full_semantics_implemented": False,
        "compiler_syntax_source": "mncompile/machine.py",
        "compiler_syntax_sha256": digest(path),
        "inventory_scope": "Compiler-generated ALU/MAU spelling candidates plus separately scoped source-derived records; not an authoritative complete ISA or legality model.",
        "selected_parser_boundary_experiment": isa_bounds_experiment(),
        "answer_parser_gap_audit": answer_parser_gap_audit(),
        "finite_carrier_proofs": [{
            "source": "proofs_lean/ProofsLean/FiniteRegion.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteRegion.lean"),
            "theorem": "ProofsLean.MNCore.Issue.Region.inFiniteEnvelope_finite",
            "scope": "Finite subtype for the PE region envelope documented by assemble3 boundary probes: width < 5, four addresses < 4096, and madpe < 4.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: region_address_cycle0_max through region_address_cycle3_overflow, madpe_3/madpe_4, and LM0/LM1/GRF capacity findings.",
            "missing": "A universal assembler soundness theorem from parsed legal operands to this envelope, bank-specific alignment, all other operand fields, bounded line lists, and machine-level coverage.",
        }],
        "datapath_fragments": [{
            "source": fragment_source.relative_to(REPO).as_posix(), "sha256": digest(fragment_source),
            "implemented": "16/32/64-bit inc/dec/add/sub/not/lnot/and/or/xor/integer max/min/passa/lsl/lsr/bsl/bsr/packbit; lane packing, replicated flags and LSB bypass",
            "scope": "Already-read and already-reduced buses only; not VSM instruction execution or legality",
            "missing": "Operand decoding/access/reduction, masks, timing/forwarding, parallel issue, all other ISA operations",
            "reference_experiment": datapath_experiment("integer-alu", 0),
        }, {
            "source": untyped_source.relative_to(REPO).as_posix(), "sha256": digest(untyped_source),
            "implemented": "zero and 32-bit imm/immu; explicit manualReading/referenceBinary profiles for msl/msr",
            "scope": "Already-read buses of four PEs in one MAB; unqualified rotation semantics remain unknown",
            "missing": "Operand access, masks, timing, parallel issue, resolution of rotation LSB discrepancy",
            "reference_experiment": datapath_experiment("untyped-alu", 1),
        }, {
            "source": memory_source.relative_to(REPO).as_posix(), "sha256": digest(memory_source),
            "properties_source": address_properties.relative_to(REPO).as_posix(), "properties_sha256": digest(address_properties),
            "implemented": "LM0/LM1/GRF0/GRF1/T capacities, address schedules, BAR/T/madpe offset arithmetic, alignment/wrap, raw reads and unmasked writes",
            "scope": "Combinational memory primitives; writes are instantaneous and cannot establish instruction scheduling correctness",
            "missing": "Complete operand decoding/legality, masks, precision conversion, read/write timing, forwarding, parallel-port checks and universal reference conformance",
            "reference_experiment": datapath_experiment("pe-memory", 1),
            "additional_reference_experiments": [datapath_experiment("dynamic-address", 1)],
        }, {
            "source": masked_memory_source.relative_to(REPO).as_posix(),
            "sha256": digest(masked_memory_source),
            "implemented": "Per-word PE-memory mask application for ll and half-word modes; all-ones equivalence and masked write readback proofs",
            "scope": "Immediate memory primitive with caller-supplied flags and selector width; not connected to a complete instruction step",
            "missing": "Directive resolution for memory targets, mask-state timing, hazards, parallel ports and universal reference conformance",
            "source_basis": [{
                "source": "viz/core/src/machine.rs",
                "sha256": digest(REPO / "viz/core/src/machine.rs"),
            }],
        }, {
            "source": mask_source.relative_to(REPO).as_posix(), "sha256": digest(mask_source),
            "implemented": "Fixed/variable mask entries, per-half/word write merging, zero flush, flag preservation, mask-register AND writes, single-line cancellation of multiline selection",
            "scope": "Pure mask and register primitives; full-width GRF reference experiments only; no full instruction model",
            "missing": "All masked destinations and width combinations, complete syntax/legality, poisoned values, timing and parallel-issue integration",
            "reference_experiment": datapath_experiment("masks", 1),
        }, {
            "source": forwarding_source.relative_to(REPO).as_posix(), "sha256": digest(forwarding_source),
            "implemented": "Four forwarding slots per cycle, nop/noforward preservation, absent producer poison, deferred consumption, unknown distinct from known invalid values",
            "scope": "Known whole-step producer summaries and whole-value poison only; not a VSM interpreter or complete numeric-error model",
            "missing": "All initial state/encoding rules, exact memory timing, per-lane numerical poison and full instruction integration",
            "reference_experiment": datapath_experiment("forwarding", 0, allow_unknown=True),
        }, {
            "source": encoded_forwarding.relative_to(REPO).as_posix(), "sha256": digest(encoded_forwarding),
            "implemented": "Explicit encoded-stream LBF retention/replacement profile; nop/noforward preservation",
            "scope": "Assembler-generated 426-bit fragments only; does not change unknown VSM cases",
            "missing": "Formal decoding/encoding correspondence and whole VSM legality",
            "reference_experiment": encoded_lbf_experiment(),
        }, {
            "source": issue_source.relative_to(REPO).as_posix(), "sha256": digest(issue_source),
            "implemented": "Full structural PE Op/Operand payload mirror, issue projection, abstract PE-line rules, and a partial parsed-op to integer-ALU bridge for supported L/I/S integer operations and packbit",
            "scope": "The Rust enum inventory is checked against Lean constructors. A separate partial executor covers supported integer ALU/zero/immediate expressions with direct PE-memory destinations, masks/flush and ordered multiple destinations; this is not full ISA semantics",
            "source_basis": [{
                "source": "viz/core/src/vsm.rs", "sha256": digest(REPO / "viz/core/src/vsm.rs"),
            }, {
                "source": "viz/core/src/issue.rs", "sha256": digest(REPO / "viz/core/src/issue.rs"),
            }, {
                "source": parsed_integer_source.relative_to(REPO).as_posix(),
                "sha256": digest(parsed_integer_source),
            }],
            "missing": "VSM parser correspondence, non-PE and matrix destinations, floating/MAU/L1/L2/MV execution, all assembler legality checks outside issue.rs, hardware correspondence and integration with the total instruction transition",
            "reference_experiment": None,
        }],
        "unresolved_semantic_discrepancies": [rotation_discrepancy()],
        "corrected_model_errors": [mask_model_correction()],
        "forwarding_findings": forwarding_findings(),
        "syntax_candidates": [{"spelling": name, "formal_step_semantics": "unimplemented"} for name in spellings],
        "obligations": [{"area": area, "status": "partial_datapath_only" if area in (
            "integer_16_32_64_and_signedness", "parallel_issue_and_memory_port_legality", "wide_access_and_lsb_passthrough",
            "immediates_fixed_operands_and_zero", "pe_rotations_and_coordinate_operands",
            "t_indirect_madpe_and_address_mapping", "masks_flush_and_mask_directives",
            "forwarding_lifetime_and_latency") else "unimplemented"} for area in areas],
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
