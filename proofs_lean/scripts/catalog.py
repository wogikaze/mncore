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
    if len(record["observations"]) != 3410:
        raise ValueError("ISA boundary experiment case count changed")
    observations = {row["case"]: row for row in record["observations"]}
    for entry in range(256):
        row = observations.get(f"omr_{entry}")
        expected = 1 <= entry <= 15
        if row is None or row["accepted"] != expected or not row["matches_expected"]:
            raise ValueError(f"exhaustive OMR selector evidence is incomplete at {entry}")
        row = observations.get(f"imr_selector_{entry}")
        expected = entry < 32
        if row is None or row["accepted"] != expected or not row["matches_expected"]:
            raise ValueError(f"exhaustive IMR selector evidence is incomplete at {entry}")
        for width in ("n", "l", "ll"):
            row = observations.get(f"mask_directive_{width}_{entry}")
            if row is None or row["accepted"] != expected or not row["matches_expected"]:
                raise ValueError(
                    f"exhaustive mask directive selector evidence is incomplete: {width}/{entry}"
                )
        expected_argument = 6 <= entry <= 9
        for opcode in ("hbfe", "hbfn"):
            row = observations.get(f"{opcode}_{entry}")
            if (row is None or row["accepted"] != expected_argument
                    or not row["matches_expected"]):
                raise ValueError(
                    f"exhaustive {opcode} argument evidence is incomplete at {entry}"
                )
    for row in record["observations"]:
        encoded = row.get("encoded_words", [])
        auxiliary = row.get("auxiliary_output_kinds", [])
        if len(encoded) + len(auxiliary) != (row["assembler_output_lines"] or 0):
            raise ValueError(f"missing encoded-word shape: {row['case']}")
        if any(kind not in {"d", "r"} for kind in auxiliary):
            raise ValueError(f"unexpected auxiliary assembler output: {row['case']}")
        for word in encoded:
            if (not word["binary"] or
                    word["bit_width"] != {"j": 426, "m": 82}.get(word["kind"])):
                raise ValueError(f"unexpected assembler word encoding: {row['case']}")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": script.relative_to(REPO).as_posix(),
        "generator_sha256": digest(script),
        "probes": len(record["observations"]),
        "accepted": sum(row["accepted"] for row in record["observations"]),
        "rejected": sum(not row["accepted"] for row in record["observations"]),
        "observed_encoded_word_kinds": sorted({
            (word["kind"], word["bit_width"])
            for row in record["observations"] for word in row.get("encoded_words", [])
        }),
        "findings": record["findings"],
        "scope": record["scope"],
        "formal_isa_completeness_proof": False,
    }


def opcode_arity_experiment() -> dict:
    reference = ROOT / "evidence/opcode-arity/reference.json"
    script = ROOT / "scripts/check_opcode_arity_reference.py"
    record = json.loads(reference.read_text())
    for item in record["tool_hashes"]:
        path = REPO / item["path"]
        if item["path"] == "judge/judge-py/mncore2_emuenv/assemble3" and not path.exists():
            continue
        if digest(path) != item["sha256"]:
            raise ValueError(f"stale opcode arity experiment: {item['path']}")
    if record["candidate_count"] != 184 or len(record["observations"]) != 184:
        raise ValueError("opcode arity experiment must cover all 184 compiler candidates")
    if record["accepted_maximal_candidates"] != 184 or record["rejected_duplicate_overflows"] != 184:
        raise ValueError("opcode arity experiment contains unexpected assembler results")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": script.relative_to(REPO).as_posix(),
        "generator_sha256": digest(script),
        "candidates": record["candidate_count"],
        "accepted_maximal_templates": record["accepted_maximal_candidates"],
        "rejected_duplicate_overflows": record["rejected_duplicate_overflows"],
        "scope": record["scope"],
        "full_isa_completeness_proof": False,
        "limitations": record["limitations"],
    }


def answer_parser_gap_audit() -> dict:
    reference = ROOT / "evidence/parser-gap-audit/answers.json"
    record = json.loads(reference.read_text())
    if record["answer_files"] != 73:
        raise ValueError("parser-gap audit must cover all 73 checked-in answers")
    if record["opcode_candidate_source"]["candidate_count"] != 184:
        raise ValueError("parser-gap audit must cover all 184 syntax candidates")
    if any(
        not expression.get("source_count", 0) <= 3
        for row in record["opcode_candidate_results"]
        for expression in row["result"].get("expressions", [])
    ):
        raise ValueError("a parser candidate exceeds the three-source envelope")
    answer_shapes = record.get("answer_expression_shapes", [])
    if not answer_shapes or any(row["source_count"] > 3 for row in answer_shapes):
        raise ValueError("a parsed answer expression exceeds the Lean three-source envelope")
    if any(not row["destinations_nodup"] for row in answer_shapes):
        raise ValueError("a checked-in answer expression has repeated parsed destinations")
    if record["parse_errors"] or record["raw_operand_occurrences"] or record["other_opcode_occurrences"]:
        raise ValueError("checked-in answers contain parser errors or structural fallbacks")
    raw_fallbacks = record.get("raw_operand_fallback_probes", [])
    if len(raw_fallbacks) != 5:
        raise ValueError("Rust Raw operand fallback probes are missing")
    candidate_raw_probes = record.get("opcode_candidate_raw_operand_probes", [])
    expected_candidate_raw_slots = sum(
        expression["source_count"] + expression["destination_count"]
        for row in record["opcode_candidate_results"]
        for expression in row["result"].get("expressions", [])
    )
    if len(candidate_raw_probes) != expected_candidate_raw_slots:
        raise ValueError("compiler-candidate Raw operand slot audit is incomplete")
    if any(
        not probe["result"].get("parsed")
        or len(probe["result"].get("raw_operands", [])) != 1
        or probe["result"]["raw_operands"][0].get("operand") != "$qraw"
        for probe in candidate_raw_probes
    ):
        raise ValueError("compiler-candidate operand slot did not produce exactly one Raw")
    assembler_reference = json.loads(
        (ROOT / "evidence/isa-bounds/reference.json").read_text()
    )
    assembler_raw = {
        row["case"].removeprefix("raw_operand_"): row
        for row in assembler_reference["observations"]
        if row["case"].startswith("raw_operand_")
    }


    for probe in raw_fallbacks:
        assembler_case = {
            "alu_source": "alu_source",
            "alu_destination": "alu_destination",
            "zero_destination": "zero_destination",
            "matrix_read_source": "matrix_source",
            "l1bm_source": "l1bm_source",
        }[probe["case"]]
        observation = assembler_raw.get(assembler_case)
        if (observation is None or observation["source"] != probe["source"] or
                observation["accepted"] or observation["assembler_output_lines"] is not None):
            raise ValueError(f"Rust/assembler Raw fallback evidence mismatch: {probe['case']}")
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
        "raw_operand_fallback_probes": len(raw_fallbacks),
        "syntax_candidate_raw_operand_slot_probes": len(candidate_raw_probes),
        "syntax_candidate_raw_operand_slots_parsed": True,
        "syntax_candidate_raw_operand_assembler_acceptance_tested": True,
        "unique_opcode_spellings": len(record["parsed_operator_spellings"]),
        "parser_source_destination_arity": dict(sorted(Counter(
            f"{expression['class']}:src{expression['source_count']}:dst{expression['destination_count']}"
            for row in record["opcode_candidate_results"]
            for expression in row["result"].get("expressions", [])
        ).items())),
        "answer_expression_count": sum(row["occurrences"] for row in answer_shapes),
        "answer_max_source_count": max(row["source_count"] for row in answer_shapes),
        "answer_destination_lists_nodup": True,
        "answer_parser_source_arity": dict(sorted(Counter(
            f"{row['class']}:src{row['source_count']}"
            for row in answer_shapes
            for _ in range(row["occurrences"])
        ).items())),
        "raw_operand_occurrences": len(record["raw_operand_occurrences"]),
        "other_opcode_occurrences": len(record["other_opcode_occurrences"]),
        "parse_errors": len(record["parse_errors"]),
        "scope": record["scope"],
    }

def parallel_issue_boundary_experiment() -> dict:
    reference = ROOT / "evidence/isa-bounds/reference.json"
    record = json.loads(reference.read_text())
    observations = {row["case"]: row for row in record["observations"]}
    expected = {
        "mask_application_same_width": (True, 1),
        "mask_application_conflicting_width": (False, None),
        "mask_application_conflicting_entry": (False, None),
        "mask_flush_conflicting_entry": (False, None),
        "omr_cross_group_same_entry": (False, None),
        "omr_cross_group_different_entries": (False, None),
        "l1bm_forward_source": (True, 1),
        "l1bm_turnaround_forward_source": (True, 2),
        "l1bm_duplicate_lbf_write": (False, None),
        "zero_duplicate_lm0_output": (False, None),
        "zero_duplicate_nowrite_outputs": (False, None),
        "zero_nowrite_with_other_output": (False, None),
        "bar_write_lm0": (True, 1),
        "bar_write_lm1": (True, 1),
        "bar_write_and_read_other_bank": (True, 1),
        "bar_write_and_read_same_bank": (False, None),
        "bar_write_and_data_write_same_bank": (False, None),
        "l2bmdars_parallel_l2bm_exception": (False, None),
    }
    companions = ("bcast", "bcast2", "distrib", "froml1b", "reduce",
                  "reduce2", "gather", "imcast")
    for selector in range(2):
        for opcode in companions:
            expected[f"l2bmdars_{opcode}_selector{selector}"] = (False, None)
    for case, (accepted, words) in expected.items():
        row = observations.get(case)
        if row is None or (row["accepted"], row["assembler_output_lines"]) != (accepted, words):
            raise ValueError(f"unexpected assemble3 mask-issue boundary: {case}")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "manual_sections": ["SDM 3.6.1.7", "SDM 3.6.1.9", "SDM 3.6.1.15", "SDM 3.6.1.17", "SDM 3.6.1.19", "SDM 3.6.2.1", "SDM 3.6.4", "SDM 3.6.7.10"],
        "observations": [
            {"case": case, "accepted": observations[case]["accepted"],
             "assembler_output_lines": observations[case]["assembler_output_lines"]}
            for case in expected
        ],
        "formal_rules": [
            "ProofsLean.MNCore.Issue.maskWidthsAgree",
            "ProofsLean.MNCore.Issue.maskEntriesAgree",
            "ProofsLean.MNCore.Issue.projected_mask_applications_are_parser_masks",
            "ProofsLean.MNCore.Issue.conflicting_mask_widths_rejected",
            "ProofsLean.MNCore.Issue.conflicting_mask_entries_rejected",
            "ProofsLean.MNCore.Issue.duplicate_mask_register_writes_rejected",
            "ProofsLean.MNCore.Issue.lbfWritesUnique",
            "ProofsLean.MNCore.Issue.projected_lbf_writes_match_transfer_sources",
            "ProofsLean.MNCore.Issue.duplicate_lbf_writes_rejected",
            "ProofsLean.MNCore.Issue.duplicate_memory_destination_bank_is_illegal",
            "ProofsLean.MNCore.Issue.base_address_write_conflicts_with_same_bank_read",
            "ProofsLean.MNCore.Issue.projected_bar_writes_are_bar_destinations",
            "ProofsLean.MNCore.Issue.nowrite_with_other_destination_is_illegal",
            "ProofsLean.MNCore.Issue.projected_nowrite_output_validity",
            "ProofsLean.MNCore.Issue.parsed_duplicate_nowrite_output_rejected",
        ],
        "limitations": "These probes cover mask agreement, OMR, LBF and BAR writes, duplicate PE-memory destinations, and `$nowrite` exclusivity; they do not establish complete parser, assembler, or hazard legality correspondence.",
    }


def answer_encoding_experiment() -> dict:
    reference = ROOT / "evidence/answer-encoding/reference.json"
    script = ROOT / "scripts/check_answer_encoding_reference.py"
    record = json.loads(reference.read_text())
    if record["answer_count"] != 73 or len(record["observations"]) != 73:
        raise ValueError("answer encoding evidence must cover all 73 answers")
    counts = Counter()
    for row in record["observations"]:
        source = REPO / row["source"]
        if digest(source) != row["source_sha256"]:
            raise ValueError(f"stale answer encoding source: {row['source']}")
        if len(row["words"]) != row["assembler_output_lines"]:
            raise ValueError(f"answer output line count mismatch: {row['source']}")
        for word in row["words"]:
            if (not word["binary"] or
                    word["bit_width"] != {"j": 426, "m": 82}.get(word["kind"])):
                raise ValueError(f"unexpected answer encoding shape: {row['source']}")
            counts[word["kind"]] += 1
    if counts != {"j": 984, "m": 57} or sum(counts.values()) != 1041:
        raise ValueError(f"unexpected answer encoding totals: {counts}")
    for item in record["tool_hashes"]:
        path = REPO / item["path"]
        if item["path"] == "judge/judge-py/mncore2_emuenv/assemble3" and not path.exists():
            continue
        if digest(path) != item["sha256"]:
            raise ValueError(f"stale answer encoding tool: {item['path']}")
    if record["proves_all_assembler_outputs_have_these_shapes"] or record["proves_isa_completeness"]:
        raise ValueError("answer corpus evidence cannot prove universal ISA completeness")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": script.relative_to(REPO).as_posix(),
        "generator_sha256": digest(script),
        "answers": record["answer_count"],
        "encoded_words": record["output_word_count"],
        "word_counts_by_kind": record["word_counts_by_kind"],
        "word_shapes": [["j", 426], ["m", 82]],
        "universal_encoding_claim": False,
        "formal_isa_completeness_proof": False,
    }


def encoded_word_universe() -> dict:
    finite_source = ROOT / "ProofsLean/FiniteIssue.lean"
    adapter_source = ROOT / "ProofsLean/ProgramLegality.lean"
    required_finite = (
        "AssemblerInstructionWord.finite",
        "encodedPrograms_lengthBounded_finite",
    )
    required_adapter = (
        "encodedUniverseMachine",
        "encodedUniverseAlphabet_coversBelow",
        "encodedUniverse_shortPrograms_complete",
        "encodedUniverse_legalLinesCostBelow_finite",
        "encodedUniverseMachine_not_complete",
    )
    if any(name not in finite_source.read_text() for name in required_finite):
        raise ValueError("finite assembler-word carrier theorem is missing")
    if any(name not in adapter_source.read_text() for name in required_adapter):
        raise ValueError("assembler-word enumeration adapter theorem is missing")
    return {
        "finite_source": finite_source.relative_to(REPO).as_posix(),
        "finite_source_sha256": digest(finite_source),
        "adapter_source": adapter_source.relative_to(REPO).as_posix(),
        "adapter_source_sha256": digest(adapter_source),
        "line_alphabet": "Sum (BitVec 426) (BitVec 82)",
        "bounded_programs_finite": "ProofsLean.MNCore.Issue.encodedPrograms_lengthBounded_finite",
        "short_program_enumeration_complete": "ProofsLean.MNCore.Issue.encodedUniverse_shortPrograms_complete",
        "legal_lines_finite": "ProofsLean.MNCore.Issue.encodedUniverse_legalLinesCostBelow_finite",
        "machine_complete": False,
        "universal_source_to_encoding_correspondence": False,
        "scope": "All bit patterns in the observed PE/MV word widths; an over-approximation of accepted source output pending universal assembler correspondence.",
    }


def raw_candidate_assembler_experiment() -> dict:
    reference = ROOT / "evidence/raw-candidate-assembler/reference.json"
    record = json.loads(reference.read_text())
    parser_audit = ROOT / "evidence/parser-gap-audit/answers.json"
    parser_record = json.loads(parser_audit.read_text())
    expected = {
        (probe["spelling"], probe["operand_token_index"])
        for probe in parser_record["opcode_candidate_raw_operand_probes"]
    }
    observed = {
        (row["spelling"], row["operand_token_index"])
        for row in record["observations"]
    }
    if len(expected) != 1470 or len(observed) != len(record["observations"]) or observed != expected:
        raise ValueError("Raw-candidate assembler experiment does not cover parser probe slots")
    for item in record["tool_hashes"]:
        if digest(REPO / item["path"]) != item["sha256"]:
            raise ValueError(f"stale Raw-candidate assembler input: {item['path']}")
    if record["accepted_count"] + record["rejected_count"] != len(expected):
        raise ValueError("Raw-candidate assembler outcome counts are inconsistent")
    if (
        record["accepted_count"] != sum(row["accepted"] for row in record["observations"])
        or record["rejected_count"] != sum(not row["accepted"] for row in record["observations"])
        or record["probe_count"] != len(expected)
    ):
        raise ValueError("Raw-candidate assembler outcome totals do not match observations")
    return {
        "source": reference.relative_to(REPO).as_posix(),
        "sha256": digest(reference),
        "generator": "proofs_lean/scripts/check_raw_candidate_assembler_reference.py",
        "generator_sha256": digest(ROOT / "scripts/check_raw_candidate_assembler_reference.py"),
        "probes": len(expected),
        "accepted": record["accepted_count"],
        "rejected": record["rejected_count"],
        "scope": record["scope"],
        "limitations": record["limitations"],
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
        "checked_answer_encoding_experiment": answer_encoding_experiment(),
        "encoded_word_universe": encoded_word_universe(),
        "opcode_destination_arity_experiment": opcode_arity_experiment(),
        "answer_parser_gap_audit": answer_parser_gap_audit(),
        "raw_candidate_assembler_experiment": raw_candidate_assembler_experiment(),
        "parallel_issue_boundary_experiment": parallel_issue_boundary_experiment(),
        "fintype_bounded_enumeration": {
            "source": "proofs_lean/ProofsLean/Enumeration.lean",
            "sha256": digest(ROOT / "ProofsLean/Enumeration.lean"),
            "finite_candidate_set": "programsUpToFinset",
            "bound_specific_certificate": "ProofsLean.finiteAlphabetCertificate",
            "fintype_specialization": "programsUpToFintype",
            "certificate": "ProofsLean.fintypeCertificate",
            "proved": [
                "ProofsLean.programsUpToFinset_complete",
                "ProofsLean.programsUpToFintype_complete",
                "ProofsLean.shortProgramsFinset_complete",
                "ProofsLean.finiteAlphabetCertificate",
                "ProofsLean.shortProgramsFintype_complete",
            ],
            "limitation": "A cost-bounded finite-subtype alphabet is available, but the universal MN-Core proof that legal rows lie in the operand envelope and the machine connection remain open.",
        },
        "partial_machine_bounded_legal_lines": {
            "source": "proofs_lean/ProofsLean/ProgramLegality.lean",
            "sha256": digest(ROOT / "ProofsLean/ProgramLegality.lean"),
            "line_type": "ProofsLean.MNCore.Issue.InstructionLine",
            "fintype": "ProofsLean.MNCore.partialMachine_legalLineFintype",
            "alphabet_coverage": "ProofsLean.MNCore.partialMachine_legalLineAlphabet_covers",
            "enumeration_complete": "ProofsLean.MNCore.partialMachine_exactAlphabet_shortPrograms_complete",
            "scope": "For each score bound, the exact set of lines occurring in programs legal under the current local issue, payload-envelope, and PE/block hazard predicate is finite and can serve as a complete short-program alphabet.",
            "limitation": "The partial machine step returns unknown, and source parser/assembler completeness into this legality predicate remains unproved; this does not define MNCore.machine or establish ISA-wide completeness.",
        },
        "finite_carrier_proofs": [{
            "source": "proofs_lean/ProofsLean/FiniteRegion.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteRegion.lean"),
            "theorem": "ProofsLean.MNCore.Issue.Region.inFiniteEnvelope_finite",
            "scope": "Finite subtype for the PE region envelope documented by assemble3 boundary probes: width in {1, 2, 4}, four addresses < 4096, and madpe < 4.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: region_address_cycle0_max through region_address_cycle3_overflow, madpe_3/madpe_4, and LM0/LM1/GRF capacity findings.",
            "missing": "A universal assembler soundness theorem from parsed legal operands to this envelope, bank-specific alignment, all other operand fields, bounded line lists, and machine-level coverage.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.listLengthLE_finite",
            "scope": "For any finite element type and any fixed bound, the subtype of lists with length at most that bound is finite.",
            "evidence": "Lean encodes each bounded list as either nil or a head paired with a shorter bounded tail; no external parser evidence is needed for this generic theorem.",
            "missing": "Per-opcode source/destination arity bounds and their parser correspondence are still needed before applying this lemma to all PE expressions.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.InstructionLine.inFiniteEnvelope_finite",
            "scope": "Finite carrier for PE rows of at most ten normalized expressions, nop rows with count below the given bound and bounded wait tags, and normalized MV transfers whose size is below 32768.",
            "evidence": "Composes the proved finite carriers for normalized expressions, bounded expression lists, optional wait tags, and MV sizes. The assemble3 boundary probes accept size 32704 and reject 32768 for every documented MV grammar; they do not establish exact interior-size legality.",
            "missing": "No proof yet shows that every legal fixed-cost line satisfies these expression payload envelopes, that the nop bound follows from cost, or that all legal line forms embed in this subtype. The MV size envelope is an observed upper bound, not exact legality for each size below 32768.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteInstructionLines.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteInstructionLines.lean"),
            "theorem": "ProofsLean.MNCore.Issue.InstructionLine.costBelowEnvelope_finite",
            "scope": "Finite subtype of normalized instruction lines whose cost is below a fixed bound and whose payloads satisfy the proved finite envelopes.",
            "evidence": "Subtype of InstructionLine.inFiniteEnvelope_finite; cost is additionally restricted below the same bound.",
            "missing": "The parser/assembler and hazard model must prove that every legal line below the cost bound satisfies the payload envelope.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteInstructionLines.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteInstructionLines.lean"),
            "theorem": "ProofsLean.MNCore.Issue.InstructionLine.legalCostBelowEnvelope_finite",
            "scope": "Finite subtype of legal normalized instruction lines below a fixed cost bound, conditional on a linewise envelope inclusion premise.",
            "evidence": "Applies the finite bounded carrier through an injective embedding using the supplied legal-line envelope premise.",
            "missing": "The supplied premise is not yet proved for an MNCore machine; opcode/parser completeness, operand range soundness, simultaneous issue, and hazards remain open.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteInstructionLines.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteInstructionLines.lean"),
            "theorem": "ProofsLean.MNCore.Issue.InstructionLine.legalCostBelowFinset",
            "scope": "Finset alphabet for exactly the legal normalized instruction lines below a cost bound, under the stated finite-envelope inclusion premise.",
            "evidence": "Builds the subtype Fintype and embeds its values through ProofsLean.finiteSubtypeAlphabet; membership is characterized by legality and cost below the bound.",
            "missing": "The linewise envelope premise and correspondence to complete MN-Core parsed source remain unproved.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.Access.inFiniteEnvelope_finite",
            "scope": "Finite carrier for accesses whose region lies in the parser-supported PE region envelope, with the tighter <512 address bound applied to GRF0/GRF1; the bank is one of ten constructors.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json records LM0/LM1 capacities of 4096 and GRF0/GRF1 capacities of 512; Bank constructors are mirrored from the issue checker.",
            "missing": "Bank-specific address legality, parser correspondence, and bounded operand/line carriers.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedOperand.inFiniteEnvelope_finite",
            "parser_source": "proofs_lean/ProofsLean/PEParser.lean",
            "parser_source_sha256": digest(ROOT / "ProofsLean/PEParser.lean"),
            "parser_fragment": "parseParsedPEOperand?",
            "scope": "Finite carrier for structured PE operands under numeric envelopes. Parsed mask selector and OMR indices store their parser u8 values in Fin 256; legality envelopes narrow them to mask values below 32 and OMR values 1..15. A separate Lean parser fragment handles forwarding/fixed, OMR, BAR, matrix, L1BM, L2BM, DAR, nowrite, and ordinary memory operands.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: OMR and BAR width boundaries, exhaustive mask selectors 0..255 with exactly 0..31 accepted, matrix rows, L1BM and L2BM addresses/selectors, DAR addresses, memory widths 1/2/4, and PE region bounds. `PEParser.lean` checks `$imr255` and `$omr255` are retained while `$imr256` and `$omr256` are rejected.",
            "missing": "No theorem establishes that Rust/assembler accepted operands all parse inside this envelope; bank/opcode-specific alignment and width legality, finite PE lines, and complete machine-level legality remain open.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedExpr.destinationsInFiniteEnvelope_finite",
            "scope": "Finite carrier for Nodup destination lists whose operands lie in the finite PE operand envelope; the length bound follows from the finite operand carrier cardinality.",
            "evidence": "General finite-type argument plus selected assemble3 probes rejecting repeated output categories, including distinct LM0 addresses, OMR entries, and nowrite outputs.",
            "missing": "No proof yet that every assembler-accepted opcode/parser destination list is Nodup and lies in the operand envelope; the probes cover representative forms only.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL1bSet.inFiniteEnvelope_finite",
            "parser_source": "proofs_lean/ProofsLean/Issue.lean",
            "parser_source_sha256": digest(ROOT / "ProofsLean/Issue.lean"),
            "parser_fragment": "parseParsedL1bSet?, parseParsedL2Opcode?",
            "parser_range_theorem": "ProofsLean.MNCore.Issue.parsedL1bAddressModeSet_inFiniteEnvelope",
            "scope": "L1B membership masks are represented directly by Fin 256 and immode selectors by Fin 8; Lean parses canonical decimal address[/immode] and bracketed list selectors and covers every `parse_l2_opcode` branch of ParsedL2Op.",
            "evidence": "`Issue.lean`: both selector parsers and envelope theorems; L2 opcode fixtures cover broadcast list/default, direction-dependent distribution/gather, from-L1B u8 range, RRN reductions/reduce2, dars/darw, and malformed RRN rejection. Typed-operand wrappers derive direction from the first operand. Selector fixtures cover all-eight, singleton, whitespace, empty-list rejection, and out-of-range rejection. assemble3 accepts the all-eight selector `@0/7`, all 64 address/immode pairs in 0..7, and rejects address 8 and immode 8.",
            "missing": "Full PE expression parsing and parser correspondence for all L1/L2 expression forms; parser-to-assembler acceptance correspondence is not established.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope_finite",
            "parser_source": "proofs_lean/ProofsLean/Issue.lean",
            "parser_source_sha256": digest(ROOT / "ProofsLean/Issue.lean"),
            "parser_fragment": "parsedMabdiff?, parseParsedL1Opcode?",
            "parser_range_theorem": "ProofsLean.MNCore.Issue.parsedMabdiff?_boundaries",
            "scope": "Finite subtype for signed L1BM MAB differences in [-255, 255].",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: explicit signed offsets -255..255 accepted and -256/+256 rejected in both PE-to-L1BM gather and L1BM-to-PE distribution operand directions. The SDM documents useful values 0..15.",
            "missing": "The standalone `ParsedL1Op` type still admits arbitrary Int values, and the bounded parser construction is not yet composed through complete PE expression parsing or proved complete for all assembler-accepted source lines.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedRrn.inFiniteEnvelope_finite",
            "scope": "Finite carrier for the eight reduction operation codes and RRN precision characters below Unicode scalar 128; `ParsedRrn.precision` carries this bound in its type.",
            "evidence": "`ParsedRrn.precision` is a subtype with the `<128` proof. `parseParsedMvRrn?` constructs that subtype only after checking the bound and recognizes the documented precision/opcode combinations; finiteCode maps it to `Fin 128 × Fin 8`.",
            "missing": "Assembler acceptance correspondence for the complete L1/L2 RRN spelling inventory and source-line parser coverage remains unproved.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL1Mabdiff.inFiniteEnvelope_finite",
            "scope": "Finite tagged carrier for the `distrib` and `gather` MAB-offset variants in the observed signed envelope.",
            "evidence": "Shares the exhaustive signed-offset assemble3 probes recorded in `isa-bounds/reference.json`.",
            "missing": "This projection covers only the two MAB-offset variants; no theorem yet connects every L1 parser output to the finite offset envelope.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL1Selector.inFiniteEnvelope_finite",
            "scope": "Finite tagged carrier for assembler-accepted L1BM `mwrite` and `m4write` selectors below 16; parser values are separately represented by Fin 256.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: exhaustive acceptance of l1bmm@0..15 and l1bmm4@0..15, with @16 rejected for both.",
            "missing": "The L1 opcode parser retains Rust's u8 selector range, which is wider than this assembler-valid 0..15 envelope; parser output is not proved to lie in this narrower subset.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL1Op.inFiniteEnvelope_finite",
            "parser_source": "proofs_lean/ProofsLean/Issue.lean",
            "parser_source_sha256": digest(ROOT / "ProofsLean/Issue.lean"),
            "parser_fragment": "parseParsedL1Opcode?",
            "scope": "Finite tagged carrier for all nine ParsedL1Op variants under the observed mab selector, RRN precision and MAB difference envelopes; parsed mwrite/m4write selectors use Fin 256.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: l1bmm/l1bmm4 selectors 0..15, signed mabdiff -255..255 in both gather/distribution operand directions, plus ParsedRrn's explicit ASCII precision envelope and finite opcode set. `Issue.lean` fixtures cover all nine Rust L1 opcode branches, direction-dependent d derived from the first typed operand, u8 selector parsing, signed offsets, RRN parsing, and round suffixes.",
            "missing": "No theorem yet proves every output of `parseParsedL1Opcode?` lies in the finite envelope (the Rust parser's u8 selector range is wider than the assembler's 0..15 range), and no finite PE-line or machine-level carrier is composed from it.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL2Op.inFiniteEnvelope_finite",
            "scope": "Finite tagged carrier for all ten ParsedL2Op variants under bounded L1B set, from-L1B selector, and RRN envelopes; parsed from-L1B selector uses Fin 256.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: all 64 L1B set pairs, l2bm@0..7 accepted/@8 rejected, and finite RRN opcode/precision carrier.",
            "missing": "The envelope is not yet proved to contain every assembler-accepted ParsedL2Op parse, and no finite PE-line or machine-level carrier is composed from it.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedL2FromL1.inFiniteEnvelope_finite",
            "scope": "Finite tagged carrier for assembler-accepted `ParsedL2Op.fromL1b` selectors below 8; parsed values use Fin 256.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: l2bm@0..7 accepted and @8 rejected.",
            "missing": "Only the from-L1B selector payload is bounded; complete ParsedL2Op finiteness and parser-to-envelope soundness remain unproved.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.waitTagInFiniteEnvelope_finite",
            "parser_source": "proofs_lean/ProofsLean/Issue.lean",
            "parser_source_sha256": digest(ROOT / "ProofsLean/Issue.lean"),
            "parser_fragment": "parseParsedWaitTag?, parseParsedNopLine?",
            "parser_range_theorem": "ProofsLean.MNCore.Issue.parseParsedWaitTag_value_bounded",
            "parser_legality_theorem": "ProofsLean.MNCore.Issue.parseParsedNopLine_checked_wait_positive",
            "scope": "Finite carrier for positive wait tags below 256.",
            "evidence": "`Issue.lean` parses i01, iFF, and syntactic i00 into Fin 256 and rejects i100; proofs_lean/evidence/isa-bounds/reference.json records assemble3 rejection of i00/i100, acceptance of i01/iFF, and exhaustive acceptance probes for 1..255.",
            "missing": "Canonical nop plus optional wait syntax is parsed, but full Rust parse_line syntax and assembler correspondence are not proved. The checker enforces the observed nonzero rule on this AST.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.optionWaitTagInFiniteEnvelope_finite",
            "scope": "Finite optional wait tags whose present value lies in 1..255.",
            "evidence": "Same assemble3 wait-tag boundaries as waitTagInFiniteEnvelope_finite.",
            "missing": "ParsedLine and InstructionLine nop wait tags store Option (Fin 256); the canonical nop parser composes with the checker, while full parser-to-assembler correspondence remains open.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.parsedBfArgInFiniteEnvelope_finite",
            "scope": "Finite optional mantissa-length arguments in the hbfe/hbfn range 6..9.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: exhaustive u8 argument probes for hbfe/hbfn; exactly 6..9 are accepted.",
            "missing": "Connection from parsed hbfe/hbfn expressions to this range and finite composition for all ParsedOp/PE-line fields.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.projectLine_expression_count_le_ten",
            "scope": "Legal projected PE rows have at most ten expressions, from ten unique issue groups and projection-assigned distinct IDs.",
            "evidence": "Formal consequence of Issue.groupsUnique and ParsedExpr.issueGroup being total; issue groups are mirrored from viz/core/src/issue.rs.",
            "missing": "Per-op source/destination arity constraints, finite numeric payloads, parser/assembler completeness, and finite PE line alphabet.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedMask.inFiniteEnvelope_finite",
            "scope": "Finite subtype for ParsedMask patterns and entry selectors below 32.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: exhaustive u8 IMR selector probes 0..255; exactly 0..31 are accepted. These are mask selectors, not OMR entries.",
            "missing": "Proof that all assembler-accepted PE masks parse into this subtype, plus other operand fields and whole-line finiteness.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedMaskDirective.inFiniteEnvelope_finite",
            "scope": "Finite carrier for control-state mask directives with width 2 or 4 and selector below 32; parsed selectors are Fin 256 after Rust-compatible u8 casting.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: exhaustive u8 selectors 0..255 for maskn, maskln, and masklln; each accepts exactly 0..31. Width alternatives follow these directive spellings.",
            "missing": "Prove that every assembler-accepted parsed directive has selector below 32, plus whole-machine finite composition.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.ParsedLine.updateMaskState_inFiniteEnvelope",
            "scope": "Mask control-state updates preserve the finite directive envelope; non-directive lines preserve the previous bounded state.",
            "evidence": "Lean case analysis over ParsedLine.updateMaskState and the directive envelope; accepted width and selector bounds are recorded in isa-bounds/reference.json.",
            "missing": "Prove every assembler-accepted directive is represented by the bounded ParsedLine case and compose the state transition into MNCore.machine.",
        }, {
            "source": "proofs_lean/ProofsLean/ParsedIntegerStep.lean",
            "sha256": digest(ROOT / "ProofsLean/ParsedIntegerStep.lean"),
            "theorem": "ProofsLean.MNCore.PEMemory.parseMaskDirectiveOperator_width_inFiniteEnvelope",
            "scope": "The mask operator parser produces only width 2 or 4.",
            "evidence": "Direct case analysis of the operator parser: `ll` selects 4; `l` and the default form select 2.",
            "missing": "Connect complete ParsedLine mask parsing, assembler-accepted selector range, and state normalization into the machine transition model.",
        }, {
            "source": "proofs_lean/ProofsLean/ParsedIntegerStep.lean",
            "sha256": digest(ROOT / "ProofsLean/ParsedIntegerStep.lean"),
            "theorem": "ProofsLean.MNCore.PEMemory.parseMaskDirective_inFiniteEnvelope",
            "scope": "Every parsed mask directive with assembler-legal selector 0..31 satisfies the finite ParsedLine envelope; parsed selector values are stored in Fin 256 after `% 256`.",
            "evidence": "Lean connects parseMaskDirective? output to the operator-width theorem; the 0..31 selector condition comes from the official assemble3 boundary probes.",
            "missing": "The selector-range premise is not proved for arbitrary parser outputs (Fin 256 permits values through 255); connect this legal subset to the full machine semantics.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.omrEntryInFiniteEnvelope_finite",
            "scope": "Finite subtype for assembler-supported OMR entry values 1 through 15; zero is excluded.",
            "evidence": "proofs_lean/evidence/isa-bounds/reference.json: exhaustive `u8` OMR destination selector probes 0..255; exactly 1..15 are accepted.",
            "missing": "Proof that all assembler-accepted OMR operands parse into this subtype, plus the other operand fields and whole-line finiteness.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.natBelow_finite",
            "scope": "Every subtype of Nat below an arbitrary bound is finite, by injection into Fin bound.",
            "evidence": "General Lean encoding argument; per-field numeric bounds remain supported by their individual assembler probes.",
            "missing": "A PE operand/line carrier combining these bounded scalar fields and parser correspondence proofs.",
        }, {
            "source": "proofs_lean/ProofsLean/FiniteIssue.lean",
            "sha256": digest(ROOT / "ProofsLean/FiniteIssue.lean"),
            "theorem": "ProofsLean.MNCore.Issue.optionNatBelow_finite",
            "scope": "Optional Nat values whose present payloads are below an arbitrary bound form a finite subtype.",
            "evidence": "General Lean encoding argument; optional operand-field bounds are recorded in the ISA boundary evidence.",
            "missing": "A PE operand/line carrier combining these bounded scalar fields and parser correspondence proofs.",
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
