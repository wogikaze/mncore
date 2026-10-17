"""Record Rust parser fallbacks in every checked-in problem answer."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
SCANNER = REPO / "viz/core/src/bin/parser_gap_scan.rs"
SPELLINGS_SOURCE = REPO / "mncompile/machine.py"
REFERENCE = ROOT / "evidence/parser-gap-audit/answers.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    coverage = json.loads((ROOT / "coverage.json").read_text())
    spellings = [row["spelling"] for row in coverage["syntax_candidates"]]
    with tempfile.TemporaryDirectory(prefix="mncore-opcode-candidates-") as directory:
        spelling_file = Path(directory) / "spellings.txt"
        spelling_file.write_text("\n".join(spellings) + "\n")
        result = subprocess.run(
            ["cargo", "run", "--quiet", "--manifest-path", "viz/core/Cargo.toml",
             "--bin", "parser_gap_scan", "--", "--spellings", str(spelling_file)],
            cwd=REPO, capture_output=True, text=True, timeout=300,
        )
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    audit = json.loads(result.stdout)
    expected_raw_probes = {
        "alu_source": "src",
        "alu_destination": "dst",
        "zero_destination": "dst",
        "matrix_read_source": "src",
        "l1bm_source": "src",
    }
    raw_probes = audit.get("raw_operand_fallback_probes", [])
    if len(raw_probes) != len(expected_raw_probes):
        raise ValueError("raw-operand fallback probe inventory changed")
    for probe in raw_probes:
        expected_role = expected_raw_probes.get(probe["case"])
        result = probe["result"]
        if expected_role is None or not result["parsed"]:
            raise ValueError(f"Rust parser did not parse raw fallback fixture: {probe['case']}")
        expressions = result["expressions"]
        if len(expressions) != 1 or expressions[0]["raw_operands"] != [
            {"role": expected_role, "operand": "$qraw"}
        ]:
            raise ValueError(f"Rust Raw fallback changed for fixture: {probe['case']}")
        expected_raw_probes.pop(probe["case"])
    if expected_raw_probes:
        raise ValueError(f"missing Raw fallback fixtures: {sorted(expected_raw_probes)}")
    candidate_raw_probes = audit.get("opcode_candidate_raw_operand_probes", [])
    expected_candidate_slots = sum(
        row["result"]["expressions"][0]["source_count"]
        + row["result"]["expressions"][0]["destination_count"]
        for row in audit["opcode_candidate_results"]
    )
    if len(candidate_raw_probes) != expected_candidate_slots:
        raise ValueError(
            f"expected {expected_candidate_slots} candidate operand probes, "
            f"got {len(candidate_raw_probes)}"
        )
    for probe in candidate_raw_probes:
        result = probe["result"]
        raw = result.get("raw_operands", [])
        if (not result["parsed"] or len(raw) != 1 or raw[0]["operand"] != "$qraw"
                or raw[0]["role"] not in {"src", "dst"}):
            raise ValueError(
                f"candidate Raw fallback changed: {probe['spelling']} "
                f"operand slot {probe['operand_token_index']}"
            )
    answers = sorted((REPO / "problems").rglob("answer.vsm"))
    audit["input_hashes"] = [
        {"path": path.relative_to(REPO).as_posix(), "sha256": sha(path)}
        for path in answers
    ]
    audit["scanner"] = {
        "path": SCANNER.relative_to(REPO).as_posix(),
        "sha256": sha(SCANNER),
    }
    audit["opcode_candidate_source"] = {
        "path": SPELLINGS_SOURCE.relative_to(REPO).as_posix(),
        "sha256": sha(SPELLINGS_SOURCE),
        "candidate_count": len(spellings),
    }
    audit["opcode_candidate_raw_probe_scope"] = (
        "Each operand token in one compiler-generated parser-arity fixture for "
        "each syntax candidate was replaced by $qraw. This establishes parser "
        "fallback behavior for those slots only; it does not establish assembler "
        "acceptance, complete ISA spelling coverage, or legality."
    )
    text = json.dumps(audit, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if not REFERENCE.exists() or REFERENCE.read_text() != text:
            raise SystemExit("parser-gap answer audit is stale; regenerate it")
    else:
        REFERENCE.parent.mkdir(parents=True, exist_ok=True)
        REFERENCE.write_text(text)
    print(
        f"recorded {audit['answer_files']} answers, "
        f"{len(audit['raw_operand_occurrences'])} raw operands, "
        f"{len(audit['other_opcode_occurrences'])} other opcodes, "
        f"{len(audit['opcode_candidate_results'])} syntax candidates"
    )


if __name__ == "__main__":
    main()
