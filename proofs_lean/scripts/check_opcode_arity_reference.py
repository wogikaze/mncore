"""Compare all compiler opcode candidates with assemble3 destination boundaries."""
from __future__ import annotations

import argparse
import hashlib
import json
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ASSEMBLER = REPO / "judge/judge-py/mncore2_emuenv/assemble3"
PARSER_AUDIT = ROOT / "evidence/parser-gap-audit/answers.json"
REFERENCE = ROOT / "evidence/opcode-arity/reference.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def width_prefix(spelling: str) -> str:
    precision = spelling[0]
    if precision in "dl":
        return "ll"
    if precision in "fgi":
        return "l"
    return ""


def template(row: dict) -> tuple[str, str, list[str]]:
    spelling = row["spelling"]
    expression = row["result"]["expressions"][0]
    opcode_class = expression["class"]
    source_count = expression["source_count"]
    width = width_prefix(spelling)

    if opcode_class == "alu":
        sources = " ".join([f"${width}m0"] * source_count)
        destinations = [f"${width}m0", f"${width}n0", f"${width}r0",
                        f"${width}s0", "$t", "$omr1"]
    elif opcode_class == "imm":
        sources = 'i"0"'
        destinations = [f"${width}n0", f"${width}r0", f"${width}s0", "$t", "$omr1"]
    elif opcode_class == "zero":
        sources = ""
        destinations = ["$lm0", "$ln0", "$lr0", "$ls0", "$t", "$omr1"]
    elif opcode_class == "mau" and spelling[1] == "m":
        source_operands = ["$lx", f"${width}r0v", "$mauf"]
        sources = " ".join(source_operands[:source_count])
        destinations = [f"${width}s0v", f"${width}m0", f"${width}n0",
                        f"${width}r0", "$t", "$omr1"]
    elif opcode_class == "mau":
        sources = " ".join([f"${width}m0"] * source_count)
        destinations = [f"${width}m0", f"${width}n0", f"${width}r0",
                        f"${width}s0", "$t", "$omr1"]
    elif opcode_class == "mat_read":
        sources = "$llx0" if spelling[0] == "h" else "$lx0"
        destinations = [f"${width}m0", f"${width}n0", f"${width}r0",
                        f"${width}s0", "$t"]
    elif opcode_class == "mat_write":
        sources = "$aluf"
        destinations = ["$lx0"]
    else:
        raise ValueError(f"unsupported parser class: {opcode_class}")
    return opcode_class, sources, destinations


def assemble(source: str, directory: Path, name: str) -> tuple[bool, int | None, str]:
    path = directory / f"{name}.vsm"
    path.write_text(source)
    result = subprocess.run(
        [str(ASSEMBLER), "--instruction-mode", "flat", str(path)],
        capture_output=True, text=True, timeout=30,
    )
    accepted = result.returncode == 0
    words = len(result.stdout.splitlines()) if accepted else None
    diagnostic = (result.stderr.splitlines() or [""])[0]
    return accepted, words, diagnostic


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=REFERENCE)
    args = parser.parse_args()
    if not ASSEMBLER.exists():
        raise SystemExit(f"official assembler is unavailable: {ASSEMBLER}")

    audit = json.loads(PARSER_AUDIT.read_text())
    candidates = audit["opcode_candidate_results"]
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    observations = []
    with tempfile.TemporaryDirectory(prefix="mncore-opcode-arity-") as temporary:
        directory = Path(temporary)
        for index, row in enumerate(candidates):
            spelling = row["spelling"]
            opcode_class, sources, destinations = template(row)
            maximal = f"{spelling} {sources} {' '.join(destinations)}\n"
            over = f"{spelling} {sources} {' '.join(destinations + [destinations[0]])}\n"
            accepted, words, diagnostic = assemble(maximal, directory, f"{index}-max")
            overflow_accepted, overflow_words, overflow_diagnostic = assemble(
                over, directory, f"{index}-overflow")
            observations.append({
                "spelling": spelling,
                "class": opcode_class,
                "parser_source_count": row["result"]["expressions"][0]["source_count"],
                "destination_operands": destinations,
                "maximal_source": maximal.rstrip("\n"),
                "maximal_accepted": accepted,
                "maximal_words": words,
                "maximal_diagnostic": diagnostic,
                "duplicate_source": over.rstrip("\n"),
                "duplicate_accepted": overflow_accepted,
                "duplicate_words": overflow_words,
                "duplicate_diagnostic": overflow_diagnostic,
            })

    report = {
        "schema_version": 1,
        "experiment": "assemble3 acceptance of compiler opcode candidates and duplicate-output overflow",
        "scope": "184 compiler-generated ALU/MAU/matrix/immediate/zero candidates with one parser-arity-correct source template and the listed destination categories; not the complete manual ISA.",
        "tool_hashes": [
            {"path": "judge/judge-py/mncore2_emuenv/assemble3", "sha256": sha(ASSEMBLER)},
            {"path": "proofs_lean/evidence/parser-gap-audit/answers.json", "sha256": sha(PARSER_AUDIT)},
            {"path": "proofs_lean/scripts/check_opcode_arity_reference.py", "sha256": sha(Path(__file__))},
        ],
        "candidate_count": len(candidates),
        "accepted_maximal_candidates": sum(item["maximal_accepted"] for item in observations),
        "rejected_duplicate_overflows": sum(not item["duplicate_accepted"] for item in observations),
        "observations": observations,
        "limitations": [
            "A single source/destination template per spelling does not exhaust operand encodings.",
            "The candidates omit L1BM/L2BM transfer opcodes, wait/noforward, and any manual spelling absent from the compiler inventory.",
            "Rejecting one extra duplicate output does not prove that every other destination form is covered or that this rule applies to every assembler-accepted syntax.",
        ],
    }
    if report["candidate_count"] != 184 or report["accepted_maximal_candidates"] != 184 or report["rejected_duplicate_overflows"] != 184:
        raise SystemExit("opcode arity experiment differs from its expected boundary results")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print("recorded all 184 candidates: maximal templates accepted; duplicate-output overflows rejected")


if __name__ == "__main__":
    main()
