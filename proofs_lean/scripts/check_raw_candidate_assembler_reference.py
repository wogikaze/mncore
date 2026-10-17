"""Record assemble3 results for Raw-replacement parser candidate probes."""
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
REFERENCE = ROOT / "evidence/raw-candidate-assembler/reference.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not ASSEMBLER.exists():
        raise SystemExit(f"official assembler is unavailable: {ASSEMBLER}")
    audit = json.loads(PARSER_AUDIT.read_text())
    probes = audit["opcode_candidate_raw_operand_probes"]
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    observations = []
    with tempfile.TemporaryDirectory(prefix="mncore-raw-candidate-") as temporary:
        directory = Path(temporary)
        for index, probe in enumerate(probes):
            path = directory / f"{index}.vsm"
            path.write_text(probe["source"] + "\n")
            result = subprocess.run(
                [str(ASSEMBLER), "--instruction-mode", "flat", str(path)],
                capture_output=True, text=True, timeout=30,
            )
            diagnostic = (result.stderr.splitlines() or [""])[0]
            diagnostic = diagnostic.replace(str(directory), "<TMP>")
            observations.append({
                "spelling": probe["spelling"],
                "operand_token_index": probe["operand_token_index"],
                "accepted": result.returncode == 0,
                "returncode": result.returncode,
                "words": len(result.stdout.splitlines()) if result.returncode == 0 else None,
                "diagnostic": diagnostic,
            })
    report = {
        "schema_version": 1,
        "experiment": "assemble3 acceptance of $qraw replacements in compiler-candidate operand slots",
        "scope": audit["opcode_candidate_raw_probe_scope"],
        "tool_hashes": [
            {"path": ASSEMBLER.relative_to(REPO).as_posix(), "sha256": sha(ASSEMBLER)},
            {"path": PARSER_AUDIT.relative_to(REPO).as_posix(), "sha256": sha(PARSER_AUDIT)},
            {"path": Path(__file__).relative_to(REPO).as_posix(), "sha256": sha(Path(__file__))},
        ],
        "probe_count": len(observations),
        "accepted_count": sum(item["accepted"] for item in observations),
        "rejected_count": sum(not item["accepted"] for item in observations),
        "observations": observations,
        "limitations": [
            "Only one compiler-generated operand template per syntax candidate is used.",
            "The candidates do not exhaust the manual ISA or all accepted operand spellings.",
            "Rejecting these $qraw mutations does not prove that all Raw strings are rejected.",
        ],
    }
    text = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if not REFERENCE.exists() or REFERENCE.read_text() != text:
            raise SystemExit("Raw-candidate assembler reference is stale; regenerate it")
    else:
        REFERENCE.parent.mkdir(parents=True, exist_ok=True)
        REFERENCE.write_text(text)
    print(
        f"recorded {report['probe_count']} probes: {report['accepted_count']} accepted, "
        f"{report['rejected_count']} rejected by assemble3"
    )


if __name__ == "__main__":
    main()
