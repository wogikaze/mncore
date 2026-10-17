"""Record official assembler output shapes for all checked-in problem answers."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ASSEMBLER = REPO / "judge/judge-py/mncore2_emuenv/assemble3"
REFERENCE = ROOT / "evidence/answer-encoding/reference.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    answers = sorted((REPO / "problems").rglob("answer.vsm"))
    observations = []
    with tempfile.TemporaryDirectory(prefix="mncore-answer-encoding-") as directory:
        for index, source in enumerate(answers):
            temporary = Path(directory) / f"answer-{index}.vsm"
            temporary.write_bytes(source.read_bytes())
            result = subprocess.run(
                [str(ASSEMBLER), "--instruction-mode", "flat", str(temporary)],
                capture_output=True, text=True, timeout=60,
            )
            if result.returncode != 0:
                raise SystemExit(
                    f"assembler rejected {source.relative_to(REPO)}: "
                    f"{(result.stderr.splitlines() or [''])[0]}"
                )
            words = []
            for line in result.stdout.splitlines():
                fields = line.split()
                if len(fields) != 2 or fields[0] not in {"j", "m"}:
                    raise SystemExit(f"unexpected assembler output in {source}: {line!r}")
                word = {
                    "kind": fields[0],
                    "bit_width": len(fields[1]),
                    "binary": set(fields[1]) <= {"0", "1"},
                }
                expected_width = {"j": 426, "m": 82}[fields[0]]
                if not word["binary"] or word["bit_width"] != expected_width:
                    raise SystemExit(f"unexpected encoded word shape in {source}: {word}")
                words.append(word)
            observations.append({
                "source": source.relative_to(REPO).as_posix(),
                "source_sha256": sha(source),
                "assembler_output_lines": len(words),
                "words": words,
            })
    counts = {kind: sum(word["kind"] == kind for row in observations for word in row["words"])
              for kind in ("j", "m")}
    report = {
        "schema_version": 1,
        "experiment": "flat assembler output shapes for all checked-in problem answers",
        "scope": "All 73 answer.vsm files in the repository. This is corpus evidence, not proof that every legal source has these shapes.",
        "answer_count": len(answers),
        "output_word_count": sum(row["assembler_output_lines"] for row in observations),
        "word_counts_by_kind": counts,
        "tool_hashes": [
            {"path": ASSEMBLER.relative_to(REPO).as_posix(), "sha256": sha(ASSEMBLER)},
            {"path": Path(__file__).resolve().relative_to(REPO).as_posix(), "sha256": sha(Path(__file__).resolve())},
        ],
        "observations": observations,
        "proves_all_assembler_outputs_have_these_shapes": False,
        "proves_isa_completeness": False,
    }
    if len(answers) != 73:
        raise SystemExit(f"expected 73 answers, found {len(answers)}")
    text = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if not REFERENCE.exists() or REFERENCE.read_text() != text:
            raise SystemExit("answer encoding reference is stale; regenerate it")
    else:
        REFERENCE.parent.mkdir(parents=True, exist_ok=True)
        REFERENCE.write_text(text)
    print(f"recorded {len(answers)} answers and {report['output_word_count']} encoded words")


if __name__ == "__main__":
    main()
