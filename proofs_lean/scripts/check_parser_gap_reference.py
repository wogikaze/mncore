"""Record Rust parser fallbacks in every checked-in problem answer."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
SCANNER = REPO / "viz/core/src/bin/parser_gap_scan.rs"
REFERENCE = ROOT / "evidence/parser-gap-audit/answers.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = subprocess.run(
        ["cargo", "run", "--quiet", "--manifest-path", "viz/core/Cargo.toml",
         "--bin", "parser_gap_scan"],
        cwd=REPO, capture_output=True, text=True, timeout=300,
    )
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    audit = json.loads(result.stdout)
    answers = sorted((REPO / "problems").rglob("answer.vsm"))
    audit["input_hashes"] = [
        {"path": path.relative_to(REPO).as_posix(), "sha256": sha(path)}
        for path in answers
    ]
    audit["scanner"] = {
        "path": SCANNER.relative_to(REPO).as_posix(),
        "sha256": sha(SCANNER),
    }
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
        f"{len(audit['other_opcode_occurrences'])} other opcodes"
    )


if __name__ == "__main__":
    main()
