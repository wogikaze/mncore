"""Probe assembler output-role validation needed by finite destination carriers."""
from __future__ import annotations

import hashlib
import json
import resource
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
ASSEMBLER = REPO / "judge/judge-py/mncore2_emuenv/assemble3"
REFERENCE = ROOT / "evidence/output-roles/reference.json"

CASES = [
    ("t_single_output", "zero $t", True),
    ("t_duplicate_output", "zero $t $t", False),
    ("omr_single_output", "zero $omr1", True),
    ("nowrite_single_output", "zero $nowrite", True),
    ("nowrite_duplicate_output", "zero $nowrite $nowrite", False),
    ("peid_output", "zero $peid", False),
    ("l2bid_output", "zero $l2bid", False),
    ("mabid_output", "zero $mabid", False),
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if not ASSEMBLER.exists():
        raise SystemExit(f"official assembler is unavailable: {ASSEMBLER}")
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    observations = []
    with tempfile.TemporaryDirectory(prefix="mncore-output-role-") as temporary:
        directory = Path(temporary)
        for name, source, expected in CASES:
            path = directory / f"{name}.vsm"
            path.write_text(source + "\n")
            result = subprocess.run(
                [str(ASSEMBLER), "--instruction-mode", "flat", str(path)],
                capture_output=True, text=True, timeout=30,
            )
            accepted = result.returncode == 0
            observations.append({
                "case": name,
                "source": source,
                "expected_accepted": expected,
                "accepted": accepted,
                "returncode": result.returncode,
                "words": len(result.stdout.splitlines()) if accepted else None,
                "diagnostic": (result.stderr.splitlines() or [""])[0],
            })
    if any(item["accepted"] != item["expected_accepted"] for item in observations):
        raise SystemExit("assemble3 output-role observations differ from expectations")
    report = {
        "schema_version": 1,
        "experiment": "assemble3 output-role and duplicate-destination validation",
        "scope": "Focused zero-op probes for T, OMR, nowrite, and fixed operands; not an exhaustive per-opcode destination grammar.",
        "tool_hashes": [
            {"path": "judge/judge-py/mncore2_emuenv/assemble3", "sha256": sha(ASSEMBLER)},
            {"path": "proofs_lean/scripts/check_output_roles_reference.py", "sha256": sha(Path(__file__))},
        ],
        "observations": observations,
        "limitations": [
            "This records assembler behavior; it does not prove correspondence with the Lean issue checker.",
            "The Lean finite destination carrier still needs a proof that accepted operands meet its list-shape conditions.",
        ],
    }
    REFERENCE.parent.mkdir(parents=True, exist_ok=True)
    REFERENCE.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"recorded {len(observations)} assemble3 output-role probes")


if __name__ == "__main__":
    main()
