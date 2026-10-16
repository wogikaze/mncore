"""Probe assembler operand-role validation needed by finite line carriers."""
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
    ("lm0_output", "zero $m0", True),
    ("lm1_output", "zero $n0", True),
    ("grf0_output", "zero $r0", True),
    ("grf1_output", "zero $s0", True),
    ("t_single_output", "zero $t", True),
    ("t_duplicate_output", "zero $t $t", False),
    ("lm0_duplicate_output", "zero $m0 $m0", False),
    ("omr_multiple_outputs", "zero $omr1 $omr2", False),
    ("omr_single_output", "zero $omr1", True),
    ("nowrite_single_output", "zero $nowrite", True),
    ("nowrite_duplicate_output", "zero $nowrite $nowrite", False),
    ("bar_lm0_output", "zero $mb", True),
    ("bar_lm1_output", "zero $nb", True),
    ("forward_aluf_output", "zero $aluf", False),
    ("forward_mauf_output", "zero $mauf", False),
    ("forward_lbf_output", "zero $lbf", False),
    ("forward_mreadf_output", "zero $mreadf", False),
    ("matrix_x_output", "zero $lx0", False),
    ("matrix_y_output", "zero $ly0", False),
    ("l1bm_output", "zero $lb0", False),
    ("l2bm_output", "zero $lc0", False),
    ("dar_output", "zero $dar0", False),
    ("fixed_l2bid_output", "zero $l2bid", False),
    ("fixed_l1bid_output", "zero $l1bid", False),
    ("fixed_mabid_output", "zero $mabid", False),
    ("peid_output", "zero $peid", False),
    ("fixed_subpeid_output", "zero $subpeid", False),
    ("fixed_msb1_output", "zero $msb1", False),
    ("alu_memory_output", "iadd $m0 $n0 $m0", True),
    ("alu_t_output", "iadd $m0 $n0 $t", True),
    ("alu_fixed_output", "iadd $m0 $n0 $peid", False),
    ("alu_matrix_output", "iadd $m0 $n0 $lx0", False),
    ("matrix_write_register_output", "gmwrite $aluf $lx0", True),
    ("matrix_write_memory_output", "gmwrite $aluf $m0", False),
    ("matrix_read_memory_output", "gmread $lx0 $m0", True),
    ("matrix_read_register_output", "gmread $lx0 $lx0", False),
    ("mau_memory_output", "dvadd $m0 $n0 $m0", True),
    ("mau_matrix_output", "dvadd $m0 $n0 $lx0", False),
    ("l1bm_to_regs_order", "l1bmm $lb0 $m0", True),
    ("l1bm_to_regs_reversed", "l1bmm $m0 $lb0", False),
    ("l2bm_to_l1bm_order", "l2bmb $lc0 $lb0", True),
    ("l2bm_to_l1bm_reversed", "l2bmb $lb0 $lc0", False),
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
        "experiment": "assemble3 operand-role and duplicate-destination validation",
        "scope": "Focused zero, ALU, MAU, matrix, L1BM, and L2BM probes; not an exhaustive per-opcode operand grammar.",
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
