"""Compare the Lean integer datapath fragment against the official tools.

This finite experiment is not ISA completeness, universal conformance, or an
optimality proof. Only unmasked, unreduced, scalar GRF operations are exercised.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def program(vectors: str) -> tuple[str, list[tuple[int, int, int]]]:
    lines, expected = [], []
    location = "n0c0b0m0p0"
    for row in vectors.splitlines():
        spelling, binary, a, b, high, low, mask = row.split("\t")
        if not re.fullmatch(r"[a-z]+", spelling) or binary not in {"true", "false"}:
            raise ValueError(f"invalid oracle row: {row}")
        for bank, addr, value in [("r", 0, int(a)), ("r", 2, 0x0123456789abcdef),
                                  ("s", 4, int(b)), ("s", 6, 0xfedcba9876543210)]:
            lines.append(f"d set $l{bank}{addr}{location} 1 {value:016X}")
        operands = "$llr0 $lls4" if binary == "true" else "$llr0"
        lines.extend([f"{spelling} {operands} $llr8 $omr1", "nop/2",
                      f"d get $lr8{location} 1", f"d get $lr10{location} 1",
                      f"d get $omr1{location} 1"])
        expected.append((int(high), int(low), int(mask)))
    if not expected:
        raise ValueError("empty oracle output")
    return "\n".join(lines) + "\n", expected


def observations(output: str, count: int) -> list[tuple[int, int, int]]:
    rows = [line for line in output.splitlines() if line.startswith("DEBUG-")]
    if len(rows) != 6 * count:
        raise ValueError(f"expected {6 * count} debug records, got {len(rows)}")
    observed = []
    for index in range(count):
        group = rows[index * 6:(index + 1) * 6]
        values = []
        for line, addr in zip(group[:2], [8, 10]):
            match = re.fullmatch(rf"DEBUG-GREG0\(n0c0b0m0p0,{addr}\):.*v:0x([0-9A-Fa-f]+)\).*", line)
            if not match:
                raise ValueError(f"unexpected GRF output: {line}")
            values.append(int(match[1], 16))
        masks = []
        for line in group[2:]:
            match = re.fullmatch(r"DEBUG-OMR\(n0c0b0m0p0,1\):Mask\{([0-9]+)\}.*", line)
            if not match:
                raise ValueError(f"unexpected mask output: {line}")
            masks.append(int(match[1]))
        if len(set(masks)) != 1:
            raise ValueError(f"cycle flags differ for broadcast scalar operands: {masks}")
        observed.append((*values, masks[0]))
    return observed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # The official assembler aborts for some invalid spellings; do not leave cores.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    subprocess.run([lake, "build", "alu_probe"], cwd=ROOT, check=True, capture_output=True, timeout=300)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/alu_probe")], check=True,
                            capture_output=True, text=True, timeout=60).stdout
    vsm, expected = program(oracle)
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    assembly = subprocess.run([str(assembler), "--instruction-mode", "flat"], input=vsm,
                              capture_output=True, text=True, timeout=60)
    if assembly.returncode:
        raise SystemExit(f"official assembler rejected probe:\n{assembly.stderr}")
    run = subprocess.run([str(emulator), "--offchip-memory-init", "zero"], input=assembly.stdout,
                         capture_output=True, text=True, check=True, timeout=180,
                         env={**os.environ, "OMP_THREAD_LIMIT": "1"})
    raw = run.stdout + run.stderr
    actual = observations(raw, len(expected))
    differences = [{"index": index, "oracle": line, "observed": got}
                   for index, (line, wanted, got) in enumerate(zip(oracle.splitlines(), expected, actual))
                   if wanted != got]
    sources = [ROOT / "ProofsLean/IntegerALU.lean", ROOT / "ALUProbe.lean",
               Path(__file__).resolve(), assembler, emulator]
    counts = dict(sorted(Counter(row.split("\t")[0] for row in oracle.splitlines()).items()))
    report = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "finite_lean_datapath_reference_comparison",
        "scope": f"{len(counts)} integer spellings; 30 common operand pairs plus 48 width-specific boundary pairs for each shift spelling; unmasked unreduced scalar GRF accesses; one PE; all four broadcast cycles",
        "cases_per_spelling": counts,
        "cases": len(expected), "matched": len(expected) - len(differences),
        "differences": differences, "vectors_sha256": sha(oracle.encode()),
        "vsm_sha256": sha(vsm.encode()), "reference_output_sha256": sha(raw.encode()),
        "sources": [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources],
        "proves_universal_conformance": False, "proves_isa_completeness": False,
        "proves_optimality": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_name("vectors.tsv").write_text(oracle)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(expected), "matched": report["matched"], "differences": len(differences)}))
    if differences:
        print(json.dumps(differences[:5], indent=2))
        raise SystemExit("Lean datapath differs from the reference")


if __name__ == "__main__":
    main()
