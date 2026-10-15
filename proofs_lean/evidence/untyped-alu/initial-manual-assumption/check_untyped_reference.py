"""Finite comparison of zero/imm/immu/msl/msr on all four PEs of one MAB.

No universal ISA conformance or optimality claim follows from this experiment.
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
    rows = [row.split("\t") for row in vectors.splitlines()]
    if not rows or len(rows) % 4 or any(len(row) != 9 for row in rows):
        raise ValueError("vectors must contain complete four-PE groups")
    lines, expected = [], []
    for index in range(len(rows) // 4):
        group = rows[4 * index:4 * index + 4]
        name, payload = group[0][1:3]
        if name not in {"zero", "imm", "immu", "msl", "msr"} or not 0 <= int(payload) < 2**32:
            raise ValueError("invalid operation or immediate")
        for pe, row in enumerate(group):
            case, op, immediate, number, high, low, out_high, out_low, mask = row
            if (int(case), op, immediate, int(number)) != (index, name, payload, pe):
                raise ValueError("inconsistent group or PE ordering")
            location = f"n0c0b0m0p{pe}"
            for addr, value in [(0, int(high)), (2, int(low)), (8, 2**64 - 1), (10, 2**64 - 1)]:
                lines.append(f"d set $lr{addr}{location} 1 {value:016X}")
            # Avoid accepting an unwritten, initially zero mask as a zero flag.
            lines.append(f"d set $omr1{location} 1 000000000000FFFF")
            expected.append((int(out_high), int(out_low), int(mask)))
        source = f'ui"{payload}" ' if name in {"imm", "immu"} else "$llr0 " if name in {"msl", "msr"} else ""
        lines.extend([f"{name} {source}$llr8 $omr1", "nop/2"])
        for pe in range(4):
            location = f"n0c0b0m0p{pe}"
            lines.extend([f"d get $lr8{location} 1", f"d get $lr10{location} 1",
                          f"d get $omr1{location} 1"])
    return "\n".join(lines) + "\n", expected


def observations(output: str, count: int) -> list[tuple[int, int, int]]:
    lines = [line for line in output.splitlines() if line.startswith("DEBUG-")]
    if len(lines) != count * 6:
        raise ValueError(f"expected {count * 6} debug records, got {len(lines)}")
    result = []
    for index in range(count):
        pe = index % 4
        group = lines[index * 6:(index + 1) * 6]
        words, flags = [], []
        for line, addr in zip(group[:2], [8, 10]):
            match = re.fullmatch(rf"DEBUG-GREG0\(n0c0b0m0p{pe},{addr}\):.*v:0x([0-9a-fA-F]+)\).*", line)
            if not match:
                raise ValueError(f"unexpected word output: {line}")
            words.append(int(match[1], 16))
        for line in group[2:]:
            match = re.fullmatch(rf"DEBUG-OMR\(n0c0b0m0p{pe},1\):Mask\{{([0-9]+)\}}.*", line)
            if not match:
                raise ValueError(f"unexpected flag output: {line}")
            flags.append(int(match[1]))
        if len(set(flags)) != 1:
            raise ValueError("scalar broadcast flags differ between cycles")
        result.append((*words, flags[0]))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    sources = [ROOT / "ProofsLean/IntegerALU.lean", ROOT / "ProofsLean/UntypedALU.lean",
               ROOT / "UntypedProbe.lean", Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources]
    subprocess.run([lake, "build", "untyped_probe"], cwd=ROOT, check=True, capture_output=True, timeout=300)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/untyped_probe")], check=True,
                            capture_output=True, text=True, timeout=60).stdout
    vsm, expected = program(oracle)
    assembly = subprocess.run([str(assembler), "--instruction-mode", "flat"], input=vsm,
                              capture_output=True, text=True, timeout=60)
    if assembly.returncode:
        raise SystemExit(f"official assembler rejected probe:\n{assembly.stderr}")
    run = subprocess.run([str(emulator), "--offchip-memory-init", "zero"], input=assembly.stdout,
                         capture_output=True, text=True, check=True, timeout=180,
                         env={**os.environ, "OMP_THREAD_LIMIT": "1"})
    raw = run.stdout + run.stderr
    actual = observations(raw, len(expected))
    if any(sha(p.read_bytes()) != item["sha256"] for p, item in zip(sources, hashes)):
        raise SystemExit("probe sources/tools changed during comparison; evidence not saved")
    differences = [{"index": i, "oracle": row, "observed": got}
                   for i, (row, want, got) in enumerate(zip(oracle.splitlines(), expected, actual)) if want != got]
    counts = dict(sorted(Counter(row.split("\t")[1] for row in oracle.splitlines()).items()))
    report = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "finite_lean_datapath_reference_comparison",
        "scope": "zero/imm/immu/msl/msr; all four PEs of one MAB; unmasked unreduced scalar GRF; nonzero destination/mask sentinels",
        "programs": len(expected) // 4, "cases": len(expected), "cases_per_spelling": counts,
        "matched": len(expected) - len(differences), "differences": differences,
        "vectors_sha256": sha(oracle.encode()), "vsm_sha256": sha(vsm.encode()),
        "reference_output_sha256": sha(raw.encode()), "sources": hashes,
        "proves_universal_conformance": False, "proves_isa_completeness": False, "proves_optimality": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_name("vectors.tsv").write_text(oracle)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(expected), "matched": report["matched"], "differences": len(differences)}))
    if differences:
        print(json.dumps(differences[:8], indent=2))
        raise SystemExit("untyped datapath differs from the reference")


if __name__ == "__main__":
    main()
