"""Finite raw PE memory read experiment through ALU passa, not full ISA proof."""
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


def initial_payload(words: int) -> str:
    return "".join(f"{(0x12345678 + 1664525 * i) % 2**32:08X}" for i in range(words))


def program(vectors: str) -> tuple[str, list[int]]:
    rows = [row.split("\t") for row in vectors.splitlines()]
    if not rows or len(rows) % 4 or any(len(row) != 7 for row in rows):
        raise ValueError("expected four-cycle groups")
    lines, expected = [], []
    for index in range(len(rows) // 4):
        group = rows[4 * index:4 * index + 4]
        bank, operand = group[0][1:3]
        if bank not in {"m", "n", "r", "s", "t"} or not re.fullmatch(r"\$l{0,2}[mnrst][0-9v,\[\]]*", operand):
            raise ValueError("unexpected operand spelling")
        for cycle, row in enumerate(group):
            number, memory, source, c, address, high, low = row
            if (int(number), memory, source, int(c)) != (index, bank, operand, cycle):
                raise ValueError("inconsistent cycle group")
            expected.extend([int(high), int(low)])
        capacity = 4096 if bank in {"m", "n"} else 512 if bank in {"r", "s"} else 16
        if bank == "t":
            # T debug commands have special access semantics. Initialize via
            # four explicit two-long-word cycle writes from a known GRF region.
            lines.extend([f"d set $lr0n0c0b0m0p0 8 {initial_payload(16)}",
                          "lpassa $llr0v $t", "nop/2"])
        else:
            lines.append(f"d set $l{bank}0n0c0b0m0p0 {capacity // 2} {initial_payload(capacity)}")
        lines.extend(["d set $ls64n0c0b0m0p0 8 " + "FFFFFFFFFFFFFFFF" * 8,
                      f"lpassa {operand} $lls64v", "nop/2", "d get $ls64n0c0b0m0p0 8"])
    return "\n".join(lines) + "\n", expected


def observations(output: str, count: int) -> list[int]:
    rows = [line for line in output.splitlines() if line.startswith("DEBUG-")]
    if len(rows) != count:
        raise ValueError(f"expected {count} output words, got {len(rows)}")
    result = []
    for index, line in enumerate(rows):
        addr = 64 + 2 * (index % 8)
        match = re.fullmatch(rf"DEBUG-GREG1\(n0c0b0m0p0,{addr}\):.*v:0x([0-9a-fA-F]+)\).*", line)
        if not match:
            raise ValueError(f"unexpected output address or PE: {line}")
        result.append(int(match[1], 16))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    sources = [ROOT / "ProofsLean/IntegerALU.lean", ROOT / "ProofsLean/PEMemory.lean",
               ROOT / "MemoryProbe.lean", Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources]
    subprocess.run([lake, "build", "memory_probe"], cwd=ROOT, check=True, capture_output=True, timeout=300)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/memory_probe")], check=True,
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
    differences = [{"index": i // 2, "half": i % 2, "oracle": oracle.splitlines()[i // 2], "observed": got}
                   for i, (want, got) in enumerate(zip(expected, actual)) if want != got]
    counts = dict(sorted(Counter(row.split("\t")[1] for row in oracle.splitlines()).items()))
    bad_cycles = {item["index"] for item in differences}
    report = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "finite_lean_datapath_reference_comparison",
        "scope": "LM0/LM1/GRF0/GRF1/T raw reads via lpassa; 32/64/128-bit accesses; scalar/strided/wrapping/flat addresses; all four cycles; one PE; BAR=0, no indirect/madpe/masks/hazards",
        "programs": len(expected) // 8, "cases": len(expected) // 2, "cases_per_spelling": counts,
        "matched": len(expected) // 2 - len(bad_cycles), "differences": differences,
        "vectors_sha256": sha(oracle.encode()), "vsm_sha256": sha(vsm.encode()),
        "reference_output_sha256": sha(raw.encode()), "sources": hashes,
        "proves_universal_conformance": False, "proves_isa_completeness": False, "proves_optimality": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_name("vectors.tsv").write_text(oracle)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cycles": report["cases"], "matched": report["matched"], "differences": len(differences)}))
    if differences:
        print(json.dumps(differences[:8], indent=2))
        raise SystemExit("PE memory datapath differs from the reference")


if __name__ == "__main__":
    main()
