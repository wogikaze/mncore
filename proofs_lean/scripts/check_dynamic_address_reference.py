"""Compare BAR/T-indirect/MADPE reads with explicit per-PE, per-cycle inputs."""
from __future__ import annotations

import argparse
import json
import os
import re
import resource
import shutil
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

from check_memory_reference import initial_payload, sha

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def program(vectors: str) -> tuple[str, list[int]]:
    rows = [line.split("\t") for line in vectors.splitlines()]
    if not rows or len(rows) % 16 or any(len(row) != 10 for row in rows):
        raise ValueError("expected complete four-PE/four-cycle groups")
    lines, expected = [], []
    for index in range(len(rows) // 16):
        group = rows[index * 16:index * 16 + 16]
        bank, operand, bar = group[0][1:4]
        if bank not in {"m", "n"} or not re.fullmatch(r"\$l{0,2}[mn]t?[0-9v,j\[\]]+", operand):
            raise ValueError("invalid dynamic LM operand")
        if not 0 <= int(bar) < 4096:
            raise ValueError("invalid BAR")
        for position, row in enumerate(group):
            number, memory, source, base, t, pe, cycle, address, high, low = row
            if (int(number), memory, source, base, int(pe), int(cycle)) != (
                    index, bank, operand, bar, position // 4, position % 4):
                raise ValueError("inconsistent dynamic-address group")
            if not 0 <= int(t) < 2**64:
                raise ValueError("T input must be 64 bits")
            expected.extend([int(high), int(low)])
        lines.extend([f"zero ${bank}b", "nop/2"])
        for pe in range(4):
            location = f"n0c0b0m0p{pe}"
            lines.append(f"d set $l{bank}0{location} 2048 {initial_payload(4096)}")
            t_payload = "".join(f"{int(row[4]):016X}A5A5A5A55A5A5A5A" for row in group[pe*4:pe*4+4])
            lines.extend([f"d set $lr0{location} 8 {t_payload}",
                          f"d set $ls32{location} 1 {int(bar) << 32:016X}",
                          f"d set $ls64{location} 8 " + "FFFFFFFFFFFFFFFF" * 8])
        lines.extend(["lpassa $llr0v $t", "nop/2", f"lpassa $ls32 ${bank}b", "nop/2",
                      f"lpassa {operand} $lls64v", "nop/2"])
        for pe in range(4):
            lines.append(f"d get $ls64n0c0b0m0p{pe} 8")
    return "\n".join(lines) + "\n", expected


def observations(output: str, count: int) -> list[int]:
    rows = [line for line in output.splitlines() if line.startswith("DEBUG-")]
    if len(rows) != count:
        raise ValueError(f"expected {count} words, got {len(rows)}")
    result = []
    for index, line in enumerate(rows):
        pe, addr = (index // 8) % 4, 64 + 2 * (index % 8)
        match = re.fullmatch(rf"DEBUG-GREG1\(n0c0b0m0p{pe},{addr}\):.*v:0x([0-9a-fA-F]+)\).*", line)
        if not match:
            raise ValueError(f"unexpected output PE/address: {line}")
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
               ROOT / "DynamicAddressProbe.lean", ROOT / "scripts/check_memory_reference.py",
               Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources]
    subprocess.run([lake, "build", "dynamic_address_probe"], cwd=ROOT, check=True, capture_output=True, timeout=300)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/dynamic_address_probe")], check=True,
                            capture_output=True, text=True, timeout=60).stdout
    vsm, expected = program(oracle)
    assembly = subprocess.run([str(assembler), "--instruction-mode", "flat"], input=vsm,
                              capture_output=True, text=True, timeout=60)
    if assembly.returncode:
        raise SystemExit(f"official assembler rejected probe:\n{assembly.stderr}")
    run = subprocess.run([str(emulator), "--offchip-memory-init", "zero"], input=assembly.stdout,
                         capture_output=True, text=True, timeout=180,
                         env={**os.environ, "OMP_THREAD_LIMIT": "1"})
    if run.returncode:
        raise SystemExit(f"official emulator rejected probe:\n{run.stderr[-4000:]}")
    raw = run.stdout + run.stderr
    actual = observations(raw, len(expected))
    if any(sha(p.read_bytes()) != item["sha256"] for p, item in zip(sources, hashes)):
        raise SystemExit("sources/tools changed during comparison; evidence not saved")
    differences = [{"index": i // 2, "half": i % 2, "oracle": oracle.splitlines()[i // 2], "observed": got}
                   for i, (want, got) in enumerate(zip(expected, actual)) if want != got]
    bad_cycles = {row["index"] for row in differences}
    report = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "finite_lean_datapath_reference_comparison",
        "scope": "LM0/LM1 BAR and MADPE; LM0 T indirect; 32/64/128-bit reads; all four PEs and cycles; nonaligned/wrapping values; 64-bit T extremes; auto/flat indirect schedules; no masks or port/hazard conformance",
        "programs": len(expected) // 32, "cases": len(expected) // 2,
        "cases_per_spelling": dict(sorted(Counter(row.split("\t")[1] for row in oracle.splitlines()).items())),
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
        raise SystemExit("dynamic-address model differs from reference")


if __name__ == "__main__":
    main()
