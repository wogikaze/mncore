"""Finite mask-profile comparison: data merging, flush, flags and directives."""
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

from check_memory_reference import sha

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
MODES = {"write", "flush", "both", "register", "directive", "override"}


def mask_input(flags: int) -> int:
    # spassa generates one zero-test flag per 16-bit lane in the high long-word.
    return sum((0 if flags & (1 << bit) else 1) << (16 * bit) for bit in range(4))


def program(vectors: str) -> tuple[str, list[tuple[int, int, int]]]:
    rows = [line.split("\t") for line in vectors.splitlines()]
    if not rows or len(rows) % 4 or any(len(row) != 15 for row in rows):
        raise ValueError("expected complete four-cycle mask groups")
    lines, expected = [], []
    for index in range(len(rows) // 4):
        group = rows[index*4:index*4+4]
        width, mode, seed = group[0][1:4]
        if width not in {"l", "ll"} or mode not in MODES:
            raise ValueError("invalid mask width/mode")
        for cycle, row in enumerate(group):
            case, w, m, s, c, mask, high, low, old_high, old_low, out_high, out_low, flags, mh, ml = row
            if (int(case), w, m, s, int(c)) != (index, width, mode, seed, cycle) or not 0 <= int(mask) < 16:
                raise ValueError("inconsistent mask group")
            expected.append((int(out_high), int(out_low), int(flags)))
        mask_payload = "".join(f"{mask_input(int(row[5])):016X}DEADBEEFCAFEBABE" for row in group)
        data_payload = "".join(f"{int(row[6]):016X}{int(row[7]):016X}" for row in group)
        old_payload = "".join(f"{int(row[8]):016X}{int(row[9]):016X}" for row in group)
        lines.extend(["mask 0", f"d set $lr0n0c0b0m0p0 8 {mask_payload}",
                      f"d set $lr32n0c0b0m0p0 8 {data_payload}",
                      f"d set $ls64n0c0b0m0p0 8 {old_payload}",
                      "d set $ls0n0c0b0m0p0 2 " + "0000000000000000" * 2,
                      "spassa $llr0v $omr1", "spassa $lls0 $omr2"])
        if mode == "directive":
            lines.append(f"mask{width}s 1")
        if mode == "override":
            lines.append("masklls 16")
        selector = "$imr1" if width == "l" else "$llimr1"
        opcode = "spassa/" + selector if mode in {"flush", "both"} else "spassa"
        destination = "$lls64v"
        if mode in {"write", "both"}:
            destination += "/" + selector + ("p" if width == "l" else "")
        flags_destination = "$omr2/" + selector if mode in {"register", "override"} else "$omr2"
        lines.extend([f"{opcode} $llr32v {destination} {flags_destination}", "nop/2", "mask 0",
                      "d get $ls64n0c0b0m0p0 8", "d get $omr2n0c0b0m0p0 1"])
    return "\n".join(lines) + "\n", expected


def observations(output: str, count: int) -> list[tuple[int, int, int]]:
    rows = [line for line in output.splitlines() if line.startswith("DEBUG-")]
    if count % 4 or len(rows) != count * 3:
        raise ValueError("incomplete mask data/flag output")
    result = []
    for index in range(count // 4):
        group = rows[index*12:index*12+12]
        words, flags = [], []
        for offset, line in enumerate(group[:8]):
            addr = 64 + 2 * offset
            match = re.fullmatch(rf"DEBUG-GREG1\(n0c0b0m0p0,{addr}\):.*v:0x([0-9a-fA-F]+)\).*", line)
            if not match:
                raise ValueError(f"unexpected memory output: {line}")
            words.append(int(match[1], 16))
        for line in group[8:]:
            match = re.fullmatch(r"DEBUG-OMR\(n0c0b0m0p0,2\):Mask\{([0-9]+)\}.*", line)
            if not match:
                raise ValueError(f"unexpected flags output: {line}")
            flags.append(int(match[1]))
        result.extend((words[2*c], words[2*c+1], flags[c]) for c in range(4))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    sources = [ROOT / "ProofsLean/IntegerALU.lean", ROOT / "ProofsLean/Masks.lean",
               ROOT / "MaskProbe.lean", ROOT / "scripts/check_memory_reference.py",
               Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources]
    subprocess.run([lake, "build", "mask_probe"], cwd=ROOT, check=True, capture_output=True, timeout=300)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/mask_probe")], check=True,
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
    vectors = oracle.splitlines()
    differences = [{"index": i, "oracle": row, "observed": got}
                   for i, (row, want, got) in enumerate(zip(vectors, expected, actual)) if want != got]
    legacy_differences = [{"index": i, "oracle": row, "observed": got}
                          for i, (row, got) in enumerate(zip(vectors, actual))
                          if (int(row.split("\t")[13]), int(row.split("\t")[14])) != got[:2]]
    report = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "finite_lean_datapath_reference_comparison",
        "scope": "Long/double masks, all 16 lane-flag patterns in every cycle; write/flush/both/mask-register/directive/override; one PE, wide GRF destination; no hazard/port completeness",
        "programs": len(expected) // 4, "cases": len(expected),
        "cases_per_spelling": dict(sorted(Counter(row.split("\t")[1] for row in vectors).items())),
        "matched": len(expected) - len(differences), "differences": differences,
        "legacy_simulator_disagreements": legacy_differences,
        "vectors_sha256": sha(oracle.encode()), "vsm_sha256": sha(vsm.encode()),
        "reference_output_sha256": sha(raw.encode()), "sources": hashes,
        "proves_universal_conformance": False, "proves_isa_completeness": False, "proves_optimality": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_name("vectors.tsv").write_text(oracle)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cycles": len(expected), "matched": report["matched"], "differences": len(differences),
                      "legacy_simulator_disagreements": len(legacy_differences)}))
    if differences:
        print(json.dumps(differences[:8], indent=2))
        raise SystemExit("mask profile differs from reference")


if __name__ == "__main__":
    main()
