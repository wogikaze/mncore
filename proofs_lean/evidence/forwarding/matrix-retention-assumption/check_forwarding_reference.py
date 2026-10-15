"""Separate assembly, success, recognized forwarding errors, and unknown failures."""
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
FORWARD = {"alu": "$aluf", "mau": "$mauf", "mread": "$mreadf", "lbf": "$lbf"}
SCENARIOS = {"valid", "nop", "noforward", "noforward-alu", "disabled-write", "disabled-discard",
             "disabled-mask-off", "disabled-narrow-off", "disabled-chain", "disabled-long-off",
             "disabled-flush-off", "disabled-register-off"}
SCENARIOS.add("disabled-register-focus")


def program(unit: str, scenario: str) -> tuple[str, bool]:
    if unit not in FORWARD or scenario not in SCENARIOS:
        raise ValueError("unknown forwarding fixture")
    lines = ["d set $lr0 8 " + "3FF00000000000000000000000000000" * 4,
             "d set $ls64n0c0b0m0p0 8 " + "112233445566778899AABBCCDDEEFF00" * 4]
    if scenario.startswith("disabled-register"):
        lines.extend(["d set $ls0 2 " + "0000000000000000" * 2, "lpassa $lls0 $omr1"])
    if scenario == "disabled-register-focus":
        lines.extend(["lpassa $l2bid $omr3", "lpassa $l1bid $omr3/$imr3", "lpassa $peid $omr3/$imr3"])
    if unit == "mread":
        lines.extend(["dmwrite $lr0v $lx0", "nop/2"])
    if unit == "lbf":
        lines.append("d set $lb0 64 " + "3FF0000000000000" * 64)
    producer = {"alu": 'immu ui"1072693248" $nowrite', "mau": "dvpassa $llr0v $nowrite",
                "mread": "dmread $lx0 $nowrite", "lbf": "l1bmm $lb0 $nowrite"}[unit]
    lines.append(producer)
    if scenario == "nop":
        lines.append("nop/3")
    elif scenario == "noforward":
        lines.append("noforward")
    elif scenario == "noforward-alu":
        lines.append('noforward; immu ui"1073741824" $nowrite')
    elif scenario.startswith("disabled"):
        lines.append("dvpassa $llr0v $nowrite" if unit == "alu" else "zero $nowrite")
    source = FORWARD[unit]
    dump = True
    if scenario == "disabled-discard":
        lines.append(f"lpassa {source} $nowrite")
        dump = False
    elif scenario == "disabled-chain":
        lines.extend([f"lpassa {source} $nowrite", "lpassa $aluf $lls64v"])
    elif scenario == "disabled-mask-off":
        lines.append(f"lpassa {source} $lls64v/ll0000")
    elif scenario == "disabled-narrow-off":
        lines.append(f"lpassa {source} $ls64v/0000")
    elif scenario == "disabled-long-off":
        lines.append(f"lpassa {source} $lls64v/0000p")
    elif scenario == "disabled-flush-off":
        lines.append(f"lpassa/ll0000 {source} $lls64v")
    elif scenario == "disabled-register-off":
        lines.append(f"lpassa {source} $omr1/0000")
        dump = False
    elif scenario == "disabled-register-focus":
        lines.append(f"lpassa {source} $omr1/$imr3")
        dump = False
    else:
        lines.append(f"lpassa {source} $lls64v")
    lines.append("nop/2")
    if dump:
        lines.append("d get $ls64n0c0b0m0p0 8")
    elif scenario.startswith("disabled-register"):
        lines.append("d get $omr1n0c0b0m0p0 1")
    return "\n".join(lines) + "\n", dump


def classify(returncode: int, output: str) -> str:
    if returncode == 0:
        return "ok"
    if "RuntimeError" in output and re.search(r"Accessing to .*forwarding register failed", output, re.I):
        return "failure"
    return "unclassified_runtime_error"


def check_values(output: str, high: int, low: int) -> bool:
    rows = [row for row in output.splitlines() if row.startswith("DEBUG-")]
    if len(rows) != 8:
        return False
    for i, row in enumerate(rows):
        match = re.fullmatch(rf"DEBUG-GREG1\(n0c0b0m0p0,{64+2*i}\):.*v:0x([0-9a-fA-F]+)\).*", row)
        if not match or int(match[1], 16) != (high if i % 2 == 0 else low):
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    sources = [ROOT / "ProofsLean/IntegerALU.lean", ROOT / "ProofsLean/Forwarding.lean",
               ROOT / "ForwardingProbe.lean", ROOT / "scripts/check_memory_reference.py",
               Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in sources]
    build = subprocess.run([lake, "build", "forwarding_probe"], cwd=ROOT, capture_output=True, text=True, timeout=300)
    if build.returncode:
        raise SystemExit(build.stdout + build.stderr)
    oracle = subprocess.run([str(ROOT / ".lake/build/bin/forwarding_probe")], check=True,
                            capture_output=True, text=True, timeout=60).stdout
    args.output.parent.mkdir(parents=True, exist_ok=True)
    program_dir = args.output.parent / "programs"
    program_dir.mkdir(exist_ok=True)
    records = []
    for index, row in enumerate(oracle.splitlines()):
        unit, scenario, expected, high, low = row.split("\t")
        if expected not in {"ok", "failure", "unknown"}:
            raise SystemExit("invalid semantic outcome")
        vsm, dump = program(unit, scenario)
        path = program_dir / f"{index:02d}-{unit}-{scenario}.vsm"
        path.write_text(vsm)
        assembly = subprocess.run([str(assembler), "--instruction-mode", "flat"], input=vsm,
                                  capture_output=True, text=True, timeout=60)
        stage, raw, code = "assembler_failure", assembly.stdout + assembly.stderr, assembly.returncode
        values_match = False
        if assembly.returncode == 0:
            try:
                run = subprocess.run([str(emulator), "--offchip-memory-init", "zero"], input=assembly.stdout,
                                     capture_output=True, text=True, timeout=180,
                                     env={**os.environ, "OMP_THREAD_LIMIT": "1"})
                code, raw = run.returncode, run.stdout + run.stderr
                stage = classify(code, raw)
                values_match = not dump or check_values(raw, int(high), int(low)) if stage == "ok" else True
                if stage == "ok" and scenario.startswith("disabled-register"):
                    flags = re.findall(r"DEBUG-OMR\(n0c0b0m0p0,1\):Mask\{([0-9]+)\}", raw)
                    values_match = flags == ["0"] * 4
            except subprocess.TimeoutExpired as error:
                stage, code = "timeout", None
                raw = (error.stdout or b"") + (error.stderr or b"")
                raw = raw.decode(errors="replace") if isinstance(raw, bytes) else raw
        unresolved = expected == "unknown"
        matched = not unresolved and stage == expected and values_match
        record = {"unit": unit, "scenario": scenario, "expected": expected, "observed": stage,
                  "assembler_accepted": assembly.returncode == 0, "returncode": code,
                  "values_checked": stage == "ok" and (dump or scenario.startswith("disabled-register")), "values_match": values_match,
                  "matched": matched, "unresolved": unresolved, "program": path.relative_to(args.output.parent).as_posix(),
                  "program_sha256": sha(vsm.encode()), "output_sha256": sha(raw.encode()),
                  "diagnostic": next((line[:1000] for line in raw.splitlines() if "forwarding register failed" in line), raw[-1000:]) if stage != "ok" else ""}
        records.append(record)
        print(json.dumps({"index": index, "unit": unit, "scenario": scenario, "observed": stage, "matched": matched, "unresolved": unresolved}), flush=True)
    if any(sha(p.read_bytes()) != item["sha256"] for p, item in zip(sources, hashes)):
        raise SystemExit("sources/tools changed during comparison; report not saved")
    report = {"schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
              "evidence_kind": "finite_forwarding_values_and_recognized_runtime_errors",
              "scope": "Explicit reference target for ALU/MAU/mread/L1-to-PE forwarding; ordinary mread retention observed; L1-to-PE absence unresolved; normal finite producer values, nop/noforward, discard/chain/write masks and flags-only writes; not full hazards or numerical poison",
              "cases": len(records), "matched": sum(row["matched"] for row in records),
              "unresolved": sum(row["unresolved"] for row in records),
              "cases_per_spelling": dict(sorted(Counter(row["unit"] for row in records).items())),
              "records": records, "vectors_sha256": sha(oracle.encode()), "sources": hashes,
              "proves_universal_conformance": False, "proves_isa_completeness": False, "proves_optimality": False}
    args.output.with_name("vectors.tsv").write_text(oracle)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if report["matched"] + report["unresolved"] != report["cases"]:
        raise SystemExit("forwarding abstraction has unresolved reference mismatches")


if __name__ == "__main__":
    main()
