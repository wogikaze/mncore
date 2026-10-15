"""Observe LBF using unchanged assembler-generated instruction fragments.

This is an encoded-stream experiment. It does not certify rejected whole VSM
sources as legal or establish an ISA decoder/conformance proof.
"""
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

from check_forwarding_reference import check_values, classify, program
from check_memory_reference import sha

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def pe_words(assembly: str) -> list[str]:
    words = []
    for line in assembly.splitlines():
        if line.startswith("m "):
            raise ValueError("MV fragments are outside this experiment")
        if line.startswith("j "):
            if not re.fullmatch(r"j [01]{426}", line):
                raise ValueError("unexpected encoded PE word format")
            words.append(line)
    return words


def splice(template: str, driver: str) -> str:
    pe_words(template)
    pe_words(driver)
    lines = template.splitlines()
    positions = [i for i, line in enumerate(lines) if line.startswith("j ")]
    if len(positions) < 2:
        raise ValueError("template lacks producer and consumer")
    # The first scored word is the L1BM producer; all earlier lines are debug input.
    insert = positions[0] + 1
    return "\n".join(lines[:insert] + driver.splitlines() + lines[insert:]) + "\n"


def sources(scenario: str) -> tuple[str, str, str, bool]:
    original = {"disabled-write", "disabled-discard", "disabled-mask-off", "disabled-narrow-off", "disabled-chain"}
    if scenario in original:
        full, dump = program("lbf", scenario)
        if full.count("\nzero $nowrite\n") != 1:
            raise ValueError("unexpected disabled-producer recipe")
        template = full.replace("\nzero $nowrite\n", "\n", 1)
        driver = "zero $nowrite\n"
    else:
        template, dump = program("lbf", "valid")
        drivers = {
            "after-alu-imm": 'immu ui"1073741824" $nowrite\n',
            "after-mau": "dvpassa $lls0v $nowrite\n",
            "after-two-ordinary": 'zero $nowrite\nimmu ui"1073741824" $nowrite\n',
            "producer-new": "d set $lb0 64 " + "4000000000000000" * 64 + "\nl1bmm $lb0 $nowrite\n",
            "noforward-producer-new": "d set $lb0 64 " + "4000000000000000" * 64 + "\nnoforward; l1bmm $lb0 $nowrite\n",
            "nop": "nop/3\n",
        }
        driver = drivers[scenario]
    # A distinct MAU value makes a shared/aliased forwarding path observable.
    template = "d set $ls0 8 " + "40000000000000000000000000000000" * 4 + "\n" + template
    lines = template.splitlines()
    producer = lines.index("l1bmm $lb0 $nowrite")
    full = "\n".join(lines[:producer+1] + driver.splitlines() + lines[producer+1:]) + "\n"
    return template, driver, full, dump


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    tools = REPO / "judge/judge-py/mncore2_emuenv"
    assembler, emulator = tools / "assemble3", tools / "gpfn3_package_main"
    source_paths = [ROOT / "ProofsLean/EncodedForwarding.lean", ROOT / "ProofsLean/Forwarding.lean",
                    ROOT / "ProofsLean/IntegerALU.lean", ROOT / "lean-toolchain",
                    ROOT / "LBFEncodedProbe.lean", ROOT / "scripts/check_forwarding_reference.py",
                    ROOT / "scripts/check_memory_reference.py", Path(__file__).resolve(), assembler, emulator]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p.read_bytes())} for p in source_paths]
    build = subprocess.run([lake, "build", "lbf_encoded_probe"], cwd=ROOT, capture_output=True, text=True, timeout=300)
    if build.returncode:
        raise SystemExit(build.stdout + build.stderr)
    vectors = subprocess.run([str(ROOT / ".lake/build/bin/lbf_encoded_probe")], check=True,
                             capture_output=True, text=True, timeout=60).stdout
    args.output.parent.mkdir(parents=True, exist_ok=True)
    records = []
    for index, vector in enumerate(vectors.splitlines()):
        unit, scenario, expected, high, low = vector.split("\t")
        if unit != "lbf" or expected != "ok":
            raise SystemExit("only known LBF value experiments are supported")
        directory = args.output.parent / f"{index:02d}-{scenario}"
        directory.mkdir(exist_ok=True)
        template, driver, full, dump = sources(scenario)
        artifacts = {}
        for name, text in [("template.vsm", template), ("driver.vsm", driver), ("intended.vsm", full)]:
            (directory / name).write_text(text)
            artifacts[name] = sha(text.encode())
        assemblies = {}
        for name, text in [("template", template), ("driver", driver), ("full", full)]:
            result = subprocess.run([str(assembler), "--instruction-mode", "flat"], input=text,
                                    capture_output=True, text=True, timeout=60)
            assemblies[name] = result
            for suffix, data in [("asm", result.stdout), ("stderr.txt", result.stderr)]:
                filename = f"{name}.{suffix}"
                (directory / filename).write_text(data)
                artifacts[filename] = sha(data.encode())
        if assemblies["template"].returncode or assemblies["driver"].returncode:
            raise SystemExit("an instruction fragment was not accepted")
        encoded = splice(assemblies["template"].stdout, assemblies["driver"].stdout)
        (directory / "encoded.asm").write_text(encoded)
        artifacts["encoded.asm"] = sha(encoded.encode())
        observed_words = pe_words(assemblies["full"].stdout)
        encoded_words = pe_words(encoded)
        prefix_identical = bool(observed_words) and encoded_words[:len(observed_words)] == observed_words
        if assemblies["full"].returncode == 0:
            prefix_identical = prefix_identical and len(encoded_words) == len(observed_words)
        stage, code, raw = "timeout", None, ""
        try:
            run = subprocess.run([str(emulator), "--offchip-memory-init", "zero"], input=encoded,
                                 capture_output=True, text=True, timeout=180,
                                 env={**os.environ, "OMP_THREAD_LIMIT": "1"})
            code, raw = run.returncode, run.stdout + run.stderr
            stage = classify(code, raw)
        except subprocess.TimeoutExpired as error:
            raw = ((error.stdout or b"") + (error.stderr or b"")).decode(errors="replace")
        values_match = stage == "ok" and (not dump or check_values(raw, int(high), int(low)))
        matched = stage == expected and values_match and prefix_identical
        record = {"unit": unit, "scenario": scenario, "expected": expected, "observed": stage,
                  "returncode": code, "matched": matched, "values_checked": dump, "values_match": values_match,
                  "directory": directory.relative_to(args.output.parent).as_posix(), "artifacts": artifacts,
                  "fragment_assembly_accepted": True, "full_vsm_accepted": assemblies["full"].returncode == 0,
                  "full_assembler_returncode": assemblies["full"].returncode,
                  "full_prefix_words_identical": prefix_identical, "full_emitted_words": len(observed_words),
                  "encoded_words": len(encoded_words), "output_sha256": sha(raw.encode()),
                  "diagnostic": raw[-1000:] if stage != "ok" else ""}
        records.append(record)
        print(json.dumps({"index": index, "scenario": scenario, "matched": matched,
                          "full_vsm_accepted": record["full_vsm_accepted"], "observed": stage}), flush=True)
    if any(sha(p.read_bytes()) != item["sha256"] for p, item in zip(source_paths, hashes)):
        raise SystemExit("sources/tools changed during comparison; report not saved")
    report = {"schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
              "evidence_kind": "unchanged_encoded_fragment_execution_not_vsm_legality_proof",
              "scope": "LBF retention/replacement across ordinary ALU/MAU/nop/noforward steps; unchanged 426-bit assembler-generated words; same emitted prefix as whole-source assembly; one observed PE/four cycles",
              "cases": len(records), "matched": sum(row["matched"] for row in records), "records": records,
              "vectors_sha256": sha(vectors.encode()), "sources": hashes,
              "whole_vsm_legality_proven": False, "decoder_correspondence_proven": False,
              "proves_universal_conformance": False, "proves_isa_completeness": False, "proves_optimality": False}
    args.output.with_name("vectors.tsv").write_text(vectors)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if report["matched"] != report["cases"]:
        raise SystemExit("encoded LBF comparison has unresolved mismatches")


if __name__ == "__main__":
    main()
