"""Reproduce domain-valid counterexamples against evaluator-only references.

This module never participates in code generation. Passing a finite audit does
not prove validity; a failing audit suffices to exclude a shortest reference.
"""

import argparse
import json
import re
import struct
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def execute(assembler, emulator, program):
    assembled = subprocess.run(
        [assembler, "--instruction-mode", "flat"],
        input=program,
        text=True,
        capture_output=True,
        check=True,
    )
    result = subprocess.run(
        [emulator, "--offchip-memory-init", "zero"],
        input=assembled.stdout,
        text=True,
        capture_output=True,
        check=True,
    )
    return re.findall(r"DEBUG-LM1\([^\n]*\(0x([0-9a-fA-F]{16})\)", result.stderr)


def audit_references(assembler, emulator):
    cases = []
    cases.append(
        (
            "plus_two",
            "2.plus-two",
            "All twenty UInt64 inputs are zero (allowed 0..99).",
            "d set $lm0 20 " + "0" * 320 + "\n",
            20,
            [2] * 20,
            lambda bits: [int(word, 16) for word in bits],
        )
    )
    cases.append(
        (
            "fle",
            "8.fle",
            "All forty Float inputs are zero (allowed 0..5).",
            "d set $lm0 20 " + "0" * 320 + "\n",
            20,
            [0] * 40,
            lambda bits: [int(word[i : i + 8], 16) for word in bits for i in (0, 8)],
        )
    )
    matrix = [1.0] * 64
    matrix[8] = -0.0
    expected = [matrix[row * 8 + col] for col in range(8) for row in range(8)]
    payload = b"".join(struct.pack(">d", value) for value in matrix).hex()
    cases.append(
        (
            "transpose_addr",
            "9.transpose-addr",
            "All Double inputs are one except X[1,0]=-0.0 (numerically within 0..64).",
            "d set $lm0 64 " + payload + "\n",
            64,
            expected,
            lambda bits: [struct.unpack(">d", bytes.fromhex(word))[0] for word in bits],
        )
    )
    audits = {}
    for slug, directory, description, prefix, longs, expected, decode in cases:
        reference = ROOT / "problems/challenge" / directory
        suffix = f"nop\nnop\nd getd $ln0n0c0b0m0p0 {longs}\n"
        actual = decode(
            execute(
                assembler,
                emulator,
                prefix + (reference / "answer.vsm").read_text() + suffix,
            )
        )
        if len(actual) != len(expected):
            raise RuntimeError(f"Incomplete emulator output for {slug}: {len(actual)}")
        differences = [
            {"index": i, "expected": want, "actual": got}
            for i, (want, got) in enumerate(zip(expected, actual))
            if want != got
        ]
        metadata = json.loads((reference / "answer.json").read_text())
        audits[slug] = {
            "reference_submission": metadata["submission_url"],
            "reference_lines": metadata["lines"],
            "eligible": not differences,
            "status": "counterexample"
            if differences
            else "no_counterexample_in_this_audit",
            "description": description,
            "input_debug_vsm": prefix,
            "output_debug_vsm": suffix,
            "differences": differences,
            "reason": "Domain-valid input produces an incorrect output"
            if differences
            else "Finite audit is not a proof",
        }
    return {
        "schema_version": 1,
        "policy": "Exclude only references with reproduced domain-valid counterexamples; retain correctness as a separate obligation.",
        "reproduce": "python -m mncompile.reference_audits --assembler PATH --emulator PATH --output PATH",
        "audits": audits,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assembler", required=True)
    parser.add_argument("--emulator", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = audit_references(args.assembler, args.emulator)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for slug, audit in report["audits"].items():
        print(slug, audit["status"], len(audit["differences"]))


if __name__ == "__main__":
    main()
