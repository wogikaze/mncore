"""Run the Welcome answer with the official assembler and emulator.

This checks the checked-in testcase only. It does not establish universal
correctness or full-ISA optimality.
"""
from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
PROBLEM = REPO / "problems/challenge/1.plus-one"
TOOLS = REPO / "judge/judge-py/mncore2_emuenv"


def main() -> None:
    testcase = (PROBLEM / "testcase.vsm").read_text().splitlines()
    inputs = [line for line in testcase if line.strip().startswith("d set ")]
    outputs = [line for line in testcase if line.strip().startswith("d get")]
    answer = (PROBLEM / "answer.vsm").read_text().splitlines()
    if len(inputs) != 8 or len(outputs) != 8 or len(answer) != 2:
        raise SystemExit("unexpected Welcome testcase or answer shape")

    expected: list[tuple[int, int, int]] = []
    for line in outputs:
        match = re.search(r"\$ln(\d+)n0c0b0m0p0.*expect=\[(\d+), (\d+)\]", line)
        if match is None:
            raise SystemExit(f"cannot read expected output from testcase: {line}")
        expected.append((int(match[1]), int(match[2]), int(match[3])))

    program = "\n".join(inputs + answer + outputs) + "\n"
    assembled = subprocess.run(
        [str(TOOLS / "assemble3"), "--instruction-mode", "flat"],
        input=program, capture_output=True, text=True, check=True, timeout=60,
    )
    run = subprocess.run(
        [str(TOOLS / "gpfn3_package_main"), "--offchip-memory-init", "zero"],
        input=assembled.stdout, capture_output=True, text=True, check=True,
        timeout=180, env={**os.environ, "OMP_THREAD_LIMIT": "1"},
    )
    actual: list[tuple[int, int, int]] = []
    for line in (run.stdout + run.stderr).splitlines():
        match = re.fullmatch(
            r"DEBUG-LM1\(n0c0b0m0p0,(\d+)\):\(0\) \(0x([0-9a-fA-F]{16})\).*",
            line,
        )
        if match is not None:
            packed = int(match[2], 16)
            actual.append((int(match[1]), packed >> 32, packed & 0xFFFFFFFF))
    if actual != expected:
        raise SystemExit(f"Welcome emulator mismatch\nexpected={expected}\nactual={actual}")
    print(f"PASS: official emulator matched all {len(actual) * 2} Welcome output words")


if __name__ == "__main__":
    main()
