#!/usr/bin/env python3
"""Cross-check the 3-line Convert Endian answer on deterministic 64-bit inputs."""

from __future__ import annotations

import random
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
CORE = REPO / "viz" / "core"
JUDGE = REPO / "judge" / "judge-py"
ANSWER = REPO / "problems" / "challenge" / "12.convert-endian" / "answer.vsm"


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr


def byte_swap(value: int) -> int:
    return int.from_bytes(value.to_bytes(8, "little"), "big")


def main() -> None:
    parser = __import__("argparse").ArgumentParser()
    parser.add_argument("--seed", type=int, default=0xC0FFEE)
    parser.add_argument("--words-per-pe", type=int, default=2)
    args = parser.parse_args()
    if args.words_per_pe < 1 or args.words_per_pe > 2:
        raise SystemExit("--words-per-pe must be in 1..2 for this four-PE testcase layout")

    rng = random.Random(args.seed)
    vectors = [[rng.getrandbits(64) for _ in range(args.words_per_pe)] for _ in range(4)]
    edge_words = [0x5FE1DC66CBEA3DB3, 0, 0xFFFFFFFFFFFFFFFF, 0x0123456789ABCDEF]
    for pe, value in enumerate(edge_words):
        vectors[pe][0] = value

    input_lines = [f"# ======= In(0): ((4_PE:{args.words_per_pe}))@LM0 / ULong ======="]
    output_lines = [f"# ======= Out(0): ((4_PE:{args.words_per_pe}))@LM1 / ULong ======="]
    raw_inputs: list[str] = []
    raw_outputs: list[str] = []
    for pe, words in enumerate(vectors):
        for index, value in enumerate(words):
            address = index * 2
            coordinate = f"@[{pe},{index}]"
            input_lines.append(
                f"d set $lm{address}p{pe} 1 {value:016X} "
                f"# values=[{value}] / ULong {coordinate}"
            )
            raw_inputs.append(f"d set $lm{address}p{pe} 1 {value:016X}")
            swapped = byte_swap(value)
            output_lines.append(
                f"d getd $ln{address}n0c0b0m0p{pe} 1 "
                f"# expect=[{swapped}] / ULong {coordinate}"
            )
            raw_outputs.append(f"d getd $ln{address}n0c0b0m0p{pe} 1")

    solution = ANSWER.read_text(encoding="utf-8")
    bare_vsm = "\n".join(raw_inputs) + "\n"
    bare_vsm += "\n" + "\n".join(
        line for line in solution.splitlines() if line.strip() and not line.lstrip().startswith("#")
    ) + "\n\n"
    bare_vsm += "\n".join(raw_outputs) + "\n"

    testcase = "\n".join(input_lines)
    testcase += "\n# ======= YOUR VSM WILL BE INSERTED HERE =======\n"
    testcase += "# ======= Output =======\n" + "\n".join(output_lines) + "\n"

    with tempfile.TemporaryDirectory(prefix="mncore-convert-endian-") as temp_dir:
        temp = Path(temp_dir)
        testcase_path = temp / "testcase.vsm"
        vsm_path = temp / "convert-endian.vsm"
        testcase_path.write_text(testcase, encoding="utf-8")
        vsm_path.write_text(bare_vsm, encoding="utf-8")
        judge_output = run(["python3", "judge.py", str(testcase_path), str(ANSWER)], JUDGE)
        sim_output = run(["cargo", "run", "--release", "--bin", "difftest_file", "--",
                          str(vsm_path)], CORE)

    judge_summary = next(line for line in judge_output.splitlines() if "ACCEPTED!!" in line)
    sim_summary = next(line for line in sim_output.splitlines() if "mismatches" in line)
    print(judge_summary.strip())
    print(sim_summary.strip())
    print(f"seed={args.seed}, values={4 * args.words_per_pe}")


if __name__ == "__main__":
    main()
