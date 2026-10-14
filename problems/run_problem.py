#!/usr/bin/env python3
"""Helper script for running MN-Core Challenge testcases locally."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import List

REPO_ROOT = Path(__file__).resolve().parent.parent
PROBLEMS_ROOT = REPO_ROOT / "problems"
DEFAULT_SOLUTION_NAME = "solution.vsm"
DEFAULT_JUDGE = REPO_ROOT / "judge" / "judge-py" / "judge.py"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the MN-Core judge against one or more testcases stored under"
            " problems/<name>/."
        )
    )
    parser.add_argument(
        "problem",
        help=(
            "Problem name or path. If a relative path is given, it is resolved"
            " from the problems/ directory."
        ),
    )
    parser.add_argument(
        "--solution",
        "-s",
        type=str,
        default=None,
        help=(
            "Path to your solution VSM file. Defaults to problems/<name>/"
            f"{DEFAULT_SOLUTION_NAME}."
        ),
    )
    parser.add_argument(
        "--judge",
        "-j",
        type=str,
        default=str(DEFAULT_JUDGE),
        help="Path to judge.py (run setup_judge.sh once if it is missing).",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Also show inputs / expect / actual matrix sections (asm and result are always shown).",
    )
    parser.add_argument(
        "--keep-going",
        action="store_true",
        help="Run all testcases even if one fails.",
    )
    parser.add_argument(
        "--raw-judge-output",
        action="store_true",
        help="Do not filter judge stderr sections; print raw output from judge.py.",
    )
    return parser.parse_args()


def resolve_problem_dir(raw: str) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = PROBLEMS_ROOT / path
    return path.resolve()


def collect_testcases(problem_dir: Path) -> List[Path]:
    patterns = ["testcase.vsm", "testcase" + "*.vsm"]
    testcases: List[Path] = []
    for pattern in patterns:
        testcases.extend(problem_dir.glob(pattern))
    unique = sorted({tc.resolve() for tc in testcases})
    return unique


def ensure_paths(
    problem_dir: Path, solution_path: Path, judge_path: Path
) -> List[Path]:
    if not problem_dir.exists():
        sys.exit(f"Problem directory not found: {problem_dir}")

    if not problem_dir.is_dir():
        sys.exit(f"Problem path is not a directory: {problem_dir}")

    if not solution_path.exists():
        sys.exit(
            "Solution VSM file not found: "
            f"{solution_path}. Provide --solution if you store it elsewhere."
        )

    if not judge_path.exists():
        sys.exit(
            "judge.py not found. Run setup_judge.sh once to download the official"
            " judge assets. Expected path: "
            f"{judge_path}"
        )

    testcases = collect_testcases(problem_dir)
    if not testcases:
        sys.exit(
            "No testcase*.vsm files found under the problem directory."
            " Place the official testcase there first."
        )
    return testcases


# Sections produced by judge.py -v that are always hidden (too large).
_ALWAYS_SKIP: set[str] = {"vsm", "emu"}
# Sections hidden unless --verbose / -v is passed to this script.
_VERBOSE_ONLY: set[str] = {"inputs", "expect", "actual"}


def _filter_judge_stderr(raw: str, verbose: bool) -> str:
    """Split judge stderr into labelled sections and drop noisy ones."""
    import re

    header_re = re.compile(r"^-{3,}\s+(.+?)\s+-{3,}$")
    sections: list[tuple[str | None, list[str]]] = []
    current_label: str | None = None
    current_lines: list[str] = []

    for line in raw.splitlines():
        m = header_re.match(line)
        if m:
            sections.append((current_label, current_lines))
            current_label = m.group(1).strip()
            current_lines = []
        else:
            current_lines.append(line)

    sections.append((current_label, current_lines))

    out_parts: list[str] = []
    for label, lines in sections:
        if label is None:
            chunk = "\n".join(lines).strip()
            if chunk:
                out_parts.append(chunk)
            continue
        if label in _ALWAYS_SKIP:
            out_parts.append(f"[--- {label}: {len(lines)} lines hidden ---]")
            continue
        if not verbose and label in _VERBOSE_ONLY:
            continue
        header = f"------------------- {label} --------------------"
        body = "\n".join(lines).strip()
        out_parts.append(header if not body else header + "\n" + body)

    return "\n".join(out_parts)


def run_judge(
    judge_path: Path,
    testcase: Path,
    solution: Path,
    verbose: bool,
    raw_judge_output: bool,
) -> int:
    # Always run with -v so we can capture structured output; we filter it ourselves.
    cmd = ["python3", str(judge_path), str(testcase), str(solution), "-v"]

    print(f"\n🚀  Running {testcase.name} against {solution.name}...")
    print("    » python3 judge.py " + testcase.name + " " + solution.name +
          (" -v" if verbose else ""))

    # Original Challenge testcases predate the explicit Output separator that
    # the downloadable judge expects. Adapt only the temporary input copy.
    testcase_body = testcase.read_text(encoding="utf-8")
    output_marker = "# ======= Output ======="
    insertion_marker = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
    with tempfile.TemporaryDirectory(prefix="mncore-testcase-") as temporary:
        if output_marker not in testcase_body and insertion_marker in testcase_body:
            prefix, suffix = testcase_body.split(insertion_marker, 1)
            suffix, count = re.subn(
                r"(?m)^(# ======= Out\(0\):.*)$",
                lambda match: output_marker + "\n" + match[1],
                suffix,
                count=1,
            )
            if count:
                adapted = Path(temporary) / testcase.name
                adapted.write_text(prefix + insertion_marker + suffix, encoding="utf-8")
                cmd[2] = str(adapted)
        proc = subprocess.run(cmd, capture_output=True, text=True)

    if raw_judge_output:
        if proc.stderr.strip():
            print(proc.stderr, file=sys.stderr, end="")
    else:
        filtered_stderr = _filter_judge_stderr(proc.stderr, verbose)
        if filtered_stderr.strip():
            print(filtered_stderr, file=sys.stderr)
    if proc.stdout.strip():
        print(proc.stdout)

    return proc.returncode


def main() -> None:
    args = parse_args()
    problem_dir = resolve_problem_dir(args.problem)

    solution_path = (
        Path(args.solution).resolve()
        if args.solution
        else (problem_dir / DEFAULT_SOLUTION_NAME).resolve()
    )
    judge_path = Path(args.judge).resolve()

    testcases = ensure_paths(problem_dir, solution_path, judge_path)

    failed = []
    for testcase in testcases:
        code = run_judge(
            judge_path,
            testcase,
            solution_path,
            args.verbose,
            args.raw_judge_output,
        )
        if code != 0:
            failed.append((testcase, code))
            if not args.keep_going:
                break

    if failed:
        print("\n❌  Judge failed for the following testcases:")
        for tc, code in failed:
            print(f"  - {tc.name} (exit code {code})")
        sys.exit(failed[0][1])

    print("\n✅  All testcases passed!")


if __name__ == "__main__":
    main()
