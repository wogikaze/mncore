#!/usr/bin/env python3
"""Authoritative FizzBuzz gate: the official judge (judge.py via run_problem.py).

    python3 tools/fbverify.py candidate.vsm [more.vsm ...] [--quiet]

Prints the judge's own verdict line (`ACCEPTED!! score=<words> j=<n> m=<n>`)
or the failure. This is the only gate that counts for a claim.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBLEM = "challenge/20.fizzbuzz"
VERDICT = re.compile(r"(ACCEPTED!!.*|Wrong Answer.*|.*\berror\b.*)")


def verify(candidate: Path) -> tuple[bool, str]:
    run = subprocess.run(
        [sys.executable, str(ROOT / "problems/run_problem.py"), PROBLEM,
         "--solution", str(candidate)],
        capture_output=True, text=True, cwd=ROOT,
    )
    output = run.stdout + run.stderr
    match = VERDICT.search(output)
    if "ACCEPTED!!" in output:
        return True, match.group(1).strip() if match else "ACCEPTED"
    detail = match.group(1).strip() if match else output.strip().splitlines()[-1:] or ["no verdict"]
    return False, detail if isinstance(detail, str) else " ".join(detail)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", nargs="+")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv[1:])
    worst = 0
    for name in args.candidate:
        ok, detail = verify(Path(name))
        worst = max(worst, 0 if ok else 1)
        if not args.quiet:
            print(f"{name}: {detail}")
    return worst


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
