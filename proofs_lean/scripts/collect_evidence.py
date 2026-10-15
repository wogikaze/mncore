"""Record reproducible official-judge evidence; never turn it into an optimality claim."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
sys.path.insert(0, str(REPO))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    from mncompile.bench.run import judge
    from mncompile.sim import EMU_DIR

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", type=Path, required=True)
    parser.add_argument("--solution", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--claimed-bound", type=int)
    args = parser.parse_args()
    cases = sorted(args.problem.glob("testcase*.vsm"))
    if not cases:
        parser.error("no official testcases found")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    frozen = args.output.parent / "solution.vsm"
    if args.solution.resolve() != frozen.resolve():
        shutil.copyfile(args.solution, frozen)
    rows = []
    with tempfile.TemporaryDirectory() as directory:
        solution = Path(directory) / "solution.vsm"
        shutil.copyfile(frozen, solution)
        for case in cases:
            verdict = judge(case.resolve(), solution)
            relative = case.resolve().relative_to(REPO).as_posix()
            rows.append({"path": relative, "sha256": sha(case), "judge": verdict})
    record = {
        "schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "official_testcase_execution_not_formal_optimality",
        "problem": args.problem.as_posix(),
        "solution": "solution.vsm", "solution_sha256": sha(frozen),
        "tools": [{"path": str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path),
                   "sha256": sha(path)}
                  for path in (REPO / "judge/judge-py/judge.py", EMU_DIR / "assemble3", EMU_DIR / "gpfn3_package_main")],
        "cases": rows, "claimed_testcase_bound": args.claimed_bound,
        "contradicts_claimed_testcase_bound": bool(rows) and args.claimed_bound is not None and
            all(r["judge"]["accepted"] and r["judge"]["score"] < args.claimed_bound for r in rows),
        "proves_all_input_correctness": False, "proves_optimality": False,
    }
    args.output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"accepted": all(r["judge"]["accepted"] for r in rows),
                      "scores": [r["judge"]["score"] for r in rows],
                      "refutes_testcase_bound": record["contradicts_claimed_testcase_bound"]}))
    if args.claimed_bound is not None and not record["contradicts_claimed_testcase_bound"]:
        raise SystemExit("the alleged testcase counterexample was not reproduced")


if __name__ == "__main__":
    main()
