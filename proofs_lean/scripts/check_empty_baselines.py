"""Record empty-program judge observations for all 73 problems.

Neither a failed empty run nor this finite inventory is a formal lower bound.
Score-zero normalization, problem specifications and execution correspondence
remain separate proof obligations.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
sys.path.insert(0, str(REPO))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    from mncompile.bench.run import normalized_testcase
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    paths = json.loads((ROOT / "audit.json").read_text())["problems"]
    if len(paths) != 73:
        raise SystemExit("baseline inventory must cover all 73 problems")
    judge = REPO / "judge/judge-py/judge.py"
    tools = [judge, judge.parent / "mncore2_emuenv/assemble3", judge.parent / "mncore2_emuenv/gpfn3_package_main",
             REPO / "mncompile/bench/run.py", Path(__file__).resolve()]
    hashes = [{"path": p.relative_to(REPO).as_posix(), "sha256": sha(p)} for p in tools]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    frozen = args.output.parent / "empty.vsm"
    frozen.write_bytes(b"")
    rows = []
    with tempfile.TemporaryDirectory(prefix="mncore-empty-baseline-") as temporary:
        directory = Path(temporary)
        solution = directory / "empty.vsm"
        solution.write_bytes(b"")
        for index, entry in enumerate(paths):
            problem = REPO / entry["id"]
            testcases = sorted(problem.glob("testcase*.vsm"))
            if not testcases:
                raise SystemExit(f"missing testcase: {problem}")
            cases = []
            for testcase in testcases:
                normalized = normalized_testcase(testcase, directory)
                normalized_hash = sha(normalized)
                try:
                    result = subprocess.run([sys.executable, str(judge), str(normalized), str(solution)],
                                            capture_output=True, text=True, timeout=180,
                                            env={**os.environ, "OMP_THREAD_LIMIT": "1"})
                    raw = result.stdout + result.stderr
                    accepted = re.search(r"ACCEPTED!! score=(\d+)", raw)
                    stage = "accepted" if result.returncode == 0 and accepted else "rejected"
                    mismatch = re.search(r"\d+ value\(s\) correct, but \d+ value\(s\) mismatch", raw)
                    reason = "output_mismatch" if mismatch else "judge_or_execution_rejection" if stage == "rejected" else None
                    score = int(accepted[1]) if accepted else None
                    diagnostic = mismatch[0] if mismatch else raw[-1500:] if stage != "accepted" else ""
                    code = result.returncode
                except subprocess.TimeoutExpired as error:
                    stage, score, code, reason = "timeout", None, None, "unclassified_timeout"
                    raw = ((error.stdout or b"") + (error.stderr or b"")).decode(errors="replace")
                    diagnostic = raw[-1500:]
                cases.append({"path": testcase.relative_to(REPO).as_posix(), "sha256": sha(testcase),
                              "normalized_sha256": normalized_hash, "observed": stage, "score": score,
                              "returncode": code, "reason": reason, "diagnostic": diagnostic,
                              "output_sha256": hashlib.sha256(raw.encode()).hexdigest()})
            rows.append({"problem": entry["id"], "cases": cases,
                         "empty_accepted_on_all_testcases": all(c["observed"] == "accepted" for c in cases),
                         "contains_unclassified_timeout": any(c["observed"] == "timeout" for c in cases)})
            print(json.dumps({"index": index, "problem": entry["id"],
                              "outcomes": [c["observed"] for c in cases]}), flush=True)
    if any(sha(path) != item["sha256"] for path, item in zip(tools, hashes)):
        raise SystemExit("tools changed during baseline run; report not saved")
    record = {"schema_version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
              "evidence_kind": "official_testcase_empty_program_observation_not_formal_lower_bound",
              "mode": "default noto judge; debug get/set disabled; official normalization for older testcases",
              "program": "empty.vsm", "program_sha256": sha(frozen), "program_count": len(rows),
              "accepted_problems": sum(r["empty_accepted_on_all_testcases"] for r in rows),
              "problems": rows, "sources": hashes,
              "proves_all_input_correctness": False, "proves_positive_lower_bound": False,
              "proves_optimality": False}
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if any(row["contains_unclassified_timeout"] for row in rows):
        raise SystemExit("baseline contains timeouts; do not count them as counterexamples")


if __name__ == "__main__":
    main()
