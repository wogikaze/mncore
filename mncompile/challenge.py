"""Reproducible Challenge comparison; reference answers are evaluator-only.

uv run --with numpy python -m mncompile.challenge --assembler /path/assemble3
    --judge /path/judge.py --output /tmp/mncompile-challenge
"""

import argparse
import contextlib
import io
import json
import re
from pathlib import Path

from problems.run_problem import collect_testcases, run_judge

from .compiler import CompileError
from .frontend import compile_program
from .generators import GlobalTensor
from .maps import Tensor

ROOT = Path(__file__).resolve().parent.parent
SOURCES = Path(__file__).resolve().parent / "benchmarks/challenge"


def benchmark(
    *,
    assembler: str,
    judge: Path,
    output: Path,
    opt: str = "opt",
    only: set[str] | None = None,
) -> dict:
    bindings = json.loads((SOURCES / "bindings.json").read_text())
    audits = json.loads((SOURCES / "reference-audits.json").read_text())["audits"]
    rows = []
    directories = sorted(
        (ROOT / "problems/challenge").glob("[0-9]*.*"),
        key=lambda p: int(p.name.split(".")[0]),
    )
    for directory in directories:
        reference = json.loads((directory / "answer.json").read_text())
        slug = reference["problem_url"].rstrip("/").split("/")[-1]
        if only and slug not in only:
            continue
        row = {
            "slug": slug,
            "problem": directory.name,
            "public_shortest": reference["lines"],
            "reference_submission": reference["submission_url"],
            "status": "unsupported",
        }
        audit = audits.get(slug)
        excluded = bool(
            audit
            and audit["status"] == "counterexample"
            and audit["reference_submission"] == reference["submission_url"]
        )
        row["reference_eligible"] = not excluded
        if excluded:
            row["reference_exclusion"] = audit
        if slug == "plus_two":
            row.update(official_tutorial_lines=9, reference_is_testcase_dependent=True)
        source_path = SOURCES / f"{slug}.py"
        if slug not in bindings or not source_path.exists():
            row["reason"] = (
                "High-level source/layout or target lowering is not implemented yet"
            )
            rows.append(row)
            print(f"[unsupported] {slug}, target={reference['lines']}", flush=True)
            continue
        try:
            contract = bindings[slug]
            output_type = GlobalTensor if "group" in contract["output"] else Tensor
            arguments = {
                "inputs": {
                    name: Tensor(**spec) for name, spec in contract["inputs"].items()
                },
                "output": output_type(**contract["output"]),
                "opt": opt,
                "assembler": assembler,
            }
            compiled = compile_program(
                source_path.read_text(),
                row_partition=contract.get("row_partition", "local"),
                atol=contract.get("atol"),
                **arguments,
            )
            artifacts = output / slug
            compiled.write(artifacts)
            row.update(
                lines=compiled.report["lines"],
                source=str(source_path.relative_to(ROOT)),
                artifacts=str(artifacts),
                error_bound=compiled.report["error_bound"],
                preconditions=compiled.report["preconditions"],
                testcase_results=[],
            )
            for testcase in collect_testcases(directory):
                capture = io.StringIO()
                with (
                    contextlib.redirect_stdout(capture),
                    contextlib.redirect_stderr(capture),
                ):
                    code = run_judge(
                        judge.resolve(),
                        testcase,
                        (artifacts / "kernel.vsm").resolve(),
                        False,
                        False,
                    )
                message = capture.getvalue()
                score = re.search(r"ACCEPTED!! score=(\d+)", message)
                accepted = (
                    code == 0 and score is not None and int(score[1]) == row["lines"]
                )
                row["testcase_results"].append(
                    {
                        "testcase": testcase.name,
                        "accepted": accepted,
                        "score": int(score[1]) if score else None,
                    }
                )
                if not accepted:
                    (artifacts / "judge-error.log").write_text(message)
            row["status"] = (
                "accepted"
                if all(case["accepted"] for case in row["testcase_results"])
                and row["testcase_results"]
                else "failed"
            )
            row["meets_public_shortest"] = (
                row["status"] == "accepted" and row["lines"] <= row["public_shortest"]
            )
            row["meets_eligible_line_target"] = row["status"] == "accepted" and (
                excluded or row["lines"] <= row["public_shortest"]
            )
            if "official_tutorial_lines" in row:
                row["meets_official_tutorial"] = (
                    row["status"] == "accepted"
                    and row["lines"] <= row["official_tutorial_lines"]
                )
            print(
                f"[{row['status']}] {slug}: {row['lines']} lines, public={row['public_shortest']}",
                flush=True,
            )
        except (CompileError, OSError) as exc:
            row["status"], row["reason"] = "unsupported", str(exc)
            print(f"[unsupported] {slug}: {exc}", flush=True)
        rows.append(row)
    report = {
        "scope": "original Challenge",
        "formal_whole_domain_proof": False,
        "line_target_complete": len(rows) == 25
        and all(row.get("meets_eligible_line_target", False) for row in rows),
        "correctness_note": "Official fixtures and line targets alone do not establish whole-domain correctness; independent domain checks and numerical bounds are also required.",
        "total": len(rows),
        "accepted": sum(row["status"] == "accepted" for row in rows),
        "meets_public_shortest": sum(
            row.get("meets_public_shortest", False) for row in rows
        ),
        "meets_eligible_line_target": sum(
            row.get("meets_eligible_line_target", False) for row in rows
        ),
        "problems": rows,
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "progress.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        f"Accepted {report['accepted']}/{len(rows)}; meets public shortest {report['meets_public_shortest']}/{len(rows)}",
        flush=True,
    )
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assembler", required=True)
    parser.add_argument("--judge", required=True, type=Path)
    parser.add_argument("--opt", default="opt")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--only", help="Comma-separated problem slugs")
    args = parser.parse_args()
    benchmark(
        assembler=args.assembler,
        judge=args.judge,
        output=args.output,
        opt=args.opt,
        only=set(args.only.split(",")) if args.only else None,
    )


if __name__ == "__main__":
    main()
