"""Benchmark: compile every problem, judge with the official judge, compare line counts.

    python -m mncompile.bench.run --output mncompile/benchmarks/results [--only 1.plus-one,...]

Only this harness reads problem statements, testcases and reference answers.
The compiler receives the kernel source and the tensor contract.
"""

from __future__ import annotations

import argparse
import json
import signal
import os
import re
import subprocess
import sys
import time
import traceback
from pathlib import Path

from . import problems as P
from ..memlimit import default_jobs, lift_for_child, limit_process, total_memory

ROOT = P.ROOT
JUDGE = ROOT / "judge" / "judge-py" / "judge.py"


def reference_lines(problem) -> int | None:
    if problem.reference.get("lines"):
        return int(problem.reference["lines"])
    m = re.search(r"Top:\s*(\d+)\s*lines", problem.statement)
    return int(m[1]) if m else None


HERE = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
OUTPUT = "# ======= Output ======="


def normalized_testcase(testcase: Path, workdir: Path) -> Path:
    """Older testcases have no Output marker; the current judge needs one (empty suffix)."""
    text = testcase.read_text()
    if OUTPUT in text:
        return testcase
    fixed = workdir / f"normalized-{testcase.name}"
    fixed.write_text(text.replace(HERE + "\n", HERE + "\n" + OUTPUT + "\n", 1))
    return fixed


def judge(testcase: Path, solution: Path) -> dict:
    testcase = normalized_testcase(testcase, solution.parent)
    p = subprocess.run([sys.executable, str(JUDGE), str(testcase), str(solution)], capture_output=True, text=True,
                       preexec_fn=lift_for_child)
    text = p.stdout + p.stderr
    m = re.search(r"ACCEPTED!! score=(\d+)", text)
    mismatch = re.search(r"(\d+) value\(s\) correct, but (\d+) value\(s\) mismatch", text)
    return {
        "testcase": testcase.name.replace("normalized-", ""),
        "accepted": p.returncode == 0 and m is not None,
        "score": int(m[1]) if m else None,
        "detail": None if m else (mismatch[0] if mismatch else text.strip().splitlines()[-1:] if text.strip() else ""),
    }


def run_one(problem_dir: str, output: str, backend: str, mem_fraction: float = 0.2) -> dict:
    from ..compiler import compile_program
    from ..errors import CompileError

    # a runaway candidate raises MemoryError in this worker instead of exhausting the machine
    limit_process(mem_fraction)

    problem = P.load(Path(problem_dir))
    out_dir = Path(output) / problem.name
    out_dir.mkdir(parents=True, exist_ok=True)
    log_lines = []
    row = {
        "problem": problem.name,
        "slug": problem.slug,
        "reference_lines": reference_lines(problem),
        "status": "failed",
    }
    t0 = time.time()
    try:
        compiled = compile_program(
            P.kernel_source(problem),
            P.contract_for(problem),
            backend=backend,
            log=lambda m: log_lines.append(m),
        )
        compiled.write(out_dir)
        row["lines"] = compiled.lines
        row["strategy"] = compiled.report.get("strategy")
        row["judge"] = [judge(tc, out_dir / "kernel.vsm") for tc in problem.testcases]
        ok = all(j["accepted"] and j["score"] == compiled.lines for j in row["judge"]) and row["judge"]
        row["status"] = "accepted" if ok else "rejected"
    except CompileError as exc:
        row["status"] = "unsupported"
        row["reason"] = str(exc)[:2000]
    except MemoryError:
        row["status"] = "crash"
        row["reason"] = "out of the per-worker memory limit"
    except Exception as exc:  # noqa: BLE001 - report harness/compiler crashes per problem
        row["status"] = "crash"
        row["reason"] = f"{type(exc).__name__}: {exc}"[:2000]
        log_lines.append(traceback.format_exc())
    row["seconds"] = round(time.time() - t0, 1)
    (out_dir / "compile.log").write_text("\n".join(log_lines) + "\n")
    return row


def _available_memory() -> int:
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) * 1024
    return 1 << 62


def _group_rss(pgid: int) -> int:
    """Resident memory of every process in a process group (the worker and its simulators)."""
    total = 0
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            if os.getpgid(int(d)) != pgid:
                continue
            with open(f"/proc/{d}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):
                        total += int(line.split()[1]) * 1024
        except (OSError, ProcessLookupError):
            continue
    return total


def _launch(problem, output, backend, mem_fraction):
    row_path = Path(output) / problem.name / "row.json"
    row_path.parent.mkdir(parents=True, exist_ok=True)
    if row_path.exists():
        row_path.unlink()
    cmd = [sys.executable, "-m", "mncompile.bench.run", "--worker", str(problem.directory),
           "--output", str(output), "--backend", backend, "--memory-fraction", str(mem_fraction)]
    proc = subprocess.Popen(cmd, start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                            env={**os.environ, "PYTHONPATH": str(ROOT)})
    return proc, row_path


def run_all(probs, output, backend, jobs, log=print):
    """Compile and judge every problem in worker processes, watching the machine's free memory:
    when it runs low the largest worker group is killed and its problem rerun alone at the end
    (an out-of-memory machine takes the whole WSL VM down)."""
    reserve = max(int(total_memory() * 0.12), 1 << 30)
    queue = list(probs)
    solo = []
    running = {}  # pid -> (proc, problem, row path, solo)
    rows = []

    def finish(pid, killed=False):
        proc, problem, row_path, alone = running.pop(pid)
        if killed:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
            if not alone:
                solo.append(problem)
                log(f"[requeued   ] {problem.name:40s} (memory low; rerun alone)")
                return
        try:
            row = json.loads(row_path.read_text())
        except (OSError, ValueError):
            row = {"problem": problem.name, "slug": problem.slug, "reference_lines": reference_lines(problem),
                   "status": "crash", "reason": "killed (memory)" if killed else f"worker exited with {proc.returncode}", "seconds": None}
        rows.append(row)
        log(f"[{row['status']:11s}] {row['problem']:40s} lines={row.get('lines')} ref={row.get('reference_lines')} {row.get('seconds')}s {row.get('reason', '')[:120]}")

    while queue or solo or running:
        limit = jobs if queue else 1
        if not queue and solo and not running:
            problem = solo.pop(0)
            proc, row_path = _launch(problem, output, backend, 0.8)
            running[proc.pid] = (proc, problem, row_path, True)
        while queue and len(running) < limit:
            problem = queue.pop(0)
            proc, row_path = _launch(problem, output, backend, 0.6)
            running[proc.pid] = (proc, problem, row_path, False)
        time.sleep(0.5)
        for pid, (proc, *_rest) in list(running.items()):
            if proc.poll() is not None:
                finish(pid)
        if running and _available_memory() < reserve:
            pid = max(running, key=lambda q: _group_rss(running[q][0].pid))
            finish(pid, killed=True)
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, default=ROOT / "mncompile" / "benchmarks" / "results")
    ap.add_argument("--only", default="")
    ap.add_argument("--set", choices=["all", "challenge", "mnist"], default="all")
    ap.add_argument("--jobs", type=int, default=default_jobs(), help="parallel compiles (default: what fits in memory)")
    ap.add_argument("--backend", default="native")
    ap.add_argument("--worker", help=argparse.SUPPRESS)
    ap.add_argument("--memory-fraction", type=float, default=0.6, help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.worker:
        row = run_one(args.worker, str(args.output), args.backend, args.memory_fraction)
        (args.output / Path(args.worker).name / "row.json").write_text(json.dumps(row) + "\n")
        return
    probs = []
    if args.set in ("all", "challenge"):
        probs += P.challenge_problems()
    if args.set in ("all", "mnist"):
        probs += P.mnist_problems()
    only = {x for x in args.only.split(",") if x}
    if only:
        probs = [p for p in probs if p.name in only or p.slug in only]
    args.output.mkdir(parents=True, exist_ok=True)
    rows = run_all(probs, args.output, args.backend, args.jobs, log=lambda m: print(m, flush=True))
    order = {p.name: i for i, p in enumerate(probs)}
    rows.sort(key=lambda r: order[r["problem"]])
    path = args.output / "progress.json"
    previous = json.loads(path.read_text()) if path.exists() and only else None
    if previous:
        merged = {r["problem"]: r for r in previous["problems"]}
        merged.update({r["problem"]: r for r in rows})
        rows = list(merged.values())
    summary = {
        "total": len(rows),
        "accepted": sum(r["status"] == "accepted" for r in rows),
        "at_or_below_reference": sum(r["status"] == "accepted" and r.get("reference_lines") and r["lines"] <= r["reference_lines"] for r in rows),
        "problems": rows,
    }
    path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"accepted {summary['accepted']}/{summary['total']}, at or below reference {summary['at_or_below_reference']}")


if __name__ == "__main__":
    main()
