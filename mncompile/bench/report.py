"""Markdown results table from a benchmark progress.json (inserted into mncompile/README.md).

    python -m mncompile.bench.report <dir with progress.json> [--readme mncompile/README.md]
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

MARK = "<!-- RESULTS -->"


def utilization(stats: dict) -> str:
    labels = {"alu": "A", "mau": "M", "mwrite": "W", "mread": "R",
              "l1bm": "L1↑", "l1bm-turnaround": "L1↓", "l2bm": "L2",
              "l2bmdarw": "DAR", "mv": "MV"}
    return " ".join(f"{labels.get(u, u)}:{v:.0%}" for u, v in stats.get("unit_utilization", {}).items() if v)


def analyze(progress: dict, directory: Path) -> None:
    """Add measurements to saved results without compiling or changing judge verdicts."""
    from . import problems as P
    from ..stats import program_stats

    problems = {p.name: p for p in P.challenge_problems() + P.mnist_problems()}
    for row in progress["problems"]:
        kernel = directory / row["problem"] / "kernel.vsm"
        if kernel.exists():
            row["resources"] = program_stats(kernel.read_text())
        problem = problems.get(row["problem"])
        if problem is not None:
            reference = problem.directory / "answer.vsm"
            if reference.exists():
                row["reference_resources"] = program_stats(reference.read_text())
        if row.get("lines") is not None and row.get("reference_lines") is not None:
            row["line_delta"] = row["lines"] - row["reference_lines"]


def table(progress: dict) -> str:
    rows = progress["problems"]
    lines = ["| 問題 | 判定 | 生成行数 | 参照解 | 差 | 下限 | 余剰 | 充填率 | 参照充填率 | モード | 戦略 |",
             "| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- | --- | --- |"]
    total_gen = total_ref = 0
    for r in rows:
        ref = r.get("reference_lines")
        n = r.get("lines")
        delta = f"{n - ref:+d}" if n is not None and ref is not None else "-"
        if r["status"] == "accepted" and n and ref:
            total_gen += n
            total_ref += ref
        status = {"accepted": "Accepted"}.get(r["status"], r["status"])
        resources = r.get("resources", {})
        lower = resources.get("resource_lower_bound", "-")
        gap = resources.get("scheduling_gap", "-")
        lines.append(f"| {r['problem']} | {status} | {n if n is not None else '-'} | {ref if ref else '-'} | {delta} | {lower} | {gap} | {utilization(resources)} | {utilization(r.get('reference_resources', {}))} | {r.get('mode', 'general')} | {r.get('strategy') or ''} |")
    acc = sum(r["status"] == "accepted" for r in rows)
    le = sum(r["status"] == "accepted" and r.get("reference_lines") and r["lines"] <= r["reference_lines"] for r in rows)
    head = (f"公式ジャッジで {acc}/{len(rows)} 問 Accepted。参照解（順位表から辿れる最短の公開 Accepted 提出）"
            f"以下の行数は {le} 問。Accepted 問題の行数合計は生成 {total_gen} 行 / 参照解 {total_ref} 行。\n\n")
    legend = ("下限は現在の命令列・ユニット割当を固定した資源下限（ユニット別命令数の最大）。余剰は生成行数との差で、"
              "依存・レイテンシ・ポート制約も含む。別の命令選択やアルゴリズムの下限ではない。\n"
              "充填率は全行に占める各ユニットの発行行数。A=ALU、M=MAU、W/R=行列レジスタ書込/読出、"
              "L1↑/↓=L1BM上り/折り返し、L2=L2BM、DAR=DAR書込、MV=MV。\n\n")
    return head + legend + "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("directory", type=Path)
    ap.add_argument("--readme", type=Path)
    ap.add_argument("--analyze", action="store_true", help="add resource statistics to saved progress.json without recompiling")
    args = ap.parse_args()
    progress = json.loads((args.directory / "progress.json").read_text())
    if args.analyze:
        analyze(progress, args.directory)
        (args.directory / "progress.json").write_text(json.dumps(progress, indent=2) + "\n")
    text = table(progress)
    if args.readme:
        body = args.readme.read_text()
        head = body.split(MARK)[0]
        args.readme.write_text(head + MARK + "\n\n" + text)
    else:
        print(text)


if __name__ == "__main__":
    main()
