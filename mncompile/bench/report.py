"""Markdown results table from a benchmark progress.json (inserted into mncompile/README.md).

    python -m mncompile.bench.report <dir with progress.json> [--readme mncompile/README.md]
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

MARK = "<!-- RESULTS -->"


def table(progress: dict) -> str:
    rows = progress["problems"]
    lines = ["| 問題 | 判定 | 生成行数 | 参照解 | 比 | 戦略 |", "| --- | --- | ---: | ---: | ---: | --- |"]
    total_gen = total_ref = 0
    for r in rows:
        ref = r.get("reference_lines")
        n = r.get("lines")
        ratio = f"{n / ref:.2f}" if n and ref else ""
        if r["status"] == "accepted" and n and ref:
            total_gen += n
            total_ref += ref
        status = {"accepted": "Accepted"}.get(r["status"], r["status"])
        lines.append(f"| {r['problem']} | {status} | {n if n is not None else '-'} | {ref if ref else '-'} | {ratio} | {r.get('strategy') or ''} |")
    acc = sum(r["status"] == "accepted" for r in rows)
    le = sum(r["status"] == "accepted" and r.get("reference_lines") and r["lines"] <= r["reference_lines"] for r in rows)
    head = (f"公式ジャッジで {acc}/{len(rows)} 問 Accepted。参照解（公開されている最短の Accepted 提出、MNIST は問題ページの Top）"
            f"以下の行数は {le} 問。Accepted 問題の行数合計は生成 {total_gen} 行 / 参照解 {total_ref} 行。\n\n")
    return head + "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("directory", type=Path)
    ap.add_argument("--readme", type=Path)
    args = ap.parse_args()
    progress = json.loads((args.directory / "progress.json").read_text())
    text = table(progress)
    if args.readme:
        body = args.readme.read_text()
        head = body.split(MARK)[0]
        args.readme.write_text(head + MARK + "\n\n" + text)
    else:
        print(text)


if __name__ == "__main__":
    main()
