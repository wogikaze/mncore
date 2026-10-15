#!/usr/bin/env python3
"""Import the shortest public Accepted MNIST submissions into the local `problems/` tree.

For every MNIST problem directory (matched by the `slug:` in its problem.md) this saves the
shortest Accepted submission linked from /mnist/standings/ as `answer.vsm`, with provenance
in `answer.json` and `answer.md`. Existing files (including the editable `main.vsm`) are
never overwritten.

    uv run --with beautifulsoup4 python problems/sync_mnist_answers.py
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

from sync_mnist_problems import BeautifulSoup, REPO_ROOT, _download_text

BASE_URL = "https://mncore-challenge.preferred.jp"


def save_if_missing(path: Path, body: str) -> None:
    if not path.exists():
        path.write_text(body, encoding="utf-8")


def local_problems(root: Path) -> dict[str, Path]:
    out = {}
    for d in sorted(root.iterdir()):
        md = d / "problem.md"
        if d.is_dir() and md.exists():
            m = re.search(r"^source_url: .*/mnist/problem/([^/\s]+)/?\s*$", md.read_text(encoding="utf-8"), re.M)
            if m:
                out[m[1]] = d
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output-root", type=Path, default=REPO_ROOT / "problems")
    parser.add_argument("--cookie", default="")
    parser.add_argument("--timeout-sec", type=int, default=30)
    parser.add_argument("--delay-sec", type=float, default=0.5)
    args = parser.parse_args()
    if BeautifulSoup is None:
        parser.error("beautifulsoup4 is required (uv run --with beautifulsoup4 python ...)")

    standings_url = f"{BASE_URL}/mnist/standings/"
    standings = BeautifulSoup(_download_text(standings_url, args.cookie, args.timeout_sec), "html.parser")
    columns = [th["data-prob-id"] for th in standings.select("thead tr:first-child th[data-prob-id]")]
    candidates: dict[str, tuple[int, str]] = {}
    for row in standings.select("tbody tr"):
        cells = row.select("td.score")
        if len(cells) != len(columns):
            raise ValueError("Standings problem columns do not match score cells")
        for slug, cell in zip(columns, cells):
            link = cell.select_one('a[href^="/mnist/shortest/"]')
            lines = cell.get("data-num-lines", "")
            if link and lines.isdigit():
                candidate = (int(lines), urljoin(BASE_URL, link["href"]))
                # the first row listed wins ties (standings order)
                if slug not in candidates or candidate[0] < candidates[slug][0]:
                    candidates[slug] = candidate

    dirs = local_problems(args.output_root)
    failures = []
    for slug, target in dirs.items():
        try:
            if (target / "answer.vsm").exists() and (target / "answer.json").exists():
                print(f"[skip] {target.name}: existing answer preserved")
                continue
            if slug not in candidates:
                raise ValueError("No public submission found in standings")
            num_lines, shortest_url = candidates[slug]
            req = Request(shortest_url, headers={"User-Agent": "mncore-problem-sync/1.0"})
            if args.cookie:
                req.add_header("Cookie", args.cookie)
            with urlopen(req, timeout=args.timeout_sec) as response:
                submission_url = response.url
                submission = BeautifulSoup(response.read().decode("utf-8"), "html.parser")
            detail = submission.select_one("div.page.submission")
            if detail is None:
                raise ValueError("Public submission detail missing")
            problem_link = detail.select_one("h1 a[href]")
            if not problem_link or urlparse(problem_link["href"]).path.strip("/") != f"mnist/problem/{slug}":
                raise ValueError("Submission belongs to a different problem")
            status_tag = detail.select_one("span.accepted")
            editor = detail.select_one("#vsm")
            if not status_tag or status_tag.get_text(strip=True) != "Accepted" or not editor:
                raise ValueError("Submission is not Accepted or VSM is missing")
            code = editor.get_text().strip() + "\n"
            metadata = detail.get_text("\n", strip=True)
            author_match = re.search(r"Author:\s*([^\n]+)", metadata)
            lines_match = re.search(r"Lines:\s*(\d+)", metadata)
            if not author_match or not lines_match or int(lines_match[1]) != num_lines:
                raise ValueError("Submission author or line count does not match standings")
            author = author_match[1]
            provenance = {
                "problem_url": f"{BASE_URL}/mnist/problem/{slug}/", "standings_url": standings_url,
                "shortest_url": shortest_url, "submission_url": submission_url,
                "author": author, "status": "Accepted", "lines": num_lines,
                "fetched_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                "local_validation": "not_run",
            }
            title = re.search(r"^# (.+)$", (target / "problem.md").read_text(encoding="utf-8"), re.M)[1]
            save_if_missing(target / "answer.vsm", code)
            save_if_missing(target / "answer.json", json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
            save_if_missing(target / "answer.md", (
                f"# {title} — Answer\n\n"
                "MNIST 順位表から辿れる公開 Accepted 提出を `answer.vsm` に保存しています（`main.vsm` は変更しません）。\n\n"
                f"- Author: {author}\n- Lines: {num_lines}\n- Status: Accepted（サイト上）\n"
                f"- Submission: {submission_url}\n- Standings: {standings_url}\n\n"
                "取得時の順位表で最小行数の提出を選んでいます。同率の場合は先に掲載された提出を採用します。\n"
                "提出者のコードをそのまま保存しています。\n"))
            print(f"[ok] {target.name}: {num_lines} lines / {author}")
            time.sleep(args.delay_sec)
        except Exception as exc:  # noqa: BLE001 - report every problem
            failures.append(slug)
            print(f"[error] {slug}: {exc}", file=sys.stderr)
    print(f"Imported answers for {len(dirs) - len(failures)}/{len(dirs)} problems; failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
