#!/usr/bin/env python3
"""Fetch the original Challenge, independently of the MNIST problem set.

Requires beautifulsoup4. Existing statements, testcases and answers are preserved.
Imports the shortest public Accepted submission linked from the standings.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

from sync_mnist_problems import (
    BeautifulSoup,
    REPO_ROOT,
    _download_text,
    _looks_like_testcase_vsm,
    _render_problem_markdown_from_html,
    _sanitize_basename,
)

BASE_URL = "https://mncore-challenge.preferred.jp"


def save_if_missing(path: Path, body: str) -> None:
    if not path.exists():
        path.write_text(body, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path, default=REPO_ROOT / "problems/challenge")
    parser.add_argument("--cookie", help="Optional Cookie header for authenticated downloads")
    parser.add_argument("--timeout-sec", type=int, default=30)
    args = parser.parse_args()
    if BeautifulSoup is None:
        parser.error("beautifulsoup4 is required (uv run --with beautifulsoup4 python ...)")

    def download(url: str) -> str:
        return _download_text(url, args.cookie, args.timeout_sec)

    listing = BeautifulSoup(download(f"{BASE_URL}/problems/"), "html.parser")
    entries: dict[str, str] = {}
    for link in listing.select("a[href]"):
        url = urljoin(BASE_URL, link["href"])
        parts = urlparse(url)
        path = parts.path.strip("/").split("/")
        if parts.netloc == urlparse(BASE_URL).netloc and len(path) == 2 and path[0] == "problem":
            entries.setdefault(path[1], url)
    if not entries:
        raise RuntimeError("No Challenge problems found; refusing to generate an empty set")

    args.output_root.mkdir(parents=True, exist_ok=True)
    standings_url = f"{BASE_URL}/standings/"
    standings = BeautifulSoup(download(standings_url), "html.parser")
    columns = [th["data-prob-id"] for th in standings.select("thead tr:first-child th[data-prob-id]")]
    candidates = {}
    for row in standings.select("tbody tr"):
        cells = row.select("td.score")
        if len(cells) != len(columns):
            raise ValueError("Standings problem columns do not match score cells")
        for slug, cell in zip(columns, cells):
            link = cell.select_one('a[href^="/shortest/"]')
            lines = cell.get("data-num-lines", "")
            if link and lines.isdigit():
                candidate = (int(lines), urljoin(BASE_URL, link["href"]))
                if slug not in candidates or candidate[0] < candidates[slug][0]:
                    candidates[slug] = candidate

    rows = []
    failures = []
    for index, (slug, url) in enumerate(entries.items(), 1):
        try:
            target = args.output_root / f"{index}.{_sanitize_basename(slug)}"
            bundle = ("problem.md", "testcase.vsm", "answer.vsm", "main.vsm", "answer.md", "answer.json")
            if all((target / filename).exists() for filename in bundle):
                saved = json.loads((target / "answer.json").read_text(encoding="utf-8"))
                title = re.search(r"^# (.+)$", (target / "problem.md").read_text(encoding="utf-8"), re.M)[1]
                status = f"{saved['status']} / {saved['lines']} lines / {saved['author']}"
                rows.append(f"| [{title}]({target.name}/problem.md) | [answer]({target.name}/answer.md) | {status} |")
                print(f"[skip] {target.name}: existing bundle preserved")
                continue
            if (target / "answer.vsm").exists() or (target / "answer.json").exists():
                raise ValueError("Incomplete answer bundle; restore missing files before syncing to avoid mixing provenance")
            html = download(url)
            soup = BeautifulSoup(html, "html.parser")
            root = soup.select_one("div.problem.page")
            if root is None:
                raise ValueError("Problem statement missing (login page or changed HTML)")
            title = root.h1.get_text(" ", strip=True)
            target.mkdir(parents=True, exist_ok=True)
            md = _render_problem_markdown_from_html(html, url, slug)
            if not md:
                raise ValueError("Could not render problem statement")
            save_if_missing(target / "problem.md", md)

            testcase_links = {}
            for link in root.select("a[href]"):
                testcase_url = urljoin(url, link["href"])
                filename = Path(urlparse(testcase_url).path).name
                if filename.startswith("testcase") and filename.endswith(".vsm"):
                    testcase_links[filename] = testcase_url
            if not testcase_links:
                raise ValueError("No official testcase links found")
            for filename, testcase_url in testcase_links.items():
                path = target / filename
                if path.exists():
                    continue
                body = download(testcase_url)
                if not _looks_like_testcase_vsm(body):
                    raise ValueError(f"Not a VSM testcase: {testcase_url}")
                save_if_missing(path, body)

            # Tutorials publish an answer inside the explicitly labelled spoiler.
            # Never mistake an illustrative (possibly incorrect) snippet for an answer.
            answers = []
            for detail in root.select("details"):
                summary = detail.find("summary")
                if summary and "想定解" in summary.get_text():
                    answers.extend(detail.select(".editor"))
            if answers:
                code = answers[0].get_text().strip() + "\n"
                save_if_missing(target / "official.vsm", code)

            if slug not in candidates:
                raise ValueError("No public submission found in standings")
            num_lines, shortest_url = candidates[slug]
            # Follow /shortest/<problem>/<author>/ to the concrete submission UUID.
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
            if not problem_link or urlparse(problem_link["href"]).path.strip("/") != f"problem/{slug}":
                raise ValueError("Submission belongs to a different problem")
            status_tag = detail.select_one("span.accepted")
            editor = detail.select_one("#vsm")
            stdout = detail.select_one("#stdout")
            if not status_tag or status_tag.get_text(strip=True) != "Accepted" or not editor:
                raise ValueError("Submission is not Accepted or VSM is missing")
            code = editor.get_text().strip() + "\n"
            if not code.strip():
                raise ValueError("Empty submission")
            metadata = detail.get_text("\n", strip=True)
            author_match = re.search(r"Author:\s*([^\n]+)", metadata)
            lines_match = re.search(r"Lines:\s*(\d+)", metadata)
            if not author_match or not lines_match or int(lines_match[1]) != num_lines:
                raise ValueError("Submission author or line count does not match standings")
            author = author_match[1]
            provenance = {
                "problem_url": url, "standings_url": standings_url,
                "shortest_url": shortest_url, "submission_url": submission_url,
                "author": author, "status": "Accepted", "lines": num_lines,
                "stdout": stdout.get_text().strip() if stdout else "",
                "fetched_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                "local_validation": "not_run",
            }
            save_if_missing(target / "answer.vsm", code)
            save_if_missing(target / "main.vsm", code)
            save_if_missing(target / "answer.json", json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
            status = f"Accepted / {num_lines} lines / {author}"
            explanation = (
                f"順位表から辿れる公開 Accepted 提出を `answer.vsm` に保存しています。\n"
                f"`main.vsm` は初回取得時にこの解答で初期化します。\n\n"
                f"- Author: {author}\n- Lines: {num_lines}\n- Status: Accepted（サイト上）\n"
                f"- Submission: {submission_url}\n- Standings: {standings_url}\n\n"
                "取得時の順位表で最小行数の提出を選んでいます。同率の場合は先に掲載された提出を採用します。\n"
                "ローカルでの再検証は未実施です。提出者のコードをそのまま保存しています。"
            )
            save_if_missing(target / "answer.md", f"# {title} — Answer\n\n{explanation}\n\n問題の出典: {url}\n\n検証:\n\n```bash\npython3 problems/run_problem.py challenge/{target.name} --solution problems/challenge/{target.name}/answer.vsm\n```\n")
            rows.append(f"| [{title}]({target.name}/problem.md) | [answer]({target.name}/answer.md) | {status} |")
            print(f"[ok] {target.name}: {status}, {len(testcase_links)} testcase(s)")
        except Exception as exc:
            failures.append(slug)
            print(f"[error] {slug}: {exc}", file=sys.stderr)

    readme = (
        "# MN-Core Challenge（通常問題）\n\n"
        f"出典: {BASE_URL}/problems/\n\n"
        "MNIST 特設問題とは別の問題セットです。各ディレクトリには問題文、公式テストケース、"
        "公開 Accepted 解答 `answer.vsm`、編集用の `main.vsm`、出典・作者・行数を記した `answer.md` / `answer.json` を置きます。\n"
        "順位表で各問題の最小行数の提出を選びます。練習問題の公式想定解も `official.vsm` に保存します。\n"
        "サイト上の Accepted を確認して保存しています。ローカルでの検証結果は各 `answer.json` の `local_validation` を参照してください。\n\n"
        "| Problem | Answer | 状態 |\n| --- | --- | --- |\n" + "\n".join(rows) + "\n"
    )
    if not failures:
        (args.output_root / "README.md").write_text(readme, encoding="utf-8")
    print(f"Synced {len(rows)}/{len(entries)} problems; failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
