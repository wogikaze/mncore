#!/usr/bin/env python3
"""Sync MN-Core Challenge MNIST problems into local `problems/` tree.

What this script does:
1. Collect problem slugs/titles from `/mnist/problems/` (or fallback list).
2. Create `problems/<index>.<name>/` directories.
3. Fetch each problem page and write `problem.md`.
4. Fetch each `testcase.vsm` from the challenge site.
5. If testcase fetch fails, fallback to `testcases/<slug>.vsm` if available.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
from datetime import datetime, timezone
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
from urllib import error, parse, request

try:
    from bs4 import BeautifulSoup
    from bs4.element import NavigableString, Tag
except ImportError:
    BeautifulSoup = None  # type: ignore[assignment]
    NavigableString = None  # type: ignore[assignment]
    Tag = None  # type: ignore[assignment]


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT_ROOT = REPO_ROOT / "problems"
DEFAULT_TESTCASE_CACHE = REPO_ROOT / "testcases"


@dataclass(frozen=True)
class ProblemEntry:
    title: str
    slug: str


# Fallback order from the currently published MNIST additional problems page.
FALLBACK_ENTRIES: tuple[ProblemEntry, ...] = (
    ProblemEntry("A - B", "mat_sub"),
    ProblemEntry("FMul 7", "mul_const"),
    ProblemEntry("ReLU", "relu"),
    ProblemEntry("ReLU grad", "relu_grad"),
    ProblemEntry("AddCol vec", "add_colvec"),
    ProblemEntry("SubRow vec", "sub_rowvec"),
    ProblemEntry("SumCol mini", "sum_col_mini"),
    ProblemEntry("SumCol", "sum_col"),
    ProblemEntry("SumRow mini", "sum_row_mini"),
    ProblemEntry("SumRow", "sum_row"),
    ProblemEntry("MaxRow", "max_row"),
    ProblemEntry("DivRow vec", "div_row"),
    ProblemEntry("Exp low prec", "exp_lowprec"),
    ProblemEntry("Exp", "exp"),
    ProblemEntry("Onehot mini", "onehot_mini"),
    ProblemEntry("Onehot", "onehot"),
    ProblemEntry("DL 256_16", "dram_dl_256_16"),
    ProblemEntry("UL 256_16", "dram_ul_256_16"),
    ProblemEntry("DL PE 256_16", "dram_dl_256_16p"),
    ProblemEntry("UL PE 256_16", "dram_ul_256_16p"),
    ProblemEntry("DL L2B 256_16", "dram_dl_256_16_l2b"),
    ProblemEntry("DL 1024_16", "dram_dl_1024_16"),
    ProblemEntry("DL 256_1024", "dram_dl_256_1024"),
    ProblemEntry("DL 16", "dram_dl_16"),
    ProblemEntry("UL 16", "dram_ul_16"),
    ProblemEntry("DL 16_1024", "dram_dl_16_1024"),
    ProblemEntry("UL 16_1024", "dram_ul_16_1024"),
    ProblemEntry("DL 16_16", "dram_dl_16_16"),
    ProblemEntry("UL 16_16", "dram_ul_16_16"),
    ProblemEntry("DL 256", "dram_dl_256"),
    ProblemEntry("UL 256", "dram_ul_256"),
    ProblemEntry("Mmul TB 4_8_8", "matmul_trb_mab_lm_4_8_8"),
    ProblemEntry("Mmul TB 4_8_16", "matmul_trb_mab_lm_4_8_16"),
    ProblemEntry("Mmul TB 4_16_8", "matmul_trb_mab_lm_4_16_8"),
    ProblemEntry("Mmul TB 4_16_16", "matmul_trb_mab_lm_4_16_16"),
    ProblemEntry("Mmul TB 256_16_16", "matmul_trb_pkg_lm_256_16_16"),
    ProblemEntry("Mmul TB 32_8_16", "matmul_trb_mab_lm_32_8_16"),
    ProblemEntry("Mmul TB 256_128_16", "matmul_trb_pkg_lm_256_128_16"),
    ProblemEntry("Mmul TB D 256_1024_16", "matmul_trb_pkg_lmdram_256_1024_16"),
    ProblemEntry("Mmul 4_8_8", "matmul_notr_mab_lm_4_8_8"),
    ProblemEntry("Mmul 4_16_16", "matmul_notr_mab_lm_4_16_16"),
    ProblemEntry("Mmul 256_16_16", "matmul_notr_pkg_lm_256_16_16"),
    ProblemEntry("Mmul TA 8_8_8", "matmul_tra_mab_lm_8_8_8"),
    ProblemEntry("Mmul TA 16_8_16", "matmul_tra_mab_lm_16_8_16"),
    ProblemEntry("Mmul TA 16_4_16", "matmul_tra_mab_lm_16_4_16"),
    ProblemEntry("Mmul TA D 16_256_16", "matmul_tra_pkg_lmdram_16_256_16"),
    ProblemEntry("Mmul TA 16_32_8", "matmul_tra_mab_lm_16_32_8"),
    ProblemEntry("Mmul TA D 16_256_1024", "matmul_tra_pkg_lmdram_16_256_1024"),
)


# Keep local directory labels compatible with existing naming in this repo.
BASENAME_OVERRIDES: dict[str, str] = {
    "mat_sub": "a-b",
    "mul_const": "fmul7",
    "relu": "relu",
    "relu_grad": "relu-grad",
    "add_colvec": "addcol-vec",
    "sub_rowvec": "subrow-vec",
    "sum_col_mini": "sumcol-mini",
    "sum_col": "sumcol",
    "sum_row_mini": "sumrow-mini",
    "sum_row": "sumrow",
    "max_row": "maxrow",
    "div_row": "divrow-vec",
    "exp_lowprec": "exp-low-prec",
    "exp": "exp",
    "onehot_mini": "onehot-mini",
}


def _sanitize_basename(text: str) -> str:
    out = text.strip().lower().replace("_", "-")
    out = re.sub(r"[^a-z0-9-]+", "-", out)
    out = re.sub(r"-{2,}", "-", out).strip("-")
    return out or "problem"


def _parse_entries_from_text(raw: str) -> list[ProblemEntry]:
    entries: list[ProblemEntry] = []
    seen: set[str] = set()

    # HTML anchor style.
    html_re = re.compile(
        r'href=["\'](?:https?://[^"\']+)?/mnist/problem/([a-zA-Z0-9_]+)["\'][^>]*>(.*?)</a>',
        re.S,
    )
    for m in html_re.finditer(raw):
        slug = m.group(1).strip()
        if slug in seen:
            continue
        title = re.sub(r"<[^>]+>", " ", m.group(2))
        title = re.sub(r"\s+", " ", title).strip() or slug
        entries.append(ProblemEntry(title=title, slug=slug))
        seen.add(slug)

    # Markdown link style.
    md_re = re.compile(r"\[([^\]]+?)\]\(/mnist/problem/([a-zA-Z0-9_]+)\)")
    for m in md_re.finditer(raw):
        title = re.sub(r"\s+", " ", m.group(1)).strip() or m.group(2)
        slug = m.group(2).strip()
        if slug in seen:
            continue
        entries.append(ProblemEntry(title=title, slug=slug))
        seen.add(slug)

    return entries


def _download_text(url: str, cookie_header: str | None, timeout_sec: int) -> str:
    req = request.Request(url)
    if cookie_header:
        req.add_header("Cookie", cookie_header)
    req.add_header("User-Agent", "mncore-problem-sync/1.0")
    with request.urlopen(req, timeout=timeout_sec) as resp:
        data = resp.read()
    return data.decode("utf-8", errors="replace")


def _looks_like_testcase_vsm(body: str) -> bool:
    head = body.lstrip()[:200].lower()
    if head.startswith("<!doctype html") or head.startswith("<html"):
        return False
    # testcase typically contains debug set/get or assembly statements.
    return any(token in body for token in ("d set", "d get", "imm ", "l2bm", "fv", "hv", "dv"))


def _looks_like_html_page(body: str) -> bool:
    head = body.lstrip()[:500].lower()
    return head.startswith("<!doctype html") or "<html" in head


def _iter_existing_problem_dirs(root: Path) -> Iterable[tuple[int, str, Path]]:
    pat = re.compile(r"^(\d+)\.(.+)$")
    for p in sorted(root.iterdir()):
        if not p.is_dir():
            continue
        m = pat.match(p.name)
        if not m:
            continue
        yield int(m.group(1)), m.group(2), p


def _resolve_target_dir(
    output_root: Path,
    slug: str,
    max_index_ref: list[int],
    suffix_to_dir: dict[str, Path],
) -> Path:
    base = BASENAME_OVERRIDES.get(slug, _sanitize_basename(slug))
    if base in suffix_to_dir:
        return suffix_to_dir[base]
    max_index_ref[0] += 1
    target = output_root / f"{max_index_ref[0]}.{base}"
    suffix_to_dir[base] = target
    return target


def _compact_text(text: str) -> str:
    text = text.replace("\xa0", " ")
    text = re.sub(r"[ \t\r\f\v]+", " ", text)
    text = re.sub(r"[ \t]*\n[ \t]*", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def _compact_inline_text(text: str) -> str:
    text = text.replace("\xa0", " ")
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def _resolve_href(page_url: str, href: str) -> str:
    # Some pages use bare slugs like "exp_lowprec" instead of absolute paths.
    if re.fullmatch(r"[a-zA-Z0-9_]+", href):
        return parse.urljoin(page_url, f"/mnist/problem/{href}/")
    return parse.urljoin(page_url, href)


def _render_inline(node: object, page_url: str) -> str:
    if NavigableString is not None and isinstance(node, NavigableString):
        return str(node)
    if Tag is None or not isinstance(node, Tag):
        return ""

    if node.name == "code":
        code = _compact_text(node.get_text(" ", strip=True))
        return f"`{code}`" if code else ""
    if node.name == "br":
        return " "
    if node.name == "a":
        text = _compact_text("".join(_render_inline(c, page_url) for c in node.children))
        href = node.get("href")
        if href:
            return f"[{text or href}]({_resolve_href(page_url, href)})"
        return text
    if node.name == "img":
        alt = _compact_text(node.get("alt") or "image")
        src = node.get("src")
        if src:
            return f"![{alt}]({parse.urljoin(page_url, src)})"
        return f"![{alt}]"

    return "".join(_render_inline(c, page_url) for c in node.children)


def _render_inline_text(tag: Tag, page_url: str) -> str:
    text = "".join(_render_inline(c, page_url) for c in tag.children)
    text = _compact_inline_text(text)
    return text


def _render_block(tag: Tag, page_url: str) -> list[str]:
    out: list[str] = []
    name = tag.name

    if name in {"p", "a"}:
        if name == "a":
            text = _compact_inline_text(_render_inline(tag, page_url))
        else:
            text = _render_inline_text(tag, page_url)
        if text:
            out.append(text)
        return out

    if name in {"ul", "ol"}:
        for li in tag.find_all("li", recursive=False):
            li_text = _render_inline_text(li, page_url)
            if li_text:
                out.append(f"* {li_text}")
        return out

    if name == "pre":
        body = tag.get_text("\n", strip=False).strip("\n")
        if body:
            out.append("```text")
            out.append(body)
            out.append("```")
        return out

    if name == "details":
        summary = ""
        summary_tag = tag.find("summary", recursive=False)
        if summary_tag:
            summary = _render_inline_text(summary_tag, page_url)
        if summary:
            out.append(f"### {summary}")
        # Some matmul pages embed very large matrices in collapsed details blocks.
        # Keep markdown compact for LLM consumption.
        details_text = _compact_inline_text(tag.get_text(" ", strip=True))
        if len(details_text) > 3000:
            out.append("_詳細データは省略。必要なら source_url を参照してください。_")
            return out
        for child in tag.children:
            if Tag is None or not isinstance(child, Tag):
                continue
            if child.name == "summary":
                continue
            out.extend(_render_block(child, page_url))
        return out

    if name == "div":
        classes = set(tag.get("class") or [])
        if "testcases" in classes:
            links = tag.find_all("a", recursive=False)
            if links:
                for a in links:
                    text = _compact_inline_text(_render_inline(a, page_url))
                    if text:
                        out.append(f"* {text}")
                return out

    text = _render_inline_text(tag, page_url)
    if text:
        out.append(text)
    return out


def _squash_blank_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    prev_blank = False
    for line in lines:
        blank = line.strip() == ""
        if blank and prev_blank:
            continue
        out.append("" if blank else line.rstrip())
        prev_blank = blank
    while out and out[-1] == "":
        out.pop()
    return out


def _render_problem_markdown_from_html(html: str, page_url: str, slug: str) -> str | None:
    if BeautifulSoup is None or Tag is None:
        return None

    soup = BeautifulSoup(html, "html.parser")
    root = soup.select_one("div.problem.page")
    if root is None:
        return None

    for bad in root.select("script,style,.help-button"):
        bad.decompose()

    h1 = root.find("h1")
    title = _compact_text(h1.get_text(" ", strip=True)) if h1 else slug

    top_line = ""
    par_line = ""
    for p in root.find_all("p", recursive=False):
        text = _compact_text(p.get_text(" ", strip=True))
        if text.startswith("Top:"):
            top_line = text
        elif text.startswith("Par:"):
            par_line = text

    sections: list[tuple[str, list[Tag]]] = []
    current_name = ""
    current_nodes: list[Tag] = []

    for child in root.children:
        if not isinstance(child, Tag):
            continue
        if child.name == "h2":
            if current_name:
                sections.append((current_name, current_nodes))
            current_name = _compact_text(child.get_text(" ", strip=True))
            current_nodes = []
            continue
        if child.name == "h1":
            continue
        if not current_name:
            continue
        current_nodes.append(child)

    if current_name:
        sections.append((current_name, current_nodes))

    if not sections:
        return None

    fetched_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    lines: list[str] = [
        "---",
        f"source_url: {page_url}",
        f"slug: {slug}",
        f"fetched_at: {fetched_at}",
        "---",
        "",
        f"# {title}",
        "",
    ]
    if top_line:
        lines.append(f"- {top_line}")
    if par_line:
        lines.append(f"- {par_line}")
    if top_line or par_line:
        lines.append("")

    for section_name, nodes in sections:
        if section_name.lower() == "submission":
            continue
        body_lines: list[str] = []
        for node in nodes:
            body_lines.extend(_render_block(node, page_url))
        body_lines = _squash_blank_lines(body_lines)
        if not body_lines:
            continue
        lines.append(f"## {section_name}")
        lines.append("")
        lines.extend(body_lines)
        lines.append("")

    lines = _squash_blank_lines(lines)
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create problems/* directories, fetch problem statements, and sync testcase.vsm."
    )
    parser.add_argument(
        "--problems-url",
        default="https://mncore-challenge.preferred.jp/mnist/problems/",
        help="Problem list URL.",
    )
    parser.add_argument(
        "--source-file",
        type=Path,
        default=None,
        help="Optional local HTML/Markdown file to parse instead of downloading --problems-url.",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=DEFAULT_OUTPUT_ROOT,
        help=f"Output root for numbered problem directories (default: {DEFAULT_OUTPUT_ROOT}).",
    )
    parser.add_argument(
        "--testcase-cache",
        type=Path,
        default=DEFAULT_TESTCASE_CACHE,
        help=f"Fallback local testcase cache dir (default: {DEFAULT_TESTCASE_CACHE}).",
    )
    parser.add_argument(
        "--cookie",
        default=None,
        help="Cookie header value for authenticated fetch (example: 'sessionid=...').",
    )
    parser.add_argument(
        "--problem-url-format",
        default="https://mncore-challenge.preferred.jp/mnist/problem/{slug}/",
        help="Problem page URL format used to fetch problem statements.",
    )
    parser.add_argument(
        "--timeout-sec",
        type=int,
        default=20,
        help="Network timeout in seconds.",
    )
    parser.add_argument(
        "--skip-problem-md",
        action="store_true",
        help="Skip fetching/writing problems/*/problem.md.",
    )
    parser.add_argument(
        "--overwrite-problem-md",
        action="store_true",
        help="Overwrite existing problems/*/problem.md.",
    )
    parser.add_argument(
        "--overwrite-testcase",
        action="store_true",
        help="Overwrite existing problems/*/testcase.vsm.",
    )
    parser.add_argument(
        "--only",
        default=None,
        help="Comma-separated slugs to process (example: relu,relu_grad).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print planned actions without writing files.",
    )
    parser.add_argument(
        "--strict-missing",
        action="store_true",
        help="Exit with non-zero status when testcase is missing.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    output_root = args.output_root.resolve()
    testcase_cache = args.testcase_cache.resolve()
    output_root.mkdir(parents=True, exist_ok=True)

    source_text = ""
    if args.source_file:
        source_text = args.source_file.read_text(encoding="utf-8")
    else:
        try:
            source_text = _download_text(args.problems_url, args.cookie, args.timeout_sec)
        except Exception as e:
            print(f"[warn] failed to fetch problems page: {e}")

    entries = _parse_entries_from_text(source_text)
    if not entries:
        print("[warn] using built-in fallback problem list")
        entries = list(FALLBACK_ENTRIES)

    if args.only:
        wanted = {s.strip() for s in args.only.split(",") if s.strip()}
        entries = [e for e in entries if e.slug in wanted]

    existing = list(_iter_existing_problem_dirs(output_root))
    suffix_to_dir = {suffix: path for _, suffix, path in existing}
    max_index_ref = [max((idx for idx, _, _ in existing), default=0)]

    created_dirs = 0
    created_main = 0
    problem_written = 0
    problem_skipped_existing = 0
    problem_missing = 0
    fetched = 0
    copied_cache = 0
    skipped_existing = 0
    missing = 0

    for e in entries:
        target_dir = _resolve_target_dir(output_root, e.slug, max_index_ref, suffix_to_dir)
        testcase_path = target_dir / "testcase.vsm"

        if not target_dir.exists():
            print(f"[mkdir] {target_dir.relative_to(REPO_ROOT)}")
            created_dirs += 1
            if not args.dry_run:
                target_dir.mkdir(parents=True, exist_ok=True)

        main_vsm = target_dir / "main.vsm"
        if not main_vsm.exists():
            print(f"[touch] {main_vsm.relative_to(REPO_ROOT)}")
            created_main += 1
            if not args.dry_run:
                main_vsm.write_text("# write solution here\n", encoding="utf-8")

        if not args.skip_problem_md:
            problem_md_path = target_dir / "problem.md"
            if problem_md_path.exists() and not args.overwrite_problem_md:
                problem_skipped_existing += 1
                print(f"[skip]  {problem_md_path.relative_to(REPO_ROOT)} (already exists)")
            else:
                try:
                    problem_url = args.problem_url_format.format(slug=e.slug)
                except KeyError as ex:
                    print(f"[warn] invalid --problem-url-format (missing key): {ex}")
                    problem_missing += 1
                    problem_url = ""
                if problem_url:
                    try:
                        html = _download_text(problem_url, args.cookie, args.timeout_sec)
                    except error.HTTPError as ex:
                        print(f"[warn] http error for problem slug={e.slug}: {ex.code}")
                        html = ""
                    except Exception as ex:
                        print(f"[warn] failed to fetch problem page for slug={e.slug}: {ex}")
                        html = ""

                    if html and not _looks_like_html_page(html):
                        print(f"[warn] fetched non-html content for problem slug={e.slug}")
                        html = ""

                    md = _render_problem_markdown_from_html(
                        html, problem_url, e.slug
                    ) if html else None
                    if md:
                        print(f"[write] {problem_md_path.relative_to(REPO_ROOT)} <= {problem_url}")
                        problem_written += 1
                        if not args.dry_run:
                            problem_md_path.write_text(md, encoding="utf-8")
                    else:
                        print(f"[miss]  problem.md not generated for slug={e.slug}")
                        problem_missing += 1

        if testcase_path.exists() and not args.overwrite_testcase:
            skipped_existing += 1
            print(f"[skip]  {testcase_path.relative_to(REPO_ROOT)} (already exists)")
            continue

        testcase_url = (
            f"https://mncore-challenge.preferred.jp/mnist/testcase/{e.slug}/testcase.vsm"
        )
        body = ""
        fetched_ok = False
        try:
            body = _download_text(testcase_url, args.cookie, args.timeout_sec)
            if _looks_like_testcase_vsm(body):
                fetched_ok = True
            else:
                print(f"[warn] fetched non-testcase content for slug={e.slug}")
        except error.HTTPError as ex:
            print(f"[warn] http error for slug={e.slug}: {ex.code}")
        except Exception as ex:
            print(f"[warn] network fetch failed for slug={e.slug}: {ex}")

        if fetched_ok:
            print(f"[fetch] {testcase_path.relative_to(REPO_ROOT)} <= {testcase_url}")
            fetched += 1
            if not args.dry_run:
                testcase_path.write_text(body, encoding="utf-8")
            continue

        cache_src = testcase_cache / f"{e.slug}.vsm"
        if cache_src.exists():
            print(f"[copy]  {testcase_path.relative_to(REPO_ROOT)} <= {cache_src.relative_to(REPO_ROOT)}")
            copied_cache += 1
            if not args.dry_run:
                shutil.copyfile(cache_src, testcase_path)
            continue

        print(f"[miss]  testcase not found for slug={e.slug}")
        missing += 1

    print(
        "\nSummary: "
        f"dirs_created={created_dirs}, main_created={created_main}, "
        f"problem_written={problem_written}, "
        f"problem_skipped_existing={problem_skipped_existing}, "
        f"problem_missing={problem_missing}, "
        f"fetched={fetched}, copied_from_cache={copied_cache}, "
        f"skipped_existing={skipped_existing}, missing={missing}"
    )
    if args.strict_missing and (missing > 0 or problem_missing > 0):
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
