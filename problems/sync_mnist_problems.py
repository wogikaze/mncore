#!/usr/bin/env python3
"""Sync MN-Core Challenge MNIST problems into local `problems/` tree.

What this script does:
1. Collect problem slugs/titles from `/mnist/problems/` (or fallback list).
2. Create `problems/<index>.<name>/` directories.
3. Fetch each `testcase.vsm` from the challenge site.
4. If web fetch fails, fallback to `testcases/<slug>.vsm` if available.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
from urllib import error, request


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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Create problems/* directories and fetch testcase.vsm files."
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
        "--timeout-sec",
        type=int,
        default=20,
        help="Network timeout in seconds.",
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
        f"fetched={fetched}, copied_from_cache={copied_cache}, "
        f"skipped_existing={skipped_existing}, missing={missing}"
    )
    if args.strict_missing and missing > 0:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
