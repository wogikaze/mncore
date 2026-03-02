#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import shutil
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

SRC_JSON = Path("docs/mncore.json")
OUT_DIR = Path("docs/mncore_llm")

RE_CHAPTER_TITLE = re.compile(r"^第\s*([0-9]+)章\s*(.+)$")
RE_NUMBERED = re.compile(r"^(\d+\.\d+(?:\.\d+)*)(?:\s*|\u3000*)(.*)$")
RE_BRACKET = re.compile(r"\[([^\[\]]+)\]")
RE_WIKI_LINK = re.compile(r"\[\[([^\[\]]+)\]\]")


@dataclass
class PageRef:
    title: str
    id_: str
    path: Path
    chapter_no: int | None
    section_no: str | None


@dataclass
class RenderedPage:
    title: str
    id_: str
    created: int
    updated: int
    views: int
    body: str


def safe_segment(text: str) -> str:
    text = text.strip().replace("/", "_")
    text = re.sub(r"\s+", "_", text)
    text = re.sub(r"[^0-9A-Za-z_\-\.\u3040-\u30ff\u3400-\u9fff]", "", text)
    text = text.strip("._")
    return text or "untitled"


def section_sort_key(sec: str) -> tuple[int, ...]:
    return tuple(int(p) for p in sec.split("."))


def topic_bucket(title: str) -> str:
    t = title.strip()
    if not t:
        return "other"
    c = t[0]
    if c.isdigit():
        return "num"
    if "A" <= c <= "Z" or "a" <= c <= "z":
        cc = c.lower()
        if cc <= "e":
            return "latin-ae"
        if cc <= "j":
            return "latin-fj"
        if cc <= "o":
            return "latin-ko"
        if cc <= "t":
            return "latin-pt"
        return "latin-uz"

    name = unicodedata.name(c, "")
    if "HIRAGANA" in name:
        return "ja-hiragana"
    if "KATAKANA" in name:
        return "ja-katakana"
    if "CJK UNIFIED IDEOGRAPH" in name:
        return "ja-kanji"
    return "other"


def cosense_to_markdown(line: str) -> str:
    def repl(match: re.Match[str]) -> str:
        body = match.group(1).strip()
        if not body:
            return "[]"
        if body.startswith("http://") or body.startswith("https://"):
            return f"<{body}>"
        parts = body.rsplit(" ", 1)
        if len(parts) == 2 and (parts[1].startswith("http://") or parts[1].startswith("https://")):
            return f"[{parts[0]}]({parts[1]})"
        return f"[[{body}]]"

    line = line.replace("\u00a0", " ")
    return RE_BRACKET.sub(repl, line)


def render_body(lines: Iterable[str], title: str) -> str:
    src = list(lines)
    if src and src[0].strip() == title.strip():
        src = src[1:]

    out: list[str] = []
    i = 0
    while i < len(src):
        line = src[i]
        if line.startswith("code:"):
            lang = line.split(":", 1)[1].strip()
            out.append(f"```{lang}")
            i += 1
            while i < len(src):
                nxt = src[i]
                if nxt == "" or nxt.startswith(" ") or nxt.startswith("\t"):
                    out.append(nxt[1:] if nxt.startswith((" ", "\t")) else "")
                    i += 1
                    continue
                break
            out.append("```")
            continue

        out.append(cosense_to_markdown(line))
        i += 1

    while out and out[-1] == "":
        out.pop()
    return "\n".join(out) + "\n"


def render_page(page: dict) -> RenderedPage:
    title = page["title"].strip()
    return RenderedPage(
        title=title,
        id_=page["id"],
        created=page["created"],
        updated=page["updated"],
        views=int(page.get("views", 0)),
        body=render_body(page.get("lines", []), title),
    )


def choose_output_path(page: RenderedPage, chapter_dirs: dict[int, Path]) -> tuple[Path, int | None, str | None]:
    title = page.title
    page_id = page.id_

    m_ch = RE_CHAPTER_TITLE.match(title)
    if m_ch:
        chapter_no = int(m_ch.group(1))
        base = chapter_dirs.setdefault(chapter_no, OUT_DIR / "chapters" / f"ch{chapter_no:02d}")
        return base / f"chapter__{page_id[:8]}.md", chapter_no, None

    m_num = RE_NUMBERED.match(title)
    if m_num:
        number = m_num.group(1)
        chapter_no = int(number.split(".", 1)[0])
        rest = m_num.group(2).strip()
        base = chapter_dirs.setdefault(chapter_no, OUT_DIR / "chapters" / f"ch{chapter_no:02d}")
        name = safe_segment(rest or "section")
        return base / f"section-{number}__{name}__{page_id[:8]}.md", chapter_no, number

    bucket = topic_bucket(title)
    topic_dir = OUT_DIR / "topics" / bucket
    name = safe_segment(title)
    return topic_dir / f"{name}__{page_id[:8]}.md", None, None


def collect_wikilinks(markdown_text: str) -> list[str]:
    return [m.group(1).strip() for m in RE_WIKI_LINK.finditer(markdown_text)]


def main() -> None:
    obj = json.loads(SRC_JSON.read_text(encoding="utf-8"))
    pages = obj["pages"]

    if OUT_DIR.exists():
        shutil.rmtree(OUT_DIR)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    chapter_dirs: dict[int, Path] = {}
    refs: list[PageRef] = []
    title_to_paths: dict[str, list[str]] = {}
    id_to_path: dict[str, str] = {}
    link_graph: dict[str, list[str]] = {}

    rendered_pages = [render_page(page) for page in pages]

    for page in rendered_pages:
        out_path, chapter_no, section_no = choose_output_path(page, chapter_dirs)
        out_path.parent.mkdir(parents=True, exist_ok=True)

        meta = [
            f"title: {page.title}",
            f"id: {page.id_}",
            f"created_unix: {page.created}",
            f"updated_unix: {page.updated}",
            f"views: {page.views}",
        ]

        content = "---\n" + "\n".join(meta) + "\n---\n\n"
        content += f"# {page.title}\n\n"
        content += page.body
        out_path.write_text(content, encoding="utf-8")

        rel = out_path.relative_to(OUT_DIR).as_posix()
        refs.append(PageRef(title=page.title, id_=page.id_, path=out_path, chapter_no=chapter_no, section_no=section_no))
        title_to_paths.setdefault(page.title, []).append(rel)
        id_to_path[page.id_] = rel
        link_graph[page.title] = sorted(set(collect_wikilinks(page.body)))

    refs_sorted = sorted(refs, key=lambda x: x.path.as_posix())

    chapter_map: dict[int, list[PageRef]] = {}
    topic_refs: list[PageRef] = []
    for ref in refs_sorted:
        if ref.chapter_no is None:
            topic_refs.append(ref)
        else:
            chapter_map.setdefault(ref.chapter_no, []).append(ref)

    # Root README
    readme_lines = [
        "# mncore_llm",
        "",
        "Cosense JSON Export (`docs/mncore.json`) を LLM/開発者向けに再編成したドキュメント群。",
        "",
        "## Entry Points",
        "",
        "- `LLM.txt`: LLM向けの最短ガイド",
        "- `README.md`: 人間向けの全体案内",
        "- `DEVELOPMENT.md`: 再生成手順と設計",
        "- `indexes/chapter_index.md`: 章別索引",
        "- `indexes/topic_index.md`: 用語/雑多ページ索引",
        "",
        "## Stats",
        "",
        f"- Pages: {len(refs_sorted)}",
        f"- Chapters: {len(chapter_map)}",
        f"- Topics: {len(topic_refs)}",
        "",
        "## Layout",
        "",
        "- `chapters/chXX/`: 章と節 (`N.M...` タイトル)",
        "- `topics/<bucket>/`: 非章ページを文字種で分割",
        "- `indexes/`: 章索引、トピック索引、JSON索引",
    ]
    (OUT_DIR / "README.md").write_text("\n".join(readme_lines) + "\n", encoding="utf-8")

    # LLM quick guide
    llm_lines = [
        "MN-Core LLM Corpus",
        "",
        "Read order:",
        "1) indexes/chapter_index.md",
        "2) chapters/ch01 .. ch04",
        "3) indexes/topic_index.md",
        "",
        "Primary lookup:",
        "- by section number: chapters/chXX/section-<number>__*.md",
        "- by title: indexes/title_to_path.json",
        "- by page id: indexes/id_to_path.json",
        "",
        "Conventions:",
        "- each file has YAML frontmatter: title, id, created_unix, updated_unix, views",
        "- Cosense links are converted to [[Title]]",
        "- inline URL links stay as Markdown links or <URL>",
    ]
    (OUT_DIR / "LLM.txt").write_text("\n".join(llm_lines) + "\n", encoding="utf-8")

    dev_lines = [
        "# DEVELOPMENT",
        "",
        "## Regenerate",
        "",
        "```bash",
        "python docs/scripts/organize_mncore_docs.py",
        "```",
        "",
        "## Input/Output",
        "",
        "- Input: `docs/mncore.json` (Cosense JSON export)",
        "- Output root: `docs/mncore_llm`",
        "",
        "## Output Details",
        "",
        "- `chapters/chXX/`: chapter title page + numbered section pages",
        "- `topics/<bucket>/`: non-numbered pages",
        "- `indexes/chapter_index.md`: chapter tree",
        "- `indexes/topic_index.md`: topic files grouped by bucket",
        "- `indexes/title_to_path.json`: title -> [path]",
        "- `indexes/id_to_path.json`: page id -> path",
        "- `indexes/link_graph.json`: title -> referenced [[titles]]",
        "",
        "## Notes",
        "",
        "- File names include `__<id8>` to avoid collisions.",
        "- Section file names use `section-<number>` for stable numeric retrieval.",
    ]
    (OUT_DIR / "DEVELOPMENT.md").write_text("\n".join(dev_lines) + "\n", encoding="utf-8")

    indexes_dir = OUT_DIR / "indexes"
    indexes_dir.mkdir(parents=True, exist_ok=True)

    # Chapter index
    chapter_index_lines = ["# Chapter Index", ""]
    for ch in sorted(chapter_map):
        chapter_index_lines.append(f"## ch{ch:02d}")
        chapter_pages = chapter_map[ch]
        chapter_title_pages = [p for p in chapter_pages if p.section_no is None]
        section_pages = [p for p in chapter_pages if p.section_no is not None]
        for p in sorted(chapter_title_pages, key=lambda x: x.path.name):
            rel = p.path.relative_to(OUT_DIR).as_posix()
            chapter_index_lines.append(f"- [chapter] `{rel}` :: {p.title}")
        for p in sorted(section_pages, key=lambda x: section_sort_key(x.section_no or "999.999")):
            rel = p.path.relative_to(OUT_DIR).as_posix()
            chapter_index_lines.append(f"- [{p.section_no}] `{rel}` :: {p.title}")
        chapter_index_lines.append("")
    (indexes_dir / "chapter_index.md").write_text("\n".join(chapter_index_lines).rstrip() + "\n", encoding="utf-8")

    # Topic index
    topic_index_lines = ["# Topic Index", ""]
    bucket_map: dict[str, list[PageRef]] = {}
    for p in topic_refs:
        bucket = p.path.relative_to(OUT_DIR).parts[1]
        bucket_map.setdefault(bucket, []).append(p)

    for bucket in sorted(bucket_map):
        topic_index_lines.append(f"## {bucket}")
        for p in sorted(bucket_map[bucket], key=lambda x: x.title):
            rel = p.path.relative_to(OUT_DIR).as_posix()
            topic_index_lines.append(f"- `{rel}` :: {p.title}")
        topic_index_lines.append("")
    (indexes_dir / "topic_index.md").write_text("\n".join(topic_index_lines).rstrip() + "\n", encoding="utf-8")

    # JSON indexes
    (indexes_dir / "id_to_path.json").write_text(
        json.dumps(dict(sorted(id_to_path.items())), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    (indexes_dir / "title_to_path.json").write_text(
        json.dumps(dict(sorted(title_to_paths.items())), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    (indexes_dir / "link_graph.json").write_text(
        json.dumps(dict(sorted(link_graph.items())), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    index = {
        "source": str(SRC_JSON),
        "page_count": len(refs_sorted),
        "chapter_count": len(chapter_map),
        "topic_count": len(topic_refs),
        "pages": [
            {
                "title": r.title,
                "id": r.id_,
                "path": r.path.relative_to(OUT_DIR).as_posix(),
                "chapter": r.chapter_no,
                "section": r.section_no,
            }
            for r in refs_sorted
        ],
    }
    (OUT_DIR / "index.json").write_text(
        json.dumps(index, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
