#!/usr/bin/env python3
"""Score every candidate VSM under research/experiments and print the ranking.

    python3 tools/scan.py [--all]

Only candidates that assemble are scored with the fast simulator. `--all` also
lists failures with their first error.
"""
from __future__ import annotations
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fbasm  # noqa: E402
import fbcheck  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


def main(argv: list[str]) -> int:
    show_all = "--all" in argv
    rows = []
    for path in sorted(ROOT.glob("research/experiments/**/*.vsm")):
        text = path.read_text(encoding="utf-8")
        ok, words, error = fbasm.assemble(text)
        if not ok:
            if show_all:
                rows.append((10**6, f"ASM-FAIL {path.relative_to(ROOT)}: {error[-70:]}"))
            continue
        result = fbcheck.check(text)
        if result.ok:
            rows.append((result.words, f"OK        {result.words:4d} {path.relative_to(ROOT)}"))
        elif show_all:
            rows.append((10**5 - (result.mismatches or 0), f"WRONG     {result.words:4d} mism={result.mismatches} {path.relative_to(ROOT)}"))
    for _, line in sorted(rows):
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
