#!/usr/bin/env python3
"""Fast FizzBuzz candidate checker (native simulator + official testcase).

Usage:
    python3 tools/fbcheck.py file.vsm [more.vsm ...]
    python3 tools/fbcheck.py --quiet file.vsm        # print only a summary line

The check uses the official testcase's own expectation: the 4096 `d getd $d<i>n0`
lines carry the expected bytes. A candidate is accepted here when the native
simulator reproduces all of them; `tools/fbverify.py` re-checks a candidate
with the official assembler and emulator and is the authoritative gate.
"""

from __future__ import annotations

import codecs
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TESTCASE = ROOT / "problems/challenge/20.fizzbuzz/testcase.vsm"
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="

_sim = None
_expected: dict[int, bytes] = {}
_pre = ""
_suf = ""


@dataclass
class Result:
    ok: bool
    words: int
    lines: int
    mismatches: int | None
    error: str | None

    def __str__(self) -> str:
        if self.error:
            return f"ERROR words={self.words} {self.error}"
        return (
            f"{'OK' if self.ok else 'FAIL'} words={self.words} lines={self.lines} "
            f"mismatches={self.mismatches}"
        )


def init() -> None:
    global _sim, _expected, _pre, _suf
    if _sim is not None:
        return
    sys.path.insert(0, str(ROOT))
    from mncompile.sim import simulator

    testcase = TESTCASE.read_text(encoding="utf-8")
    _pre, _suf = testcase.split(MARKER, 1)
    _expected = {}
    for match in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="([^"]*)"', testcase):
        _expected[int(match.group(1))] = codecs.decode(
            match.group(2), "unicode_escape"
        ).encode("latin-1")
    # Only the dumps matter; drop the explanatory comments from the suffix.
    _suf = "\n".join(
        line.split("#")[0].rstrip()
        for line in _suf.splitlines()
        if line.split("#")[0].strip()
    ) + "\n"
    _sim = simulator()
    _sim.register("fb_pre", _pre)
    _sim.register("fb_suf", _suf)


def count_lines(text: str) -> int:
    return sum(1 for line in text.splitlines() if line.split("#")[0].strip())


def check(text: str) -> Result:
    init()
    assert _sim is not None
    run = _sim.run(text, prefix_key="fb_pre", suffix_key="fb_suf")
    lines = count_lines(text)
    if run.error:
        return Result(False, run.words or 0, lines, None, f"{run.part}:{run.line}: {run.error}")
    mismatches = 0
    seen = 0
    for (mem, _pe, addr), value in run.dump.items():
        if mem != "DRAM":
            continue
        expected = _expected.get(addr)
        if expected is None:
            continue
        seen += 1
        got = value.to_bytes(8, "big")
        if got[: len(expected)] != expected:
            mismatches += 1
    if seen != len(_expected):
        return Result(False, run.words or 0, lines, mismatches,
                      f"only {seen}/{len(_expected)} dumps observed")
    return Result(mismatches == 0 and (run.words or 0) > 0, run.words or 0, lines, mismatches, None)


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if not a.startswith("-")]
    quiet = "--quiet" in argv or "-q" in argv
    if not args:
        print(__doc__)
        return 2
    worst = 0
    for name in args:
        result = check(Path(name).read_text(encoding="utf-8"))
        if quiet:
            print(f"{result.words:4d} {result} {name}")
        else:
            print(f"{name}: {result}")
        worst = max(worst, 0 if result.ok else 1)
    return worst


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
