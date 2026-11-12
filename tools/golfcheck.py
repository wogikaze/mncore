#!/usr/bin/env python3
"""Fast candidate checker for any problem: native simulator, output compared with the recorded answer.

    python3 tools/golfcheck.py <problem> candidate.vsm [...]
    e.g. python3 tools/golfcheck.py challenge/19.inversion /tmp/c.vsm

The problem's testcase is split at the insertion marker. The recorded `answer.vsm` is run once and every
value the testcase dumps (`d get*` lines after the marker) is kept as the reference; a candidate passes when
the official assembler accepts it (this includes the hazard checker, which the native simulator does not
model) and it dumps exactly the same values. This is stricter than the judge for problems with an error
tolerance (a different approximation is rejected here), so use `run_problem.py` to confirm such candidates.
Exact agreement with the native simulator is not acceptance either: confirm with the official judge.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
sys.path.insert(0, str(ROOT))


@dataclass
class Result:
    ok: bool
    words: int
    detail: str

    def __str__(self) -> str:
        return f"{'OK' if self.ok else 'FAIL'} words={self.words} {self.detail}".rstrip()


class Checker:
    def __init__(self, problem: str, reference: str | None = None):
        from mncompile.sim import simulator

        self.dir = ROOT / "problems" / problem
        pre, suf = (self.dir / "testcase.vsm").read_text(encoding="utf-8").split(MARKER, 1)
        suf = "\n".join(l.split("#")[0].rstrip() for l in suf.splitlines() if l.split("#")[0].strip()) + "\n"
        self.key = "golf:" + problem
        self.sim = simulator()
        self.sim.register(self.key + ":pre", pre)
        self.sim.register(self.key + ":suf", suf)
        ref = reference if reference is not None else (self.dir / "answer.vsm").read_text(encoding="utf-8")
        run = self._run(ref)
        if run.error or not run.dump:
            raise SystemExit(f"reference does not run: {run.error}")
        self.expected = run.dump
        self.reference_words = run.words

    def _run(self, text: str):
        return self.sim.run(text, prefix_key=self.key + ":pre", suffix_key=self.key + ":suf")

    def check(self, text: str) -> Result:
        from mncompile.sim import assembler

        asm = assembler().assemble(text)
        if not asm.ok:
            return Result(False, asm.words, "assembler: " + (asm.error.splitlines()[-1].strip() if asm.error else "failed"))
        run = self._run(text)
        if run.error:
            return Result(False, run.words or 0, f"{run.part}:{run.line}: {run.error}")
        if run.dump.keys() != self.expected.keys():
            return Result(False, run.words or 0, f"dumped {len(run.dump)}/{len(self.expected)} values")
        bad = sum(1 for k, v in self.expected.items() if run.dump[k] != v)
        return Result(bad == 0 and bool(run.words), run.words or 0, f"mismatches={bad}" if bad else "")


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__)
        return 2
    checker = Checker(argv[1])
    worst = 0
    for name in argv[2:]:
        result = checker.check(Path(name).read_text(encoding="utf-8"))
        print(f"{name}: {result}")
        worst = max(worst, 0 if result.ok else 1)
    return worst


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
