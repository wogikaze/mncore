"""Benchmark-side access to problem statements and official testcases.

The compiler never imports this module. The harness reads the tensor
declarations of a problem statement (the contract a human would read) and the
official testcases used for judging.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from ..layout import Contract, TensorSpec, parse_tensor

ROOT = Path(__file__).resolve().parents[2]
PROBLEMS = ROOT / "problems"


def _number(text: str):
    text = text.strip()
    if m := re.fullmatch(r"(-?\d+)\^\{(\d+)\}", text):
        return int(m[1]) ** int(m[2])
    if m := re.fullmatch(r"(-?)(\d+)\^\{(\d+)\}\s*-\s*(\d+)", text):
        return (-1 if m[1] else 1) * int(m[2]) ** int(m[3]) - int(m[4])
    if m := re.fullmatch(r"10\^\{(-?\d+)\}", text):
        return 10.0 ** int(m[1])
    value = float(text)
    return int(value) if value.is_integer() and "." not in text and "e" not in text.lower() else value


_LINE = re.compile(
    r"^\*\s*(?:\\\((?P<name>[A-Za-z]+)\\\))?\s*"
    r"(?:\(\\\((?P<low>[^ ]+)\s*\\le\s*[^\\]*?\\le\s*(?P<high>.+?)\\\)\))?\s*:?\s*"
    r"(?P<dtype>[A-Za-z]+)\s*`(?P<mem>\$[^`]+)`,\s*`(?P<layout>[^`]+)`"
    r"(?:\s*/\s*\\\((?P<atol>[^\\]+)\\\)\s*以下の絶対誤差が許容されます)?"
)


def parse_spec_line(line: str, default_name: str) -> TensorSpec:
    m = _LINE.match(line.strip())
    if not m:
        raise ValueError(f"Unrecognized tensor declaration: {line}")
    low = _number(m["low"]) if m["low"] else None
    high = _number(m["high"]) if m["high"] else None
    atol = float(_number(m["atol"])) if m["atol"] else 0.0
    return parse_tensor(
        m["name"] or default_name,
        m["dtype"],
        m["mem"],
        m["layout"],
        low=low,
        high=high,
        atol=atol,
    )


def statement_contract(problem_md: str) -> Contract:
    inputs, outputs = [], []
    section = None
    for raw in problem_md.splitlines():
        line = raw.strip()
        if line.startswith("## "):
            section = line[3:].strip()
            continue
        if section not in ("Inputs", "Outputs") or not line.startswith("* "):
            continue
        if "`$" not in line:
            continue
        target = inputs if section == "Inputs" else outputs
        name = f"{'in' if section == 'Inputs' else 'out'}{len(target)}"
        spec = parse_spec_line(line, name)
        if any(s.name == spec.name for s in target):
            continue  # some statements repeat the declarations
        target.append(spec)
    return Contract(inputs, outputs)


@dataclass
class Problem:
    directory: Path
    slug: str
    statement: str
    contract: Contract
    testcases: list[Path]
    reference: dict = field(default_factory=dict)

    @property
    def name(self) -> str:
        return self.directory.name


def load(directory: Path) -> Problem:
    md = (directory / "problem.md").read_text()
    slug_match = re.search(r"^slug:\s*(\S+)", md, re.M)
    slug = slug_match[1] if slug_match else directory.name
    reference = {}
    if (directory / "answer.json").exists():
        reference = json.loads((directory / "answer.json").read_text())
    testcases = sorted(directory.glob("testcase*.vsm"))
    return Problem(directory, slug, md, statement_contract(md), testcases, reference)


def challenge_problems() -> list[Problem]:
    dirs = sorted((PROBLEMS / "challenge").glob("[0-9]*.*"), key=lambda p: int(p.name.split(".")[0]))
    return [load(d) for d in dirs]


def mnist_problems() -> list[Problem]:
    dirs = sorted(PROBLEMS.glob("[0-9]*.*"), key=lambda p: int(p.name.split(".")[0]))
    return [load(d) for d in dirs if (d / "problem.md").exists()]


CONSTRAINTS = ROOT / "mncompile" / "benchmarks" / "constraints.json"


def contract_for(problem: Problem) -> Contract:
    """The statement contract plus the stated additional constraints."""
    import dataclasses

    key = ("challenge/" if problem.directory.parent.name == "challenge" else "mnist/") + problem.slug
    extra = json.loads(CONSTRAINTS.read_text()).get(key, {})
    def patch(spec):
        if spec.name in extra:
            return dataclasses.replace(spec, **extra[spec.name])
        return spec
    c = problem.contract
    return Contract([patch(s) for s in c.inputs], [patch(s) for s in c.outputs], dict(c.notes))


def kernel_source(problem: Problem) -> str:
    folder = "challenge" if problem.directory.parent.name == "challenge" else "mnist"
    return (ROOT / "mncompile" / "benchmarks" / folder / f"{problem.slug}.py").read_text()
