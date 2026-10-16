"""Check proof sources, catalog integrity, Lean kernel dependencies and build isolation."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
from pathlib import Path

import catalog
import check_issue_mirror

ROOT = catalog.ROOT
BANNED = {"sorry", "admit", "axiom", "unsafe", "native_decide", "implemented_by"}
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def code_only(text: str) -> str:
    """Remove Lean strings and nested comments before checking executable tokens."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = end if end >= 0 else len(text)
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean comment")
    return "".join(out)


def validate_source(text: str, filename: str) -> None:
    code = code_only(text)
    forbidden = set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", code)) & BANNED
    if forbidden:
        raise ValueError(f"{filename}: untrusted proof escape: {sorted(forbidden)}")
    if "skipKernelTC" in code or "optimalProven" in code:
        raise ValueError(f"{filename}: kernel bypass or evidence-free promotion")
    for imports in re.findall(r"^import\s+([^\n]+)", code, re.M):
        for module in imports.split():
            if module == "Std" or (module == "Lean" and filename == "Check.lean"):
                continue
            if module == "ProofsLean" or module.startswith("ProofsLean."):
                if (ROOT / (module.replace(".", "/") + ".lean")).exists():
                    continue
            raise ValueError(f"{filename}: unreviewed/stale import {module}")


def validate_axioms(output: str) -> None:
    records = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    no_axioms = re.findall(r"does not depend on any axioms", output)
    if len(records) + len(no_axioms) != 186:
        raise ValueError(f"missing kernel dependency reports: {output}")
    for record in records:
        names = {x.strip() for x in record.split(",") if x.strip()}
        if names - ALLOWED_AXIOMS:
            raise ValueError(f"untrusted kernel dependencies: {names - ALLOWED_AXIOMS}")


def validate_import_closure() -> None:
    reachable, pending = set(), ["ProofsLean"]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        for imports in re.findall(r"^import\s+([^\n]+)", code_only(path.read_text()), re.M):
            pending.extend(m for m in imports.split() if m.startswith("ProofsLean."))
    actual = {"ProofsLean"} | {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
                              for p in (ROOT / "ProofsLean").rglob("*.lean")}
    if actual != reachable:
        raise ValueError(f"unbuilt or missing proof sources: {actual ^ reachable}")


def main() -> None:
    catalog.archive_valid()
    check_issue_mirror.validate()
    for name, data in (("audit.json", catalog.problem_catalog()), ("coverage.json", catalog.coverage_catalog())):
        if (ROOT / name).read_text() != catalog.render(data):
            raise SystemExit(f"{name} is stale or contains unsupported claims; regenerate it")
    sources = [*sorted(ROOT.glob("*.lean")), *sorted((ROOT / "ProofsLean").rglob("*.lean"))]
    for path in sources:
        validate_source(path.read_text(), str(path.relative_to(ROOT)))
    validate_import_closure()
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    for args in ([lake, "clean"], [lake, "build", "proofs_lean", "alu_probe", "untyped_probe", "memory_probe", "dynamic_address_probe", "mask_probe", "forwarding_probe", "lbf_encoded_probe"], [lake, "env", "lean", "Check.lean"]):
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=300)
        if result.returncode:
            raise SystemExit(result.stdout + result.stderr)
        if args[-1] == "Check.lean":
            validate_axioms(result.stdout + result.stderr)
            if not re.search(r"AUDIT_DECLARATIONS: [1-9][0-9]*", result.stdout + result.stderr):
                raise SystemExit("missing audit of all project declarations")
        print(result.stdout.strip())
    print("PASS: semantic framework and restricted-model proofs. MN-Core full-ISA proofs: 0/73.")


if __name__ == "__main__":
    main()
