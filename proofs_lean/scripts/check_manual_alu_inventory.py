"""Check the manual ALU opcode table against compiler and parser inventories.

This is a narrow inventory cross-check. It does not prove operand grammar,
assembler acceptance, or the completeness of the manual itself.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
MANUAL = REPO / "docs/mncore_llm/chapters/ch03/section-3.6.12__ALU命令式__66b35fff.md"


def main() -> None:
    source = MANUAL.read_text()
    try:
        table = source.split("table:表3.9", 1)[1].split("\n\n", 1)[0]
    except IndexError as error:
        raise SystemExit("manual ALU table 3.9 not found") from error
    manual_opcodes = {
        name
        for line in table.splitlines()
        for name in re.findall(r"\[\[([^]]+)\]\]", line.split("\t", 1)[0])
    }

    sys.path.insert(0, str(REPO))
    from mncompile.machine import ALU_OPS, alu_opcodes

    expected_manual = set(ALU_OPS) | {"zero", "imm"}
    if manual_opcodes != expected_manual:
        raise SystemExit(
            "manual/compiler ALU inventory drift: "
            f"missing in compiler={sorted(manual_opcodes - expected_manual)}, "
            f"missing in manual={sorted(expected_manual - manual_opcodes)}"
        )

    coverage = json.loads((ROOT / "coverage.json").read_text())
    candidates = {row["spelling"] for row in coverage["syntax_candidates"]}
    expanded = set(alu_opcodes())
    missing = expanded - candidates
    if missing:
        raise SystemExit(f"expanded manual ALU spellings absent from parser audit: {sorted(missing)}")

    print(
        f"PASS: {len(manual_opcodes)} manual ALU base opcodes match the compiler; "
        f"all {len(expanded)} allowed ALU spellings occur in parser-audited candidates."
    )


if __name__ == "__main__":
    main()
