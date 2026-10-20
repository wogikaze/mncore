#!/usr/bin/env python3

"""Remove plain ``nop`` lines that the official assembler does not require.

The fx_export scheduler emits conservative ``nop`` fills.  ``nop/3`` lines are
the inter-operation separators and are left alone; this tool only tries lines
that are exactly ``nop`` (optionally followed by a ``#`` comment).

A removal is kept only when ``assemble3`` still accepts the whole program, so
the result never introduces an assembler-visible hazard.  Run it after
regenerating a benchmark VSM:

    python3 tools/squeeze_nops.py viz/core/benchmarks/mnist_train_step.vsm
"""

import subprocess
import sys

ASSEMBLER = "judge/judge-py/mncore2_emuenv/assemble3"


def assembles(lines: list[str]) -> bool:
    text = "\n".join(lines) + "\n"
    proc = subprocess.run(
        [ASSEMBLER, "--instruction-mode", "flat"],
        input=text,
        text=True,
        capture_output=True,
    )
    return proc.returncode == 0


def squeeze(path: str) -> int:
    with open(path) as f:
        lines = f.read().splitlines()

    removed = 0
    while True:
        progress = False
        for i in range(len(lines) - 1, -1, -1):
            stripped = lines[i].strip()
            if stripped != "nop":
                continue
            del lines[i]
            if assembles(lines):
                removed += 1
                progress = True
            else:
                lines.insert(i, "nop")
        if not progress:
            break

    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    return removed


if __name__ == "__main__":
    target = sys.argv[1] if len(sys.argv) > 1 else "viz/core/benchmarks/mnist_train_step.vsm"
    n = squeeze(target)
    print(f"removed {n} nop lines from {target}")
