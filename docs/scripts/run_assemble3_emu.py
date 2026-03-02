#!/usr/bin/env python3
"""Run a solution by directly invoking assemble3 and gpfn3_package_main.

This script expands a testcase template that contains
"# ======= YOUR VSM WILL BE INSERTED HERE =======".
"""

from __future__ import annotations

import argparse
import subprocess
import tempfile
import shutil
from pathlib import Path

MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="
ASSEMBLER = Path("judge/judge-py/mncore2_emuenv/assemble3")
EMULATOR = Path("judge/judge-py/mncore2_emuenv/gpfn3_package_main")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser()
    p.add_argument("--testcase", required=True, help="Path to testcase template vsm")
    p.add_argument("--solution", required=True, help="Path to solution vsm")
    p.add_argument("--keep-temp", action="store_true", help="Keep temp directory and print its path")
    return p.parse_args()


def run_cmd(cmd: list[str], cwd: Path) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout, proc.stderr


def main() -> None:
    args = parse_args()
    cwd = Path.cwd()

    testcase = Path(args.testcase)
    solution = Path(args.solution)
    if not testcase.exists() or not solution.exists():
        raise SystemExit("testcase or solution does not exist")

    with tempfile.TemporaryDirectory(prefix="mncore-exp-") as td:
        tdir = Path(td)
        full_vsm = tdir / "full.vsm"
        full_asm = tdir / "full.asm"

        merged = testcase.read_text(encoding="utf-8").replace(MARKER, solution.read_text(encoding="utf-8"))
        full_vsm.write_text(merged, encoding="utf-8")

        a_rc, a_out, a_err = run_cmd(
            [str(ASSEMBLER), "--instruction-mode", "flat", str(full_vsm), "--output-file", str(full_asm)],
            cwd,
        )
        print(f"assemble3 rc={a_rc}")
        if a_out.strip():
            print("[assemble3 stdout]")
            print(a_out)
        if a_err.strip():
            print("[assemble3 stderr]")
            print(a_err)

        if a_rc == 0:
            e_rc, e_out, e_err = run_cmd(
                [str(EMULATOR), "-i", str(full_asm), "--offchip-memory-init", "zero"],
                cwd,
            )
            print(f"gpfn3_package_main rc={e_rc}")
            if e_out.strip():
                print("[emulator stdout]")
                print(e_out)
            if e_err.strip():
                print("[emulator stderr] (tail 40 lines)")
                tail = "\n".join(e_err.splitlines()[-40:])
                print(tail)

        if args.keep_temp:
            keep = cwd / "tmp_mncore_exp"
            if keep.exists():
                shutil.rmtree(keep)
            shutil.copytree(tdir, keep)
            print(f"temp copied to: {keep}")


if __name__ == "__main__":
    main()
