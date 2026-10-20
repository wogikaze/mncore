#!/usr/bin/env python3

"""Remove ``nop`` / ``nop/<n>`` lines while the simulator still matches.

Unlike ``squeeze_nops.py`` (which only asks the assembler), this runs the
program on the prepared MNIST step with ``cpu_step`` and keeps a removal only
when the whole DRAM image is unchanged.  It removes separators that the
assembler accepts but the timing model does not.

    python3 tools/squeeze_nops_sim.py <program.vsm> [data_dir]
"""

import shutil
import subprocess
import sys
import tempfile

ASSEMBLER = "judge/judge-py/mncore2_emuenv/assemble3"
SIMULATOR = "./viz/core/target/release/cpu_step"
DATA = "research/experiments/mnist-gpu"


def assembles(text: str) -> bool:
    p = subprocess.run([ASSEMBLER, "--instruction-mode", "flat"], input=text,
                       text=True, capture_output=True)
    return p.returncode == 0


def run(text: str, tmp: str) -> bytes | None:
    path = f"{tmp}/try.vsm"
    open(path, "w").write(text)
    p = subprocess.run([SIMULATOR, DATA, path], capture_output=True, text=True)
    if p.returncode != 0:
        return None
    return open(f"{DATA}/cpu_final.bin", "rb").read()


def main(path: str) -> None:
    lines = open(path).read().splitlines()
    tmp = tempfile.mkdtemp()
    baseline = None
    try:
        baseline = run("\n".join(lines) + "\n", tmp)
        if baseline is None:
            raise SystemExit("the input program does not run")
        removed = 0
        for _ in range(3):
            progress = False
            for i in range(len(lines) - 1, -1, -1):
                s = lines[i].strip()
                if not (s == "nop" or (s.startswith("nop/") and s[4:].isdigit())):
                    continue
                cand = lines[:i] + lines[i + 1:]
                text = "\n".join(cand) + "\n"
                if assembles(text) and run(text, tmp) == baseline:
                    lines = cand
                    removed += 1
                    progress = True
            if not progress:
                break
        open(path, "w").write("\n".join(lines) + "\n")
        print(f"removed {removed} nop lines from {path} ({len(lines)} left)")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "viz/core/benchmarks/mnist_train_step.vsm")
