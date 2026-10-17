#!/usr/bin/env python3
"""Check Lean singleFma against Rust vectors and optionally official gpfn3.

Rust generates expected words with the simulator's integer-only model. Lean
then proves every concrete equation by kernel reduction (`by decide`). The
separate `difftest_mau` run checks that same Rust model against gpfn3.
"""

from __future__ import annotations

import argparse
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT.parent / "viz" / "core"


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--vectors", type=int, default=256)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--gpfn-runs", type=int, default=0,
                        help="also run official gpfn3 differential tests; 35 gives 573440 values")
    args = parser.parse_args()

    if args.gpfn_runs:
        output = run(["cargo", "run", "--release", "--bin", "difftest_mau", "--",
                      "fvfma", str(args.gpfn_runs), str(args.seed)], CORE)
        print(output.strip())

    vectors = run(["cargo", "run", "--quiet", "--release", "--bin",
                   "fma_kernel_vectors", "--", str(args.vectors), str(args.seed)], CORE)
    equations = []
    for line_number, line in enumerate(vectors.splitlines(), 1):
        fields = line.split()
        if len(fields) != 4:
            raise SystemExit(f"malformed Rust vector line {line_number}: {line!r}")
        a, b, c, expected = (int(field, 16) for field in fields)
        equations.append(
            "example : ProofsLean.MNCore.SingleFMA.singleFma "
            f"(BitVec.ofNat 32 {a}) (BitVec.ofNat 32 {b}) "
            f"(BitVec.ofNat 32 {c}) = BitVec.ofNat 32 {expected} := by decide"
        )
    if len(equations) != args.vectors:
        raise SystemExit(f"expected {args.vectors} Rust vectors, got {len(equations)}")

    source = "import ProofsLean.SingleFMA\n\n" + "\n".join(equations) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT,
                                     encoding="utf-8", delete=False) as generated:
        generated.write(source)
        generated_path = Path(generated.name)
    try:
        run(["lake", "env", "lean", str(generated_path)], ROOT)
    finally:
        generated_path.unlink(missing_ok=True)
    print(f"Lean kernel checked {len(equations)} deterministic FMA vectors (seed {args.seed})")


if __name__ == "__main__":
    main()
