"""Compare Lean matrix block-float dot/FMA arithmetic with the Rust simulator."""
from __future__ import annotations

import hashlib
import json
import random
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
CORE = REPO / "viz/core"
EVIDENCE = ROOT / "evidence/matrix-bf"

FORMATS = {
    "d": (11, 52, 1023, 4, 52),
    "f": (8, 23, 127, 4, 23),
    "g": (8, 23, 127, 8, 18),
    "h": (6, 9, 31, 16, 9),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def raw_value(rng: random.Random, code: str, exponent: int | None = None) -> int:
    code = "f" if code == "s" else code
    exp_bits, mantissa_bits, bias, _, _ = FORMATS[code]
    sign = rng.randrange(2)
    if exponent is None:
        exponent = rng.choice([0, *range(max(1, bias - 12), min((1 << exp_bits) - 1, bias + 13))])
    mantissa = rng.getrandbits(mantissa_bits)
    return (sign << (exp_bits + mantissa_bits)) | (exponent << mantissa_bits) | mantissa


def vector_lines() -> list[str]:
    rng = random.Random(0x4D41554246)
    rows: list[str] = []
    for code, (exp_bits, mantissa_bits, bias, lanes, kept) in FORMATS.items():
        outputs = {"d": ["d", "s"], "f": ["s"], "g": ["s"], "h": ["s", "h"]}[code]
        exp_max = (1 << exp_bits) - 1
        for output in outputs:
            for _ in range(96):
                left_common = rng.randrange(max(1, bias - 10), min(exp_max - 1, bias + 11))
                right_common = rng.randrange(max(1, bias - 10), min(exp_max - 1, bias + 11))
                left = [raw_value(rng, code, 0 if rng.randrange(12) == 0 else max(1, left_common - rng.randrange(5)))
                        for _ in range(lanes)]
                right = [raw_value(rng, code, 0 if rng.randrange(12) == 0 else max(1, right_common - rng.randrange(5)))
                         for _ in range(lanes)]
                acc_code = "d" if code == "d" else "s"
                _, _, acc_bias, _, _ = FORMATS[acc_code if acc_code in FORMATS else "f"]
                accumulator = raw_value(rng, acc_code, rng.choice([0, *range(max(1, acc_bias - 8), acc_bias + 9)]))
                rows.append("\t".join((code, output, str(kept), acc_code, str(accumulator),
                                       ",".join(map(str, left)), ",".join(map(str, right)))))
    # Include identity, zero-dot, and exact cancellation-oriented boundary vectors.
    for code, (_, _, bias, lanes, kept) in FORMATS.items():
        output = "d" if code == "d" else "s"
        one_exp_bits, one_mantissa_bits, _, _, _ = FORMATS[code]
        one = (bias << one_mantissa_bits)
        zero = "0"
        left = ",".join([str(one)] * lanes)
        rows.append("\t".join((code, output, str(kept), "d" if code == "d" else "s", zero,
                               left, left)))
        rows.append("\t".join((code, output, str(kept), "d" if code == "d" else "s", zero,
                               ",".join([zero] * lanes), left)))
    return rows


def main() -> None:
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    vector_rows = vector_lines()
    vectors = "\n".join(vector_rows) + "\n"
    lean_build = subprocess.run([lake, "build", "matrix_bf_probe"], cwd=ROOT,
                                capture_output=True, text=True, timeout=300)
    if lean_build.returncode:
        raise SystemExit(lean_build.stdout + lean_build.stderr)
    rust_build = subprocess.run(["cargo", "build", "--bin", "matrix_bf_probe"], cwd=CORE,
                                capture_output=True, text=True, timeout=300)
    if rust_build.returncode:
        raise SystemExit(rust_build.stdout + rust_build.stderr)
    lean = subprocess.run([str(ROOT / ".lake/build/bin/matrix_bf_probe")], input=vectors,
                          capture_output=True, text=True, check=True, timeout=120)
    rust = subprocess.run([str(CORE / "target/debug/matrix_bf_probe")], input=vectors,
                          capture_output=True, text=True, check=True, timeout=120)
    expected, actual = lean.stdout.splitlines(), rust.stdout.splitlines()
    if len(expected) != len(vector_rows) or len(actual) != len(expected):
        raise SystemExit(f"wrong output count: vectors={len(vector_rows)}, Lean={len(expected)}, Rust={len(actual)}")
    differences = [
        {"index": i, "vector": row, "lean": left, "rust": right}
        for i, (row, left, right) in enumerate(zip(vectors.splitlines(), expected, actual))
        if left != right
    ]
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / "vectors.tsv").write_text(vectors)
    sources = [ROOT / "ProofsLean/RRN.lean", ROOT / "MatrixBFProbe.lean", ROOT / "lakefile.toml",
               Path(__file__).resolve(), CORE / "src/float.rs", CORE / "src/bin/matrix_bf_probe.rs",
               CORE / "Cargo.toml"]
    report = {
        "schema_version": 1,
        "evidence_kind": "finite_matrix_block_float_dot_fma_differential",
        "reference": "viz/core Rust float::bf_dot + mat_fma",
        "cases": len(expected),
        "matched": len(expected) - len(differences),
        "differences": differences,
        "formats": {"d": "double, dot width 4, kept 52", "f": "single, dot width 4, kept 23",
                    "g": "pseudo-single, dot width 8, kept 18", "h": "half, dot width 16, kept 9"},
        "outputs": "D rounded/unrounded and H rounded/unrounded are both represented; F/G produce single.",
        "scope_limit": "Arithmetic fragment only: does not compare parsed operands, matrix layout, MAB row masks, PE bus packing, flags, poison, issue timing, or whole-machine state transitions.",
        "sources": {path.relative_to(REPO).as_posix(): sha(path) for path in sources},
        "vectors_sha256": hashlib.sha256(vectors.encode()).hexdigest(),
        "proves_universal_conformance": False,
        "proves_isa_completeness": False,
    }
    (EVIDENCE / "reference.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": report["cases"], "matched": report["matched"],
                      "differences": len(differences)}))
    if differences:
        raise SystemExit("matrix block-float Lean/Rust differential found mismatches")


if __name__ == "__main__":
    main()
