import json
import math
import os
import random
import re
import shutil
import struct
import subprocess
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

from mncompile.compiler import CompileError, compile_source, optimize, parse_source

NEAR_IDENTITY = "def kernel(x):\n    return x + 0.001 * x * x\n"
ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")


@unittest.skipUnless(shutil.which("opt"), "LLVM opt is required")
class CompilerTests(unittest.TestCase):
    def test_error_budget_changes_selected_program(self):
        tight = compile_source(NEAR_IDENTITY, domain=(-1, 1), atol=1e-5)
        loose = compile_source(NEAR_IDENTITY, domain=(-1, 1), atol=0.002)
        self.assertGreater(tight.report["lines"], loose.report["lines"])
        self.assertEqual(loose.vsm, "fpassa $lm0v $ln0v\n")
        self.assertLessEqual(Q(tight.report["error_bound"]), Q(1e-5))
        self.assertEqual(Q(loose.report["error_bound"]), Q(0.001))

    def test_domain_changes_allowed_approximation(self):
        small = compile_source(NEAR_IDENTITY, domain=(-1, 1), atol=0.002)
        large = compile_source(NEAR_IDENTITY, domain=(-2, 2), atol=0.002)
        self.assertEqual(small.report["lines"], 1)
        self.assertGreater(large.report["lines"], 1)

    def test_no_silent_fallback_for_impossible_budget(self):
        with self.assertRaisesRegex(CompileError, "No candidate meets"):
            compile_source(NEAR_IDENTITY, domain=(-1, 1), atol=0)

    def test_exact_identity_and_float_copy_chunks(self):
        result = compile_source(
            "def f(x):\n    return x\n", domain=(-10, 10), atol=0, words=16
        )
        self.assertEqual(Q(result.report["error_bound"]), 0)
        self.assertEqual(result.report["lines"], 2)
        self.assertIn("$lm8v $ln8v", result.vsm)

    def test_llvm_cse_is_consumed_by_backend(self):
        result = compile_source(
            "def f(x):\n    a = x*x\n    return a+a\n", domain=(-1, 1), atol=1e-4
        )
        self.assertEqual(result.vsm.count("fvmul"), 1)
        self.assertIn("define double @kernel", result.llvm_ir)
        self.assertFalse(result.report["fast_math"])

    def test_coefficient_is_hoisted_across_chunks(self):
        result = compile_source(
            "def f(x):\n    return x*7.0\n", domain=(-512, 512), atol=0.001, words=32
        )
        self.assertEqual(result.vsm.count("imm"), 1)
        self.assertEqual(result.report["lines"], 5)

    def test_llvm_constant_folding_is_included_in_bound(self):
        _, expr = parse_source("def f(x):\n    return x + (0.1 + 0.2)\n")
        llvm, result = optimize(expr, "opt")
        # LLVM folds in binary64, while the reference polynomial uses rational
        # arithmetic on the source literals. Their difference must be retained.
        self.assertNotEqual(expr.polynomial(), result.polynomial())
        self.assertNotIn("fast ", llvm)

    def test_rejects_invalid_contracts_and_unsupported_source(self):
        for domain, error in [
            ((1, -1), 0.1),
            ((0, math.inf), 1),
            ((-1, 1), -1),
            ((0, 1), math.nan),
        ]:
            with (
                self.subTest(domain=domain, error=error),
                self.assertRaises(CompileError),
            ):
                compile_source(NEAR_IDENTITY, domain=domain, atol=error)
        for source in [
            "def f(x):\n    return __import__('os')\n",
            "def f(x):\n    return x/2\n",
            "def f(x):\n    return x**17\n",
        ]:
            with self.subTest(source=source), self.assertRaises(CompileError):
                compile_source(source, domain=(-1, 1), atol=0.1)

    def test_overflow_is_not_certified(self):
        with self.assertRaisesRegex(CompileError, "No candidate meets"):
            compile_source("def f(x):\n    return x*x\n", domain=(1e30, 1e31), atol=1)

    def test_artifacts_record_model_scope_and_candidates(self):
        result = compile_source(NEAR_IDENTITY, domain=(-1, 1), atol=0.002)
        with tempfile.TemporaryDirectory() as directory:
            result.write(directory)
            report = json.loads((Path(directory) / "report.json").read_text())
            self.assertIn("conditional", report["bound_kind"])
            self.assertIn("enumerated", report["optimality"])
            self.assertGreater(len(report["candidates"]), 1)


@unittest.skipUnless(
    ASSEMBLER and EMULATOR and shutil.which("opt"),
    "Set MNCORE_ASSEMBLER and MNCORE_EMULATOR",
)
class OfficialEmulatorTests(unittest.TestCase):
    def emulate(self, compiled, samples):
        payload = "".join(struct.pack(">f", value).hex() for value in samples)
        chunks = len(samples) // 8
        source = (
            f"d set $lm0p0 {len(samples) // 2} {payload}\n"
            + compiled.vsm
            + "nop\nnop\n"
        )
        source += f"d getd $ln0n0c0b0m0p0 {len(samples) // 2}\n"
        assembly = subprocess.run(
            [ASSEMBLER, "--instruction-mode", "flat"],
            input=source,
            text=True,
            capture_output=True,
            check=True,
        )
        process = subprocess.run(
            [EMULATOR, "--offchip-memory-init", "zero"],
            input=assembly.stdout,
            text=True,
            capture_output=True,
            check=True,
        )
        payloads = re.findall(r"DEBUG-LM1[^\n]*\(0x([0-9a-fA-F]{16})\)", process.stderr)
        values = [
            value
            for item in payloads
            for value in struct.unpack(">ff", bytes.fromhex(item))
        ]
        self.assertEqual(len(values), chunks * 8, process.stderr[:2000])
        return values

    def test_tight_and_loose_bounds_against_actual_machine(self):
        rng = random.Random(42)
        samples = [-1.0, 1.0, 0.0, -0.0, 2**-126, -(2**-126), 0.5, -0.5]
        samples += [
            struct.unpack(">f", struct.pack(">f", rng.uniform(-1, 1)))[0]
            for _ in range(56)
        ]
        for budget in (1e-5, 0.002):
            compiled = compile_source(
                NEAR_IDENTITY,
                domain=(-1, 1),
                atol=budget,
                words=len(samples),
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["cost_kind"], "assembled j+m words")
            actual = self.emulate(compiled, samples)
            for x, y in zip(samples, actual):
                reference = Q(x) + Q(0.001) * Q(x) ** 2
                self.assertLessEqual(
                    abs(Q(y) - reference), Q(compiled.report["error_bound"])
                )

    def test_multiply_subtract_and_constant_lowering(self):
        samples = [-1.0, 1.0, 0.0, 0.25, -0.25, 0.5, -0.5, 0.75]
        for expression in ("7*x", "x*x - 0.25", "0.3", "-x"):
            source = f"def f(x):\n    return {expression}\n"
            _, original = parse_source(source)
            compiled = compile_source(
                source, domain=(-1, 1), atol=1e-4, assembler=ASSEMBLER
            )
            actual = self.emulate(compiled, samples)
            for x, y in zip(samples, actual):
                p = original.polynomial()
                reference = sum((c * Q(x) ** i for i, c in enumerate(p)), Q(0))
                self.assertLessEqual(
                    abs(Q(y) - reference), Q(compiled.report["error_bound"])
                )


if __name__ == "__main__":
    unittest.main()
