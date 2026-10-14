import os
import random
import re
import shutil
import struct
import subprocess
import unittest
from fractions import Fraction as Q
from pathlib import Path

from mncompile import Tensor, compile_float_map

SOURCE = (Path(__file__).parent / "benchmarks/challenge/mul2.py").read_text()
ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")


def half_value(bits):
    exponent, mantissa = (bits >> 9) & 63, bits & 511
    if exponent == 0:
        return Q(0)
    return (-1 if bits & 0x8000 else 1) * Q(512 + mantissa) * Q(2) ** (exponent - 40)


@unittest.skipUnless(shutil.which("opt"), "LLVM opt is required")
class FloatMapTests(unittest.TestCase):
    def test_error_budget_controls_half_opcode_selection(self):
        source = Tensor("h16", "m", 0, 192, -1, 1)
        out = Tensor("h16", "n", 0, 192, -2, 2)
        strict = compile_float_map(SOURCE, inputs={"x": source}, output=out, atol=0)
        loose = compile_float_map(SOURCE, inputs={"x": source}, output=out, atol=1e-9)
        self.assertEqual(strict.report["lines"], 13)
        self.assertEqual(loose.report["lines"], 9)
        self.assertEqual(Q(strict.report["error_bound"]), 0)
        self.assertEqual(Q(loose.report["error_bound"]), Q(1, 2**30))
        float_literal = compile_float_map(
            SOURCE.replace(" * 2", " * 2.0"),
            inputs={"x": source},
            output=out,
            atol=1e-9,
        )
        self.assertEqual(float_literal.report["lines"], 9)


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class OfficialHalfTests(unittest.TestCase):
    def test_float_affine_tiles_with_independent_inputs_and_coefficients(self):
        rng = random.Random(424242)
        for coefficient, offset in ((1, 0), (2, 0), (4, 0), (8, 16), (16, 0)):
            source_text = f"def kernel(x):\n    return [(v+{coefficient})*{coefficient} for v in x]\n"
            source = Tensor("f32", "m", offset, 128, 0, 1)
            output = Tensor(
                "f32",
                "n",
                offset * 2,
                128,
                coefficient**2,
                coefficient**2 + coefficient,
            )
            compiled = compile_float_map(
                source_text,
                inputs={"x": source},
                output=output,
                atol=1e-4,
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 14)
            samples = [
                0.0,
                -0.0,
                1.0,
                2**-126,
                struct.unpack(">f", bytes.fromhex("3f7fffff"))[0],
            ]
            samples += [
                struct.unpack(">f", struct.pack(">f", rng.random()))[0]
                for _ in range(128 - len(samples))
            ]
            payload = b"".join(struct.pack(">f", value) for value in samples).hex()
            program = f"d set $lm{offset} 64 {payload}\n" + compiled.vsm + "nop\nnop\n"
            program += f"d getd $ln{output.offset}n0c0b0m0p0 64\n"
            assembly = subprocess.run(
                [ASSEMBLER, "--instruction-mode", "flat"],
                input=program,
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
            payloads = re.findall(
                r"DEBUG-LM1[^\n]*\(0x([0-9a-fA-F]{16})\)", process.stderr
            )
            actual = [
                value
                for item in payloads
                for value in struct.unpack(">ff", bytes.fromhex(item))
            ]
            self.assertEqual(len(actual), 128)
            for before, after in zip(samples, actual):
                expected = (Q(before) + coefficient) * coefficient
                self.assertLessEqual(
                    abs(Q(after) - expected), Q(compiled.report["error_bound"])
                )

    def test_all_representable_normal_half_values_in_domain(self):
        # MN-Core Half is sign/exponent/mantissa = 1/6/9, not IEEE binary16.
        positive = (
            [0]
            + [
                (exponent << 9) | mantissa
                for exponent in range(1, 31)
                for mantissa in range(512)
            ]
            + [31 << 9]
        )
        samples = positive + [value | 0x8000 for value in positive]
        samples += [0] * ((-len(samples)) % 192)
        blocks = [samples[index : index + 192] for index in range(0, len(samples), 192)]
        source = Tensor("h16", "m", 0, 192, -1, 1)
        output = Tensor("h16", "n", 0, 192, -2, 2)
        for budget in (0, 1e-9):
            compiled = compile_float_map(
                SOURCE,
                inputs={"x": source},
                output=output,
                atol=budget,
                assembler=ASSEMBLER,
            )
            prefix, suffix, expected = [], [], {}
            for index, values in enumerate(blocks):
                path = f"n0c0b{index // 64}m{index // 4 % 16}p{index % 4}"
                expected[path] = values
                payload = "".join(f"{value:04x}" for value in values)
                prefix.append(f"d set $lm0{path} 48 {payload}")
                suffix.append(f"d getd $ln0{path} 48")
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            assembly = subprocess.run(
                [ASSEMBLER, "--instruction-mode", "flat"],
                input=program,
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
            actual = {path: [] for path in expected}
            for path, bits in re.findall(
                r"DEBUG-LM1\((n\d+c\d+b\d+m\d+p\d+),\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
                process.stderr,
            ):
                actual[path].extend(
                    int(bits[index : index + 4], 16) for index in range(0, 16, 4)
                )
            for path, values in expected.items():
                self.assertEqual(len(actual[path]), 192)
                for before, after in zip(values, actual[path]):
                    error = abs(half_value(after) - 2 * half_value(before))
                    self.assertLessEqual(
                        error,
                        Q(compiled.report["error_bound"]),
                        f"{path}: {before:04x} -> {after:04x}",
                    )


if __name__ == "__main__":
    unittest.main()
