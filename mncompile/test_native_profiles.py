"""Independent inputs for matrix/color/text target-library lowerings."""

import colorsys
import os
import random
import re
import struct
import subprocess
import unittest
from pathlib import Path

from mncompile import (
    CompileError,
    GlobalTensor,
    Tensor,
    compile_fizzbuzz_text,
    compile_hsv_to_rgb,
    compile_literal,
    compile_matrix_square,
    compile_range,
)

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCES = Path(__file__).parent / "benchmarks/challenge"


def f32(value):
    return struct.unpack(">f", struct.pack(">f", value))[0]


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class NativeProfileTests(unittest.TestCase):
    def execute(self, program, kind="LM1"):
        assembled = subprocess.run(
            [ASSEMBLER, "--instruction-mode", "flat"],
            input=program,
            text=True,
            capture_output=True,
            check=True,
        )
        result = subprocess.run(
            [EMULATOR, "--offchip-memory-init", "zero"],
            input=assembled.stdout,
            text=True,
            capture_output=True,
            check=True,
        )
        return re.findall(
            r"DEBUG-" + kind + r"[^\n]*\(0x([0-9a-fA-F]{16})\)", result.stderr
        )

    def test_matrix_integer_contract_and_independent_matrices(self):
        rng = random.Random(161616)
        source = (SOURCES / "mat_sq.py").read_text()
        for offset in (0, 32):
            data = Tensor("f32", "m", offset, 64, 0, 100, integral_values=True)
            output = Tensor("f32", "n", 2 * offset, 64, 0, 160000)
            compiled = compile_matrix_square(
                source,
                inputs={"x": data},
                output=output,
                row_partition="l2b_pe_word",
                atol=0,
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 10)
            prefix, suffix, expected = [], [], []
            for slot in range(8):
                group, c = slot // 2, slot % 2
                matrix = [[rng.randrange(101) for _ in range(16)] for _ in range(16)]
                if slot == 0:
                    matrix = [[0] * 16 for _ in range(16)]
                elif slot == 1:
                    matrix = [[100] * 16 for _ in range(16)]
                elif slot == 2:
                    matrix = [[100 * int(i == j) for j in range(16)] for i in range(16)]
                elif slot == 3:
                    matrix = [[(i + j) % 2 for j in range(16)] for i in range(16)]
                answer = [
                    [
                        sum(matrix[k][i] * matrix[j][k] for k in range(16))
                        for j in range(16)
                    ]
                    for i in range(16)
                ]
                for pe in range(4):
                    values, wants = [], []
                    for col in range(16):
                        for row in range(4):
                            values.append(float(matrix[4 * pe + row][col]))
                            wants.append(float(answer[4 * pe + row][col]))
                    prefix.append(
                        f"d set $lm{offset}n{group}c{c}p{pe} 32 "
                        + b"".join(struct.pack(">f", v) for v in values).hex()
                    )
                    suffix.append(f"d getd $ln{output.offset}n{group}c{c}b0m0p{pe} 32")
                    expected.extend(wants)
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            actual = [
                v
                for bits in self.execute(program)
                for v in struct.unpack(">ff", bytes.fromhex(bits))
            ]
            self.assertEqual(actual, expected)
        with self.assertRaises(CompileError):
            compile_matrix_square(
                source,
                inputs={"x": Tensor("f32", "m", 0, 64, 0, 100)},
                output=Tensor("f32", "n", 0, 64, 0, 160000),
                row_partition="l2b_pe_word",
                atol=1e-5,
            )

    def test_hsv_sector_boundaries_extremes_and_random_colors(self):
        rng = random.Random(625625)
        source = (SOURCES / "hsv2rgb.py").read_text()
        near_one = f32(1 - 2**-24)
        hues = [0.0, -0.0, 2**-126, near_one]
        for sector in range(1, 6):
            bits = int.from_bytes(struct.pack(">f", sector / 6), "big")
            hues += [
                struct.unpack(">f", (bits + i).to_bytes(4, "big"))[0]
                for i in (-2, -1, 0, 1, 2)
            ]
        samples = [
            (h, s, v)
            for h in hues
            for s in (0.0, -0.0, 2**-126, 0.5, 1.0)
            for v in (0.0, -0.0, 2**-126, 0.5, near_one)
        ]
        samples += [tuple(f32(rng.random()) for _ in range(3)) for _ in range(2048)]
        samples += [(0.0, 0.0, 0.0)] * ((-len(samples)) % 256)
        for batch in range(len(samples) // 256):
            offset = 32 if batch % 2 else 0
            data = Tensor("f32", "m", offset, 24, 0, 1)
            output = Tensor("f32", "n", 2 * offset, 24, 0, 1)
            compiled = compile_hsv_to_rgb(
                source,
                inputs={"x": data},
                output=output,
                row_partition="pe_word_rgb",
                atol=1e-4,
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 12)
            prefix, suffix, expected = [], [], []
            for slot in range(32):
                group, c, pe = slot // 8, slot // 4 % 2, slot % 4
                colors = samples[batch * 256 + slot * 8 : batch * 256 + slot * 8 + 8]
                rgb = [colorsys.hsv_to_rgb(*color) for color in colors]
                values = []
                for index in range(0, 8, 2):
                    for channel in range(3):
                        values.extend(
                            [colors[index][channel], colors[index + 1][channel]]
                        )
                        expected.extend([rgb[index][channel], rgb[index + 1][channel]])
                prefix.append(
                    f"d set $lm{offset}n{group}c{c}p{pe} 12 "
                    + b"".join(struct.pack(">f", v) for v in values).hex()
                )
                suffix.append(f"d getd $ln{output.offset}n{group}c{c}b0m0p{pe} 12")
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            actual = [
                v
                for bits in self.execute(program)
                for v in struct.unpack(">ff", bytes.fromhex(bits))
            ]
            self.assertEqual(len(actual), len(expected))
            for want, got in zip(expected, actual):
                self.assertLessEqual(
                    abs(want - got), float(compiled.report["error_bound"])
                )

    def test_text_source_constants_and_all_output_bytes(self):
        for fizz, buzz in (("Fizz", "Buzz"), ("Tapp", "Hopp")):
            source = (
                (SOURCES / "fizzbuzz.py")
                .read_text()
                .replace("FizzBuzz", fizz + buzz)
                .replace("Fizz", fizz)
                .replace("Buzz", buzz)
            )
            value = "\n".join(
                fizz + buzz
                if i % 15 == 0
                else fizz
                if i % 3 == 0
                else buzz
                if i % 5 == 0
                else str(i)
                for i in range(1, 6335)
            ).encode()
            compiled = compile_fizzbuzz_text(
                source,
                inputs={},
                output=GlobalTensor("bytes", 0, 0, len(value)),
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 98)
            words = self.execute(compiled.vsm + "nop\nnop\nd getd $d0n0 4096\n", "DRAM")
            actual = bytes.fromhex("".join(words))
            self.assertEqual(actual[: len(value)], value)

    def test_literal_constants_and_range_prefixes(self):
        for value in (b"Hello, world!", b"Hello, there!", b"Hello, folks!"):
            source = f"def kernel():\n    return {value!r}\n"
            compiled = compile_literal(
                source,
                inputs={},
                output=GlobalTensor("bytes", 0, 0, len(value)),
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 9)
            words = self.execute(compiled.vsm + "nop\nnop\nd getd $d0n0 2\n", "DRAM")
            self.assertEqual(bytes.fromhex("".join(words))[: len(value)], value)
        for count in (1, 17, 32768):
            compiled = compile_range(
                f"def kernel():\n    return list(range(1,{count + 1}))\n",
                inputs={},
                output=GlobalTensor("i32", 0, 0, count),
                assembler=ASSEMBLER,
            )
            words = self.execute(
                compiled.vsm + f"nop\nnop\nd getd $d0n0 {(count + 1) // 2}\n", "DRAM"
            )
            actual = [int(bits[i : i + 8], 16) for bits in words for i in (0, 8)]
            self.assertEqual(actual[:count], list(range(1, count + 1)))


if __name__ == "__main__":
    unittest.main()
