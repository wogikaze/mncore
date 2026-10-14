import os
import random
import re
import struct
import subprocess
import unittest
from pathlib import Path

from mncompile import Tensor, compile_threshold, compile_transpose

SOURCES = Path(__file__).parent / "benchmarks/challenge"
ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class RoutingTests(unittest.TestCase):
    def execute(self, source):
        assembled = subprocess.run(
            [ASSEMBLER, "--instruction-mode", "flat"],
            input=source,
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
            r"DEBUG-LM1\((n\d+c\d+b\d+m\d+p\d+),\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
            result.stderr,
        )

    def test_exact_threshold_boundaries_and_no_tail_clobber(self):
        rng = random.Random(909090)
        for count, threshold in ((4, 1), (40, 1), (36, 2), (256, 4)):
            data = Tensor("f32", "m", 0, count, 0, 5)
            output = Tensor("f32", "n", 0, count, 0, 0, allow_infinity=True)
            source = f'def f(x):\n    return [float("inf") if v >= {threshold} else 0.0 for v in x]\n'
            compiled = compile_threshold(
                source, inputs={"x": data}, output=output, assembler=ASSEMBLER
            )
            threshold_bits = int.from_bytes(struct.pack(">f", threshold), "big")
            samples = [
                0.0,
                -0.0,
                struct.unpack(">f", (threshold_bits - 1).to_bytes(4, "big"))[0],
                float(threshold),
            ]
            if count > 4:
                samples += [
                    struct.unpack(">f", (threshold_bits + 1).to_bytes(4, "big"))[0],
                    2**-126,
                ]
                samples += [
                    struct.unpack(">f", struct.pack(">f", rng.uniform(0, 5)))[0]
                    for _ in range(count - len(samples))
                ]
            payload = b"".join(struct.pack(">f", x) for x in samples + [5.0] * 8).hex()
            prefix = f"d set $lm0 {(count + 8) // 2} {payload}\n"
            prefix += f"d set $ln{count}n0c0b0m0p0 4 " + "deadbeef" * 8 + "\n"
            program = (
                prefix
                + compiled.vsm
                + "nop\nnop\n"
                + f"d getd $ln0n0c0b0m0p0 {(count + 8) // 2}\n"
            )
            words = [
                int(bits[index : index + 8], 16)
                for _, bits in self.execute(program)
                for index in (0, 8)
            ]
            self.assertEqual(words[count:], [0xDEADBEEF] * 8)
            for value, bits in zip(samples, words[:count]):
                if value >= threshold:
                    self.assertEqual(bits & 0xFF800000, 0x7F800000)
                else:
                    self.assertEqual(bits, 0)

    def test_cyclic_mab_transpose_with_independent_groups_and_offsets(self):
        rng = random.Random(454545)
        for offset in (0, 32):
            data = Tensor("f64", "m", offset, 16, -1, 1)
            output = Tensor("f64", "n", offset * 2, 16, -1, 1)
            compiled = compile_transpose(
                (SOURCES / "transpose_mab.py").read_text(),
                inputs={"x": data},
                output=output,
                row_partition="mab",
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 15)
            prefix, suffix, expected = [], [], {}
            for group in (0, 1):
                matrix = [[rng.uniform(-1, 1) for _ in range(16)] for _ in range(16)]
                matrix[0][0], matrix[1][1], matrix[0][15] = -0.0, 0.0, 2**-1022
                for mab, row in enumerate(matrix):
                    path = f"n{group}c0b0m{mab}p0"
                    expected[path] = [matrix[index][mab] for index in range(16)]
                    payload = b"".join(struct.pack(">d", value) for value in row).hex()
                    prefix.append(f"d set $lm{offset}n{group}c0m{mab} 16 {payload}")
                    suffix.append(f"d getd $ln{output.offset}{path} 16")
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            actual = {path: [] for path in expected}
            for path, bits in self.execute(program):
                actual[path].append(struct.unpack(">d", bytes.fromhex(bits))[0])
            self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
