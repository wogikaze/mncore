import os
import random
import re
import subprocess
import unittest
from pathlib import Path

from mncompile import Tensor, compile_inversions

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCES = Path(__file__).parent / "benchmarks/challenge"


def count_inversions(row):
    return sum(
        row[left] > row[right]
        for left in range(len(row))
        for right in range(left + 1, len(row))
    )


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class InversionTests(unittest.TestCase):
    def execute(self, program):
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
        return dict(
            re.findall(
                r"DEBUG-LM1\((n\d+c\d+b\d+m\d+p\d+),\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
                process.stderr,
            )
        )

    def test_small_rows_duplicates_extremes_and_full_uint32_values(self):
        rng = random.Random(112358)
        for offset in (0, 32):
            data = Tensor("u64", "m", offset, 16, 0, 2**32 - 1)
            output = Tensor("u64", "n", offset // 2, 1, 0, 120)
            compiled = compile_inversions(
                (SOURCES / "inversion_small.py").read_text(),
                inputs={"x": data},
                output=output,
                row_partition="l2b_l1b",
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 9)
            prefix, suffix, expected = [], [], {}
            for slot in range(64):
                if slot == 0:
                    row = list(range(16))
                elif slot == 1:
                    row = list(reversed(range(16)))
                elif slot == 2:
                    row = [0] * 16
                elif slot == 3:
                    row = [2**32 - 1] * 16
                else:
                    row = (
                        [rng.randrange(11) for _ in range(16)]
                        if slot % 2
                        else [rng.getrandbits(32) for _ in range(16)]
                    )
                group, l2b, l1b = slot // 16, slot // 8 % 2, slot % 8
                path = f"n{group}c{l2b}b{l1b}m0p0"
                prefix.append(
                    f"d set $lm{data.offset}n{group}c{l2b}b{l1b} 16 "
                    + "".join(f"{value:016x}" for value in row)
                )
                suffix.append(f"d getd $ln{output.offset}{path} 1")
                expected[path] = count_inversions(row)
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            actual = self.execute(program)
            self.assertEqual(
                {path: int(bits, 16) for path, bits in actual.items()}, expected
            )

    def test_large_rows_duplicates_sorted_and_independent_packed_rows(self):
        rng = random.Random(3141592)
        for offset in (0, 32):
            data = Tensor("u32", "m", offset, 128, 0, 100)
            output = Tensor("u32", "n", offset // 2, 2, 0, 2016)
            compiled = compile_inversions(
                (SOURCES / "inversion.py").read_text(),
                inputs={"x": data},
                output=output,
                row_partition="mab_pe_word",
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 31)
            rows = [
                list(range(64)),
                list(reversed(range(64))),
                [0] * 64,
                [100] * 64,
                [100, 0] * 32,
            ]
            rows += [
                [rng.randrange(101) for _ in range(64)] for _ in range(128 - len(rows))
            ]
            prefix, suffix, expected = [], [], {}
            for mab in range(16):
                for pe in range(4):
                    row = 2 * (4 * mab + pe)
                    left, right = rows[row : row + 2]
                    values = [value for pair in zip(left, right) for value in pair]
                    prefix.append(
                        f"d set $lm{data.offset}m{mab}p{pe} 64 "
                        + "".join(f"{value:08x}" for value in values)
                    )
                    path = f"n0c0b0m{mab}p{pe}"
                    suffix.append(f"d getd $ln{output.offset}{path} 1")
                    expected[path] = (count_inversions(left), count_inversions(right))
            program = (
                "\n".join(prefix)
                + "\n"
                + compiled.vsm
                + "nop\nnop\n"
                + "\n".join(suffix)
                + "\n"
            )
            actual = self.execute(program)
            self.assertEqual(
                {
                    path: (int(bits[:8], 16), int(bits[8:], 16))
                    for path, bits in actual.items()
                },
                expected,
            )


if __name__ == "__main__":
    unittest.main()
