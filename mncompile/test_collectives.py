import os
import random
import re
import struct
import subprocess
import unittest
from fractions import Fraction as Q
from pathlib import Path

from mncompile import Tensor, compile_gather, compile_square_sum

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCE = (Path(__file__).parent / "benchmarks/challenge/gather_easy.py").read_text()


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class GatherTests(unittest.TestCase):
    def test_square_sum_independent_rows_across_l2b_and_pe(self):
        source = (
            Path(__file__).parent / "benchmarks/challenge/square_sum.py"
        ).read_text()
        data = Tensor("f64", "m", 0, 128, -1, 1)
        output = Tensor("f64", "n", 0, 1, 0, 128)
        compiled = compile_square_sum(
            source,
            inputs={"x": data},
            output=output,
            row_partition="l2b_pe",
            atol=1e-9,
            assembler=ASSEMBLER,
        )
        self.assertEqual(compiled.report["lines"], 11)
        rng = random.Random(8675309)
        prefix, suffix, expected = [], [], {}
        for l2b in range(8):
            for pe in range(4):
                path = f"n{l2b // 2}c{l2b % 2}b0m0p{pe}"
                values = [rng.uniform(-1, 1) for _ in range(128)]
                values[:6] = [0.0, -0.0, -1.0, 1.0, 2**-1022, -(2**-1022)]
                expected[path] = sum((Q(value) ** 2 for value in values), Q(0))
                payload = b"".join(struct.pack(">d", value) for value in values).hex()
                prefix.append(f"d set $lm0n{l2b // 2}c{l2b % 2}p{pe} 128 {payload}")
                suffix.append(f"d getd $ln0{path} 1")
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
        actual = {}
        for path, bits in re.findall(
            r"DEBUG-LM1\((n\d+c\d+b\d+m\d+p\d+),\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
            process.stderr,
        ):
            actual[path] = struct.unpack(">d", bytes.fromhex(bits))[0]
        self.assertEqual(set(actual), set(expected))
        for path, reference in expected.items():
            self.assertLessEqual(
                abs(Q(actual[path]) - reference), Q(compiled.report["error_bound"])
            )

    def test_independent_mab_rows_and_multiple_tiles(self):
        rng = random.Random(1234567)
        for count in (16, 32):
            data = Tensor("f64", "m", 0, 1024, -10000, 10000)
            indices = Tensor("u64", "m", 2048, count, 0, 1023)
            output = Tensor("f64", "n", 0, count, -10000, 10000)
            compiled = compile_gather(
                SOURCE,
                inputs={"x": data, "indices": indices},
                output=output,
                row_partition="mab",
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 6 * count // 16)
            subprocess.run(
                ["opt", "-passes=verify", "-disable-output", "-"],
                input=compiled.llvm_ir,
                text=True,
                capture_output=True,
                check=True,
            )
            prefix, expected = [], {}
            for mab in range(16):
                values = [rng.uniform(-10000, 10000) for _ in range(1024)]
                selected = [0, 1023, 0, 1023] + [
                    rng.randrange(1024) for _ in range(count - 4)
                ]
                expected[mab] = [values[index] for index in selected]
                payload = b"".join(struct.pack(">d", value) for value in values).hex()
                prefix.append(f"d set $lm0n0c0b0m{mab} 1024 {payload}")
                payload = b"".join(index.to_bytes(8, "big") for index in selected).hex()
                prefix.append(f"d set $lm2048n0c0b0m{mab} {count} {payload}")
            suffix = [f"d getd $ln0n0c0b0m{mab}p0 {count}" for mab in range(16)]
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
            actual = {mab: [] for mab in range(16)}
            for mab, bits in re.findall(
                r"DEBUG-LM1\(n0c0b0m(\d+)p0,\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
                process.stderr,
            ):
                actual[int(mab)].append(struct.unpack(">d", bytes.fromhex(bits))[0])
            self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
