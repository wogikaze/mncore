import os
import random
import re
import subprocess
import unittest
from pathlib import Path

from mncompile import Tensor, compile_mod_classification

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCE = (Path(__file__).parent / "benchmarks/challenge/fizzbuzz_pe.py").read_text()


def classify(value, codes):
    return (
        codes[15]
        if value % 15 == 0
        else codes[3]
        if value % 3 == 0
        else codes[5]
        if value % 5 == 0
        else value
    )


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class ClassificationTests(unittest.TestCase):
    def test_exhaustive_domain_in_all_eight_lanes(self):
        data = Tensor("u32", "m", 0, 8, 1, 32768)
        output = Tensor("u32", "n", 0, 8, 1, 0xFFFFBBBB)
        compiled = compile_mod_classification(
            SOURCE, inputs={"x": data}, output=output, assembler=ASSEMBLER
        )
        self.assertEqual(compiled.report["lines"], 9)
        codes = {15: 0xFFFFBBBB, 3: 0xFFFF, 5: 0xBBBB}
        rng = random.Random(97531)
        for batch in range(9):
            prefix, suffix, expected = [], [], {}
            for index in range(4096):
                path = f"n{index // 1024}c{index // 512 % 2}b{index // 64 % 8}m{index // 4 % 16}p{index % 4}"
                values = (
                    [batch * 4096 + index + 1] * 8
                    if batch < 8
                    else [rng.randrange(1, 32769) for _ in range(8)]
                )
                prefix.append(
                    f"d set $lm0{path} 4 " + "".join(f"{value:08x}" for value in values)
                )
                suffix.append(f"d getd $ln0{path} 4")
                expected[path] = [classify(value, codes) for value in values]
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
                actual[path].extend([int(bits[:8], 16), int(bits[8:], 16)])
            for path, values in expected.items():
                self.assertEqual(actual[path], values, f"batch {batch}, {path}")

    def test_other_codes_offsets_and_multiple_groups(self):
        codes = {15: 303, 3: 101, 5: 202}
        source = "def f(x):\n    return [303 if v%15==0 else 101 if v%3==0 else 202 if v%5==0 else v for v in x]\n"
        data = Tensor("u32", "m", 16, 16, 1, 32768)
        output = Tensor("u32", "n", 32, 16, 1, 32768)
        compiled = compile_mod_classification(
            source, inputs={"x": data}, output=output, assembler=ASSEMBLER
        )
        values = [1, 3, 5, 15, 30, 32768, 32767, 32760, 7, 9, 10, 45, 11, 12, 25, 300]
        program = (
            "d set $lm16 8 "
            + "".join(f"{value:08x}" for value in values)
            + "\n"
            + compiled.vsm
            + "nop\nnop\nd getd $ln32n0c0b0m0p0 8\n"
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
        actual = [
            int(bits[index : index + 8], 16)
            for bits in re.findall(
                r"DEBUG-LM1[^\n]*\(0x([0-9a-fA-F]{16})\)", process.stderr
            )
            for index in (0, 8)
        ]
        self.assertEqual(actual, [classify(value, codes) for value in values])


if __name__ == "__main__":
    unittest.main()
