import os
import random
import re
import subprocess
import unittest
from pathlib import Path

from mncompile import Tensor, compile_bit_reverse

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCE = (Path(__file__).parent / "benchmarks/challenge/bit_reverse.py").read_text()


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class BitReverseTests(unittest.TestCase):
    def test_all_basis_vectors_zero_and_random_inputs(self):
        rng = random.Random(24681357)
        for batch in range(18):
            offset = 32 if batch == 17 else 0
            data = Tensor("u64", "m", offset, 4, 0, 2**64 - 1)
            output = Tensor("u64", "n", 2 * offset, 4, 0, 2**64 - 1)
            compiled = compile_bit_reverse(
                SOURCE,
                inputs={"x": data},
                output=output,
                row_partition="pe",
                assembler=ASSEMBLER,
            )
            self.assertEqual(compiled.report["lines"], 10)
            expected, prefix, suffix = {}, {}, []
            for slot in range(64):
                if batch < 16:
                    bit = batch * 64 + slot
                    values = [0] * 16
                    values[bit // 64] = 1 << (63 - bit % 64)
                elif batch == 16 and slot == 0:
                    values = [0] * 16
                elif batch == 16 and slot == 1:
                    values = [2**64 - 1] * 16
                else:
                    values = [rng.getrandbits(64) for _ in range(16)]
                expected[slot] = [
                    int(f"{value:064b}"[::-1], 2) for value in reversed(values)
                ]
                group, l2b, l1b = slot // 16, slot // 8 % 2, slot % 8
                for pe in range(4):
                    path = f"n{group}c{l2b}b{l1b}p{pe}"
                    payload = "".join(
                        f"{values[index]:016x}" for index in range(pe, 16, 4)
                    )
                    prefix[path] = f"d set $lm{data.offset}{path} 4 {payload}"
                    suffix.append(
                        f"d getd $ln{output.offset}n{group}c{l2b}b{l1b}m0p{pe} 4"
                    )
            program = (
                "\n".join(prefix.values())
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
            actual = {(slot, pe): [] for slot in range(64) for pe in range(4)}
            for group, l2b, l1b, pe, bits in re.findall(
                r"DEBUG-LM1\(n(\d+)c(\d+)b(\d+)m0p(\d+),\d+\):[^\n]*\(0x([0-9a-fA-F]{16})\)",
                process.stderr,
            ):
                slot = int(group) * 16 + int(l2b) * 8 + int(l1b)
                actual[(slot, int(pe))].append(int(bits, 16))
            for slot, reference in expected.items():
                values = [
                    actual[(slot, pe)][index] for index in range(4) for pe in range(4)
                ]
                self.assertEqual(values, reference, f"batch {batch}, L1B slot {slot}")


if __name__ == "__main__":
    unittest.main()
