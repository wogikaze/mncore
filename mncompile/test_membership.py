import os
import random
import re
import subprocess
import unittest
from pathlib import Path

from mncompile import Tensor, compile_membership

ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")
SOURCE = (Path(__file__).parent / "benchmarks/challenge/contains.py").read_text()


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class MembershipTests(unittest.TestCase):
    def compile(self, a_offset=0, b_offset=0, c_offset=32):
        a = Tensor("u64", "m", a_offset, 16, 0, 1000)
        b = Tensor("u64", "n", b_offset, 16, 0, 1000)
        c = Tensor("u64", "n", c_offset, 16, 0, 1)
        compiled = compile_membership(
            SOURCE, inputs={"a": a, "b": b}, output=c, assembler=ASSEMBLER
        )
        self.assertEqual(compiled.report["lines"], 20)
        return compiled

    def execute(self, compiled, prefix, suffix):
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
            actual.setdefault(path, []).append(int(bits, 16))
        return actual

    def test_dense_sets_duplicates_extremes_and_offsets(self):
        rng = random.Random(102938)
        sets = [
            [0] * 1024,
            [1000] * 1024,
            list(range(1001)) + [0] * 23,
            [rng.randrange(1001) for _ in range(1024)],
        ]
        for case, members in enumerate(sets):
            a_offset, b_offset, c_offset = (32, 16, 64) if case == 3 else (0, 0, 32)
            compiled = self.compile(a_offset, b_offset, c_offset)
            prefix, suffix, expected = [], [], {}
            for slot in range(64):
                group, l2b, l1b = slot // 16, slot // 8 % 2, slot % 8
                path = f"n{group}c{l2b}b{l1b}m0p0"
                queries = [(slot * 16 + index) % 1001 for index in range(16)]
                prefix.append(
                    f"d set $lm{a_offset}n{group}c{l2b}b{l1b} 16 "
                    + "".join(f"{value:016x}" for value in queries)
                )
                suffix.append(f"d getd $ln{c_offset}{path} 16")
                expected[path] = [int(value in set(members)) for value in queries]
            for mab in range(16):
                for pe in range(4):
                    values = members[(mab * 4 + pe) * 16 : (mab * 4 + pe + 1) * 16]
                    prefix.append(
                        f"d set $ln{b_offset}m{mab}p{pe} 16 "
                        + "".join(f"{value:016x}" for value in values)
                    )
            actual = self.execute(compiled, prefix, suffix)
            for path, values in expected.items():
                self.assertEqual(actual.get(path), values, f"case {case}, {path}")

    def test_singleton_basis_all_nonzero_keys_and_output_lanes(self):
        compiled = self.compile()
        for positive in (True, False):
            for batch in range(16):
                prefix, suffix, expected = [], [], {}
                for slot in range(64):
                    key = batch * 64 + slot + 1
                    if key > 1000:
                        continue
                    group, l2b, l1b = slot // 16, slot // 8 % 2, slot % 8
                    path = f"n{group}c{l2b}b{l1b}m0p0"
                    query = key if positive else key % 1000 + 1
                    prefix.append(
                        f"d set $lm0n{group}c{l2b}b{l1b} 16 " + f"{query:016x}" * 16
                    )
                    member_slot = (key - 1) % 1024
                    mab, pe, index = (
                        member_slot // 64,
                        member_slot // 16 % 4,
                        member_slot % 16,
                    )
                    prefix.append(
                        f"d set $ln{2 * index}n{group}c{l2b}b{l1b}m{mab}p{pe} 1 {key:016x}"
                    )
                    suffix.append(f"d getd $ln32{path} 16")
                    expected[path] = [int(positive)] * 16
                actual = self.execute(compiled, prefix, suffix)
                for path, values in expected.items():
                    self.assertEqual(
                        actual.get(path),
                        values,
                        f"positive={positive}, batch={batch}, {path}",
                    )


if __name__ == "__main__":
    unittest.main()
