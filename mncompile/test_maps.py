import os
import random
import re
import shutil
import subprocess
import unittest
from pathlib import Path

from mncompile import CompileError, Tensor, compile_map
from mncompile.maps import parse_map

SOURCES = Path(__file__).parent / "benchmarks/challenge"
ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")


@unittest.skipUnless(shutil.which("opt"), "LLVM opt is required")
class MapTests(unittest.TestCase):
    def test_normal_python_maps_preserve_names_and_operations(self):
        _, params, operation = parse_map((SOURCES / "a_plus_b.py").read_text())
        self.assertEqual(params, ("a", "b"))
        self.assertEqual(operation.op, "add")
        self.assertEqual([node.name for node in operation.args], ["a", "b"])

    def test_data_dependent_control_is_rejected(self):
        for source in (
            "def f(x):\n    return [v+1 for v in x if v>0]\n",
            "def f(x):\n    return [eval(v) for v in x]\n",
        ):
            with self.assertRaises(CompileError):
                parse_map(source)

    def test_llvm_and_layout_aware_sum(self):
        a = Tensor("i32", "m", 0, 32, 0, 100)
        b = Tensor("i32", "n", 0, 32, 0, 100)
        out = Tensor("i32", "m", 32, 32, 0, 200)
        compiled = compile_map(
            (SOURCES / "a_plus_b.py").read_text(), inputs={"a": a, "b": b}, output=out
        )
        self.assertEqual(compiled.report["lines"], 6)
        self.assertIn("add i32", compiled.llvm_ir)
        self.assertEqual(compiled.report["error_bound"], "0")

    def test_small_u64_assumption_is_explicit(self):
        source = Tensor("u64", "n", 0, 20, 0, 99)
        out = Tensor("u64", "m", 0, 20, 2, 101)
        compiled = compile_map(
            (SOURCES / "plus_two.py").read_text(), inputs={"x": source}, output=out
        )
        self.assertEqual(compiled.report["lines"], 6)
        self.assertIn("$n1v2", compiled.vsm)
        self.assertTrue(compiled.report["preconditions"])

    def test_float_mantissa_multiply_requires_proven_range(self):
        source = Tensor("u64", "m", 0, 16, 0, 1000)
        out = Tensor("u64", "n", 0, 16, 0, 7000)
        compiled = compile_map(
            (SOURCES / "mul7.py").read_text(), inputs={"x": source}, output=out
        )
        self.assertEqual(compiled.report["lines"], 6)
        too_large = Tensor("u64", "m", 0, 16, 0, 100000)
        with self.assertRaises(CompileError):
            compile_map(
                (SOURCES / "mul7.py").read_text(), inputs={"x": too_large}, output=out
            )


@unittest.skipUnless(
    ASSEMBLER and EMULATOR and shutil.which("opt"),
    "Set official assembler/emulator paths",
)
class OfficialMapTests(unittest.TestCase):
    def execute(self, source, inputs, output, values):
        compiled = compile_map(
            source, inputs=inputs, output=output, assembler=ASSEMBLER
        )
        prefix = []
        for name, tensor in inputs.items():
            data = b"".join(
                (v & ((1 << tensor.bits) - 1)).to_bytes(tensor.bits // 8, "big")
                for v in values[name]
            )
            prefix.append(
                f"d set $l{tensor.memory}{tensor.offset} {len(data) // 8} {data.hex()}"
            )
        program = "\n".join(prefix) + "\n" + compiled.vsm + "nop\nnop\n"
        program += f"d getd $l{output.memory}{output.offset}n0c0b0m0p0 {output.elements * output.bits // 64}\n"
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
        memory = "LM0" if output.memory == "m" else "LM1"
        payloads = re.findall(
            rf"DEBUG-{memory}[^\n]*\(0x([0-9a-fA-F]{{16}})\)", process.stderr
        )
        raw = bytes.fromhex("".join(payloads))
        width = output.bits // 8
        actual = [
            int.from_bytes(
                raw[index : index + width], "big", signed=output.dtype.startswith("i")
            )
            for index in range(0, len(raw), width)
        ]
        self.assertEqual(len(actual), output.elements, process.stderr[:800])
        return actual

    def test_increment_and_sum_on_independent_random_inputs(self):
        rng = random.Random(314159)
        for count in (16, 32, 64):
            a = Tensor("i32", "m", 0, count, 0, 100)
            b = Tensor("i32", "n", 0, count, 0, 100)
            out = Tensor("i32", "m", count, count, 0, 200)
            values = {
                "a": [rng.randrange(101) for _ in range(count)],
                "b": [rng.randrange(101) for _ in range(count)],
            }
            result = self.execute(
                (SOURCES / "a_plus_b.py").read_text(), {"a": a, "b": b}, out, values
            )
            self.assertEqual(result, [a + b for a, b in zip(values["a"], values["b"])])
        a = Tensor("i32", "m", 0, 16, 0, 50)
        out = Tensor("i32", "n", 0, 16, 1, 51)
        values = {"x": [rng.randrange(51) for _ in range(16)]}
        self.assertEqual(
            self.execute((SOURCES / "plus_one.py").read_text(), {"x": a}, out, values),
            [x + 1 for x in values["x"]],
        )

    def test_plus_two_covers_entire_input_domain(self):
        values = list(range(100))
        a = Tensor("i64", "m", 0, 100, 0, 99)
        out = Tensor("i64", "n", 0, 100, 2, 101)
        self.assertEqual(
            self.execute(
                (SOURCES / "plus_two.py").read_text(), {"x": a}, out, {"x": values}
            ),
            [x + 2 for x in values],
        )

    def test_mantissa_multiply_exhausts_challenge_domain(self):
        values = list(range(1001)) + [0, 1000, 500]
        a = Tensor("u64", "m", 0, len(values), 0, 1000)
        out = Tensor("u64", "n", 0, len(values), 0, 7000)
        self.assertEqual(
            self.execute(
                (SOURCES / "mul7.py").read_text(), {"x": a}, out, {"x": values}
            ),
            [x * 7 for x in values],
        )

    def test_mantissa_multiply_generalizes_coefficients(self):
        for coefficient in (3, 13, 255):
            maximum = 65535 // coefficient
            values = [0, 1, maximum - 1, maximum] * 4
            a = Tensor("u64", "m", 0, 16, 0, maximum)
            out = Tensor("u64", "n", 0, 16, 0, maximum * coefficient)
            source = f"def f(x):\n    return [v*{coefficient} for v in x]\n"
            self.assertEqual(
                self.execute(source, {"x": a}, out, {"x": values}),
                [x * coefficient for x in values],
            )

    def test_byte_swap_random_full_width_values_and_partial_tail(self):
        rng = random.Random(271828)
        source = (SOURCES / "convert_endian.py").read_text()
        for count in (1, 5, 256):
            values = [rng.getrandbits(64) for _ in range(count)]
            if count >= 5:
                values[:5] = [
                    0,
                    2**64 - 1,
                    0x0123456789ABCDEF,
                    0x8000000000000000,
                    0xFF00FF00FF00FF00,
                ]
            a = Tensor("u64", "m", 0, count, 0, 2**64 - 1)
            out = Tensor("u64", "n", 0, count, 0, 2**64 - 1)
            actual = self.execute(source, {"x": a}, out, {"x": values})
            self.assertEqual(
                actual, [int.from_bytes(x.to_bytes(8, "little"), "big") for x in values]
            )

    def test_abs_pipeline_random_values_and_other_tile_counts(self):
        rng = random.Random(161803)
        source = (SOURCES / "abs.py").read_text()
        for count in (40, 56, 88, 120):
            values = [rng.randrange(-100, 101) for _ in range(count)]
            values[:4] = [-100, 0, 100, -1]
            a = Tensor("i32", "m", 0, count, -100, 100)
            out = Tensor("i32", "n", 0, count, 0, 100)
            actual = self.execute(source, {"x": a}, out, {"x": values})
            self.assertEqual(actual, [abs(x) for x in values])

    def test_modulo_three_all_inputs_in_every_lane(self):
        source = (SOURCES / "mod3.py").read_text()
        data = Tensor("u32", "m", 0, 32, 0, 255)
        output = Tensor("u32", "n", 0, 32, 0, 2)
        compiled = compile_map(
            source, inputs={"x": data}, output=output, assembler=ASSEMBLER
        )
        self.assertEqual(compiled.report["lines"], 8)
        prefix, suffix, expected = [], [], {}
        for value in range(256):
            path = f"n0c0b{value // 64}m{value // 4 % 16}p{value % 4}"
            prefix.append(f"d set $lm0{path} 16 " + f"{value:08x}" * 32)
            suffix.append(f"d getd $ln0{path} 16")
            expected[path] = [value % 3] * 32
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
        self.assertEqual(actual, expected)
        rng = random.Random(13579)
        for count in (64, 256):
            values = [rng.randrange(256) for _ in range(count)]
            data = Tensor("u32", "m", 16, count, 0, 255)
            output = Tensor("u32", "n", 32, count, 0, 2)
            actual = self.execute(source, {"x": data}, output, {"x": values})
            self.assertEqual(actual, [value % 3 for value in values])

    def test_integer_log2_exhaustive_domain_in_every_lane(self):
        source = (SOURCES / "log2.py").read_text()
        data = Tensor("i32", "m", 0, 32, 1, 2048)
        output = Tensor("i32", "n", 0, 32, 0, 11)
        compiled = compile_map(
            source, inputs={"x": data}, output=output, assembler=ASSEMBLER
        )
        self.assertEqual(compiled.report["lines"], 7)
        self.assertIn("llvm.ctlz.i32", compiled.llvm_ir)
        prefix, suffix, expected = [], [], {}
        for index in range(2048):
            value = index + 1
            path = f"n{index // 1024}c{index // 512 % 2}b{index // 64 % 8}m{index // 4 % 16}p{index % 4}"
            prefix.append(f"d set $lm0{path} 16 " + f"{value:08x}" * 32)
            suffix.append(f"d getd $ln0{path} 16")
            expected[path] = value.bit_length() - 1
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
        for path, value in expected.items():
            self.assertEqual(actual[path], [value] * 32, path)
        values = [random.Random(index).randrange(1, 2049) for index in range(64)]
        data = Tensor("i32", "m", 16, 64, 1, 2048)
        output = Tensor("i32", "n", 32, 64, 0, 11)
        result = self.execute(source, {"x": data}, output, {"x": values})
        self.assertEqual(result, [value.bit_length() - 1 for value in values])


if __name__ == "__main__":
    unittest.main()
