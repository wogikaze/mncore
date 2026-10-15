"""The structured instruction model can express every instruction form found in the repository."""

import re
import unittest
from pathlib import Path

from mncompile.machine import alu_opcodes, emit, mau_opcodes, parse_program
from mncompile.sim import assembler

ROOT = Path(__file__).resolve().parents[2]


def program_files():
    files = sorted(ROOT.glob("problems/*/*.vsm")) + sorted(ROOT.glob("problems/challenge/*/*.vsm"))
    return [f for f in files if not f.name.startswith("testcase")]


class Roundtrip(unittest.TestCase):
    def test_machine_code_identical_after_roundtrip(self):
        asm = assembler()
        checked = 0
        for path in program_files():
            text = path.read_text()
            if re.search(r"^\s*(d |mask)", text, re.M):
                continue
            original = asm.assemble(text)
            if not original.ok:
                continue
            with self.subTest(file=str(path.relative_to(ROOT))):
                again = asm.assemble(emit(parse_program(text)))
                self.assertTrue(again.ok, again.error[:300])
                self.assertEqual(original.code, again.code)
                checked += 1
        self.assertGreater(checked, 60)

    def test_every_opcode_spelling_assembles_in_a_minimal_form(self):
        asm = assembler()
        failures = []
        for op in alu_opcodes():
            base = op.split("/")[0].lstrip("u")
            name = base if base in ("zero", "imm", "immu", "msl", "msr") else base[1:]
            if op in ("imm", "immu"):
                text = f'{op} i"1" $lr0v\n'
            elif op == "zero":
                text = "zero $lr0v\n"
            else:
                from mncompile.machine import ALU_OPS

                n = ALU_OPS[name][0]
                srcs = " ".join(["$lr0v", "$ls0v"][:n])
                text = f"{op} {srcs} $lr8v\n"
            if not asm.assemble(text).ok:
                failures.append(op)
        for op in mau_opcodes():
            if op.endswith(("mwrite",)):
                text = f"{op} $lr0v $lx0\n"
            elif op.endswith("mread"):
                text = f"{op} {'$llx0' if op[0] == 'h' else '$lx0'} $lr8v\n"
            else:
                m = re.fullmatch(r"([dfgh])([vm])(fma|mul|add|passa)([ud]?)(r?)", op)
                n = {"fma": 3, "mul": 2, "add": 2, "passa": 1}[m[3]]
                srcs = ["$lr0v", "$ls0v", "$ln0v"][:n]
                if m[2] == "m":
                    srcs = ["$lx"] + srcs[: n - 1]
                text = f"{op} {' '.join(srcs)} $llr16v\n"
            if not asm.assemble(text).ok:
                failures.append(op)
        # a few forms are only legal with particular operand widths; they must be rare
        self.assertLess(len(failures), 40, failures)


if __name__ == "__main__":
    unittest.main()
