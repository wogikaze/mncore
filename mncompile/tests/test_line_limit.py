import unittest
from unittest.mock import patch

from mncompile.compiler import compile_program
from mncompile.errors import CompileError
from mncompile.layout import Contract, parse_tensor


class IncumbentLineLimit(unittest.TestCase):
    def setUp(self):
        self.source = "def kernel(x):\n    return x\n"
        self.contract = Contract(
            [parse_tensor("x", "Int", "$lm[0:2]", "/((2_W:1))", low=-8, high=8)],
            [parse_tensor("y", "Int", "$ln[0:2]", "/((2_W:1))")],
        )

    def test_equal_length_is_skipped_before_verification(self):
        with patch("mncompile.compiler.verify") as verify:
            with self.assertRaisesRegex(CompileError, "not strictly shorter than 1 lines"):
                compile_program(self.source, self.contract, tries=1, line_limit=1)
            verify.assert_not_called()

    def test_shorter_program_is_verified(self):
        from mncompile.verify import verify

        with patch("mncompile.compiler.verify", wraps=verify) as verification:
            result = compile_program(self.source, self.contract, tries=1, line_limit=2)
            self.assertEqual(result.lines, 1)
            self.assertTrue(verification.called)
