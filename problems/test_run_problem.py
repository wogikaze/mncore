"""Compatibility checks for official Challenge testcase formats."""

import contextlib
import io
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from run_problem import run_judge


class TestTestcaseCompatibility(unittest.TestCase):
    def check_input(self, body: str, expected: str, adapted: bool) -> None:
        with tempfile.TemporaryDirectory() as directory:
            testcase = Path(directory) / "testcase.vsm"
            testcase.write_text(body, encoding="utf-8")
            passed_paths = []

            def execute(command, **kwargs):
                passed_paths.append(Path(command[2]))
                self.assertEqual(passed_paths[-1].read_text(encoding="utf-8"), expected)
                self.assertEqual(passed_paths[-1] != testcase, adapted)
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch("run_problem.subprocess.run", side_effect=execute):
                with contextlib.redirect_stdout(io.StringIO()):
                    result = run_judge(Path("judge.py"), testcase, Path("answer.vsm"), False, False)
            self.assertEqual(result, 0)
            self.assertEqual(testcase.read_text(encoding="utf-8"), body)
            if adapted:
                self.assertFalse(passed_paths[0].exists())

    def test_legacy_separator_preserves_suffix_instructions(self):
        body = (
            'd set $lm0 1 0000000000000000\n'
            '# ======= YOUR VSM WILL BE INSERTED HERE =======\n'
            'nop\n'
            '# ======= Out(0): ((4_PE:1))@LM1 / ULong =======\n'
            'd getd $ln0 1 # expect=[0] / ULong @[0]\n'
        )
        expected = body.replace('# ======= Out(0):', '# ======= Output =======\n# ======= Out(0):')
        self.check_input(body, expected, True)

    def test_modern_separator_is_unchanged(self):
        body = '# ======= YOUR VSM WILL BE INSERTED HERE =======\n# ======= Output =======\n# ======= Out(0): values =======\n'
        self.check_input(body, body, False)

    def test_unrecognized_format_is_left_to_judge(self):
        self.check_input('nop\n', 'nop\n', False)


if __name__ == "__main__":
    unittest.main()
