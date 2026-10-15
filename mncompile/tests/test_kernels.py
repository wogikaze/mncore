"""Every benchmark kernel reproduces the official expected values on the official inputs."""

import unittest
from pathlib import Path

from mncompile.bench import problems as P
from mncompile.bench.official import logical_case
from mncompile.oracle import run_reference
from mncompile.values import matches, round_to

BENCH = Path(__file__).resolve().parents[1] / "benchmarks"


def kernel_path(problem):
    folder = "challenge" if problem.directory.parent.name == "challenge" else "mnist"
    return BENCH / folder / f"{problem.slug}.py"


class KernelSemantics(unittest.TestCase):
    def check(self, problem):
        source = kernel_path(problem).read_text()
        for testcase in problem.testcases:
            inputs, expected, atol = logical_case(problem, testcase)
            got = run_reference(source, problem.contract.inputs, problem.contract.outputs, inputs)
            for spec in problem.contract.outputs:
                bad = 0
                for index, want in expected[spec.name].items():
                    have = got[spec.name].get(index)
                    if have is not None and spec.dtype.is_float:
                        have = round_to(have, spec.dtype.bits)
                    if have is None or not matches(have, want, spec.dtype, max(atol[spec.name], 1e-9 * abs(want) if isinstance(want, float) else 0)):
                        bad += 1
                        if bad < 4:
                            print(problem.name, spec.name, index, "want", want, "got", have)
                self.assertEqual(bad, 0, problem.name)

    def test_all(self):
        for problem in P.challenge_problems() + P.mnist_problems():
            with self.subTest(problem=problem.name):
                self.check(problem)


if __name__ == "__main__":
    unittest.main()
