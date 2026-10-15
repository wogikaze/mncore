"""The layout engine must reproduce every official testcase's physical placement."""

import unittest
from collections import defaultdict

from mncompile.bench import problems as P
from mncompile.bench.testcase import parse_entries
from mncompile.layout import parse_layout


class LayoutNotation(unittest.TestCase):
    def test_parse_examples(self):
        lay = parse_layout("(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])")
        self.assertEqual(lay.logical_shape, (256, 16))
        self.assertEqual([d.axis for d in lay.broadcast], ["MAB"])
        self.assertEqual(parse_layout("/((8:1, 2_W:1))").logical_shape, (16,))
        self.assertEqual(parse_layout("(256)/ ((4_L2B:2, 32:1, 2_W:1))").logical_shape, (256,))


class OfficialPlacement(unittest.TestCase):
    def check_problem(self, problem):
        contract = problem.contract
        tensors = {f"in{i}": t for i, t in enumerate(contract.inputs)}
        tensors |= {f"out{i}": t for i, t in enumerate(contract.outputs)}
        for path in problem.testcases:
            entries = parse_entries(path.read_text())
            seen = defaultdict(set)
            for entry in entries:
                spec = tensors[entry.tensor]
                for lane, index in enumerate(entry.indices):
                    if len(index) < len(spec.shape):
                        index = tuple(index) + (0,) * (len(spec.shape) - len(index))
                    if entry.kind == "get":
                        locs = spec.locations(index, replicate=False)
                        self.assertEqual(len(locs), 1, entry.raw)
                        loc = locs[0]
                        word = loc.addr if spec.space == "dram" else loc.addr * 2
                        self.assertEqual((loc.pe, word, loc.lane), (entry.pes[0], entry.addr, lane), entry.raw)
                    else:
                        for pe in entry.pes:
                            seen[(entry.tensor, index)].add((pe, entry.addr, lane))
            for (name, index), got in seen.items():
                spec = tensors[name]
                want = {
                    (loc.pe, loc.addr if spec.space == "dram" else loc.addr * 2, loc.lane)
                    for loc in spec.locations(index, replicate=True)
                }
                if spec.space == "dram":
                    # DRAM inputs: the testcase may also place copies in other groups.
                    self.assertTrue(want <= got, (problem.name, name, index, sorted(want)[:4], sorted(got)[:4]))
                else:
                    self.assertEqual(want, got, (problem.name, name, index, sorted(want)[:4], sorted(got)[:4]))

    def test_challenge(self):
        for problem in P.challenge_problems():
            with self.subTest(problem=problem.name):
                self.check_problem(problem)

    def test_mnist(self):
        for problem in P.mnist_problems():
            with self.subTest(problem=problem.name):
                self.check_problem(problem)


if __name__ == "__main__":
    unittest.main()
