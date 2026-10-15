"""Bank splitting preserves masked merges and restores buffered output lanes."""

import unittest

from mncompile.compiler import local_strategy, traced_outputs
from mncompile.layout import Contract, parse_tensor
from mncompile.machine import emit
from mncompile.schedule import schedule
from mncompile.sim import assembler
from mncompile.verify import verify


class AlternatingOutputBanks(unittest.TestCase):
    def test_offset_and_in_place_with_partial_group(self):
        source = "def kernel(x):\n    return [abs(v) for v in x]\n"
        for memory in ("$ln[32:58]", "$lm[0:26]"):
            with self.subTest(output=memory):
                inp = parse_tensor("x", "Int", "$lm[0:26]", "/((13:1, 2_W:1))", low=-127, high=127)
                out = parse_tensor("y", "Int", memory, "/((13:1, 2_W:1))")
                contract = Contract([inp], [out])
                _, outputs = traced_outputs(source, contract)
                candidates = local_strategy(source, contract, outputs)
                if out.space == inp.space:
                    self.assertFalse(any("alternating" in name for name, _ in candidates))
                    program = next(p for name, p in candidates if "staged" in name)
                else:
                    program = next(p for name, p in candidates if "alternating" in name)
                vsm = emit(schedule(program, assembler()))
                values = {"x": {(i,): (-127, -1, 0, 1, 127)[i % 5] for i in range(26)}}
                result = verify(vsm, source, contract, cases=0, backend="official", extra_values=[values])
                self.assertTrue(result.ok, result.summary())
