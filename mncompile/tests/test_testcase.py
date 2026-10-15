"""Testcase specialization must use the values encoded in the input payload."""

import unittest

from mncompile.bench.testcase import input_values
from mncompile.compiler import narrowed_contract
from mncompile.layout import Contract, parse_tensor
from mncompile.values import round_to


class TestcaseInputs(unittest.TestCase):
    def test_encoded_float_and_short_indices(self):
        spec = parse_tensor("x", "Float", "$lm[0:1]", "(2,1)/((2_W:1), (1:1))", low=-10, high=10)
        contract = Contract([spec], [], {"example": "preserve contract metadata"})
        text = """# ======= In(0) =======
d set $lm0 1 3DCCCCCD3F800000 # values=[0.1,1.0] / Float @[0],[1]
"""
        values = input_values(text, contract)
        self.assertEqual(values, {"x": {(0, 0): round_to(0.1, 32), (1, 0): 1.0}})
        narrowed = narrowed_contract(contract, values)
        self.assertEqual(narrowed.inputs[0].low, round_to(0.1, 32))
        self.assertEqual(narrowed.inputs[0].high, 1.0)
        self.assertEqual(contract.inputs[0].low, -10)
        self.assertEqual(narrowed.notes, contract.notes)

    def test_string_payload_is_numeric(self):
        spec = parse_tensor("x", "String", "$lm[0:1]", "/((8_W:1))")
        text = """# ======= In(0) =======
d set $lm0 1 48656C6C6F212121 # values="Hello!!!" / String @[0],[1],[2],[3],[4],[5],[6],[7]
"""
        self.assertEqual(input_values(text, Contract([spec], [])),
                         {"x": {(i,): c for i, c in enumerate(b"Hello!!!")}})

    def test_missing_input_is_rejected(self):
        spec = parse_tensor("x", "Float", "$lm[0:1]", "/((2_W:1))")
        with self.assertRaisesRegex(ValueError, "leaves 2 elements of x unset"):
            input_values("", Contract([spec], []))
