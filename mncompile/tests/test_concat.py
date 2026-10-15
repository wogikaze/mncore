"""Tests for the concat analysis: `sep.join(f(i) for i in range(a, b))`."""

import unittest
from pathlib import Path

from mncompile.concat import Number, analyze_concat, render
from mncompile.compiler import traced_outputs
from mncompile.errors import CompileError
from mncompile.strsym import ConcatStr
from mncompile import trace

ROOT = Path(__file__).resolve().parents[2]


def plan_of(source):
    graph, result = trace.trace(source, [])
    assert isinstance(result, ConcatStr)
    return analyze_concat(result.concat), result


class ConcatTest(unittest.TestCase):
    def test_fizzbuzz(self):
        src = (ROOT / "mncompile/benchmarks/challenge/fizzbuzz.py").read_text()
        plan, result = plan_of(src)
        self.assertEqual(plan.period, 15)
        self.assertEqual([(b.lo, b.hi) for b in plan.blocks], [(1, 10), (10, 100), (100, 1000), (1000, 6335)])
        self.assertEqual([b.period_bytes for b in plan.blocks], [55, 63, 71, 79])
        self.assertEqual(plan.numbers, [Number(1, 0)])
        leaf_parts = {leaf.parts for leaf in plan.leaves}
        self.assertTrue({("FizzBuzz",), ("Fizz",), ("Buzz",), (0,)} <= leaf_parts)
        starts = [b.base + b.period_bytes * ((b.lo - plan.start) // plan.period)
                  + b.offsets[(b.lo - plan.start) % plan.period] for b in plan.blocks]
        self.assertEqual(starts, [0, 30, 408, 4668])
        self.assertEqual(plan.length, 32766)
        self.assertEqual(render(plan), str(result))

    def test_period_one(self):
        src = 'def kernel():\n    return "\\n".join(str(i) for i in range(5, 120))\n'
        plan, result = plan_of(src)
        self.assertEqual(plan.period, 1)
        self.assertEqual(len(plan.blocks), 3)
        self.assertEqual(render(plan), str(result))

    def test_select_item(self):
        src = ('def kernel():\n    return ",".join("ab" if i % 4 == 0 else str(3 * i)'
               ' for i in range(0, 50))\n')
        plan, result = plan_of(src)
        self.assertEqual(plan.period, 4)
        self.assertEqual(plan.numbers, [Number(3, 0)])
        self.assertEqual(render(plan), str(result))

    def test_non_affine_rejected(self):
        src = 'def kernel():\n    return "".join(str(i * i) for i in range(1, 100))\n'
        graph, result = trace.trace(src, [])
        self.assertIsInstance(result, ConcatStr)
        with self.assertRaises(CompileError):
            analyze_concat(result.concat)

    def test_listcomp_nested_def(self):
        src = (
            'def kernel():\n'
            '    def w(i):\n'
            '        if i % 3 == 0:\n'
            '            return "x"\n'
            '        return str(i)\n'
            '    return "\\n".join([w(i) for i in range(1, 40)])\n'
        )
        plan, result = plan_of(src)
        self.assertEqual(plan.period, 3)
        self.assertEqual(render(plan), str(result))

    def test_traced_outputs(self):
        from mncompile.bench import problems

        problem = next(p for p in problems.challenge_problems() if p.slug == "fizzbuzz")
        contract = problems.contract_for(problem)
        src = problems.kernel_source(problem)
        graph, outputs = traced_outputs(src, contract)
        name = contract.outputs[0].name
        self.assertIn(name, outputs.concat)
        reference = trace.load_reference(src)()
        values = [outputs[name][idx].value for idx in sorted(outputs[name])]
        self.assertEqual(values, list(reference.encode("latin-1")))


if __name__ == "__main__":
    unittest.main()
