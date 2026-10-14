import json
import shutil
import unittest
from pathlib import Path

from mncompile import CompileError, GlobalTensor, Tensor, compile_program

SOURCES = Path(__file__).parent / "benchmarks/challenge"


@unittest.skipUnless(shutil.which("opt"), "LLVM opt is required")
class FrontendTests(unittest.TestCase):
    def test_all_challenge_sources_without_operation_labels(self):
        bindings = json.loads((SOURCES / "bindings.json").read_text())
        self.assertEqual(len(bindings), 25)
        for slug, contract in bindings.items():
            with self.subTest(slug=slug):
                output_type = GlobalTensor if "group" in contract["output"] else Tensor
                compiled = compile_program(
                    (SOURCES / f"{slug}.py").read_text(),
                    inputs={
                        name: Tensor(**spec)
                        for name, spec in contract["inputs"].items()
                    },
                    output=output_type(**contract["output"]),
                    row_partition=contract.get("row_partition", "local"),
                    atol=contract.get("atol"),
                )
                self.assertIn("chosen_lowering", compiled.report)
                self.assertGreater(compiled.report["lines"], 0)

    def test_unsupported_source_is_not_executed_or_replayed(self):
        with self.assertRaises(CompileError):
            compile_program(
                "def kernel(x):\n    return [v//7 for v in x]\n",
                inputs={"x": Tensor("u32", "m", 0, 16, 0, 100)},
                output=Tensor("u32", "n", 0, 16, 0, 100),
            )


if __name__ == "__main__":
    unittest.main()
