import json
import os
import struct
import unittest
from pathlib import Path

from mncompile import GlobalTensor, Tensor, compile_program
from mncompile.reference_audits import audit_references, execute

SOURCES = Path(__file__).parent / "benchmarks/challenge"
ASSEMBLER = os.environ.get("MNCORE_ASSEMBLER")
EMULATOR = os.environ.get("MNCORE_EMULATOR")


@unittest.skipUnless(ASSEMBLER and EMULATOR, "Set official assembler/emulator paths")
class ReferenceAuditTests(unittest.TestCase):
    def test_counterexamples_reproduce_and_generated_programs_fix_them(self):
        report = audit_references(ASSEMBLER, EMULATOR)
        recorded = json.loads((SOURCES / "reference-audits.json").read_text())
        self.assertEqual(report, recorded)
        bindings = json.loads((SOURCES / "bindings.json").read_text())
        for slug, audit in report["audits"].items():
            self.assertEqual(audit["status"], "counterexample")
            contract = bindings[slug]
            output_type = GlobalTensor if "group" in contract["output"] else Tensor
            compiled = compile_program(
                (SOURCES / f"{slug}.py").read_text(),
                inputs={
                    name: Tensor(**spec) for name, spec in contract["inputs"].items()
                },
                output=output_type(**contract["output"]),
                row_partition=contract.get("row_partition", "local"),
                atol=contract.get("atol"),
                assembler=ASSEMBLER,
            )
            words = execute(
                ASSEMBLER,
                EMULATOR,
                audit["input_debug_vsm"] + compiled.vsm + audit["output_debug_vsm"],
            )
            if slug == "plus_two":
                self.assertEqual([int(word, 16) for word in words], [2] * 20)
            elif slug == "fle":
                self.assertEqual([int(word, 16) for word in words], [0] * 20)
            else:
                # Check the complete output, not only the known failing element.
                values = [1.0] * 64
                values[8] = -0.0
                expected = [
                    values[row * 8 + col] for col in range(8) for row in range(8)
                ]
                self.assertEqual(
                    [struct.unpack(">d", bytes.fromhex(word))[0] for word in words],
                    expected,
                )


if __name__ == "__main__":
    unittest.main()
