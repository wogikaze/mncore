import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_alu_reference import observations, program


class ReferenceProtocolTests(unittest.TestCase):
    def output(self, masks=(12, 12, 12, 12)):
        return "\n".join([
            "DEBUG-GREG0(n0c0b0m0p0,8):(v:0x1234) #dump",
            "DEBUG-GREG0(n0c0b0m0p0,10):(v:0x5678) #dump",
            *(f"DEBUG-OMR(n0c0b0m0p0,1):Mask{{{mask}}} #dump" for mask in masks),
        ])

    def test_reads_high_low_and_all_cycles(self):
        self.assertEqual(observations(self.output(), 1), [(0x1234, 0x5678, 12)])

    def test_rejects_missing_debug_records(self):
        with self.assertRaises(ValueError):
            observations(self.output(masks=(12,)), 1)

    def test_rejects_inconsistent_cycle_flags(self):
        with self.assertRaises(ValueError):
            observations(self.output(masks=(12, 12, 3, 12)), 1)

    def test_rejects_wrong_pe_or_address(self):
        with self.assertRaises(ValueError):
            observations(self.output().replace("m0p0,8", "m0p1,8"), 1)

    def test_binary_inputs_use_separate_banks_and_nonoverlapping_words(self):
        text, expected = program("ladd\ttrue\t1\t2\t3\t81985529216486895\t15\n")
        self.assertIn("d set $lr2n0c0b0m0p0 1 0123456789ABCDEF", text)
        self.assertIn("d set $ls4n0c0b0m0p0", text)
        self.assertIn("ladd $llr0 $lls4 $llr8 $omr1", text)
        self.assertEqual(expected, [(3, 0x0123456789abcdef, 15)])


if __name__ == "__main__":
    unittest.main()
