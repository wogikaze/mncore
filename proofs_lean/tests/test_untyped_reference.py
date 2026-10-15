import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_untyped_reference import observations, program


class UntypedReferenceProtocolTests(unittest.TestCase):
    def vectors(self):
        return "\n".join(f"0\tmsl\t0\t{pe}\t{pe+1}\t99\t{(pe+3)%4+1}\t0\t0" for pe in range(4))

    def output(self):
        lines = []
        for pe in range(4):
            lines.extend([f"DEBUG-GREG0(n0c0b0m0p{pe},8):(v:0x{(pe+3)%4+1:X}) #dump",
                          f"DEBUG-GREG0(n0c0b0m0p{pe},10):(v:0x0) #dump",
                          *[f"DEBUG-OMR(n0c0b0m0p{pe},1):Mask{{0}} #dump"] * 4])
        return "\n".join(lines)

    def test_checks_all_four_pes_and_distinct_rotated_values(self):
        _, expected = program(self.vectors())
        self.assertEqual(observations(self.output(), 4), expected)

    def test_rejects_missing_or_reordered_pe(self):
        with self.assertRaises(ValueError):
            program("\n".join(self.vectors().splitlines()[:3]))
        with self.assertRaises(ValueError):
            program("\n".join(reversed(self.vectors().splitlines())))
        with self.assertRaises(ValueError):
            observations(self.output().replace("m0p2,8", "m0p1,8"), 4)

    def test_uses_nonzero_destination_and_mask_sentinels(self):
        text, _ = program(self.vectors())
        self.assertIn("d set $lr10n0c0b0m0p3 1 FFFFFFFFFFFFFFFF", text)
        self.assertIn("d set $omr1n0c0b0m0p3 1 000000000000FFFF", text)
        self.assertIn("msl $llr0 $llr8 $omr1", text)


if __name__ == "__main__":
    unittest.main()
