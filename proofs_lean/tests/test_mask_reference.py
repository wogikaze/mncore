import sys
import unittest
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_mask_reference import mask_input, observations, program


class MaskReferenceProtocolTests(unittest.TestCase):
    def vectors(self, mode="write"):
        return "\n".join(f"0\tl\t{mode}\t0\t{c}\t{c}\t1\t2\t3\t4\t5\t6\t{c+1}\t5\t4" for c in range(4))

    def test_word_and_flag_records_keep_cycle_order(self):
        _, expected = program(self.vectors())
        output = "\n".join([
            *(f"DEBUG-GREG1(n0c0b0m0p0,{64+2*i}):(v:0x{x:X}) #dump" for i, x in enumerate([5,6]*4)),
            *(f"DEBUG-OMR(n0c0b0m0p0,2):Mask{{{c+1}}} #dump" for c in range(4)),
        ])
        self.assertEqual(observations(output, 4), expected)
        with self.assertRaises(ValueError):
            observations(output.replace("p0,2", "p0,1"), 4)

    def test_mask_generator_and_override_are_explicit(self):
        self.assertEqual(mask_input(0), 0x0001000100010001)
        self.assertEqual(mask_input(15), 0)
        text, _ = program(self.vectors("override"))
        self.assertIn("masklls 16", text)
        self.assertIn("spassa $llr32v $lls64v $omr2/$imr1", text)
        text, _ = program(self.vectors("both"))
        self.assertIn("spassa/$imr1 $llr32v $lls64v/$imr1p $omr2", text)

    def test_saved_fixture_covers_every_flag_pattern_in_each_cycle(self):
        covered = defaultdict(set)
        for row in (ROOT / "evidence/masks/vectors.tsv").read_text().splitlines():
            fields = row.split("\t")
            covered[(fields[1], fields[2], fields[4])].add(int(fields[5]))
        self.assertEqual(len(covered), 2 * 6 * 4)
        for flags in covered.values():
            self.assertEqual(flags, set(range(16)))


if __name__ == "__main__":
    unittest.main()
