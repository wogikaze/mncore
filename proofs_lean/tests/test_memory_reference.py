import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_memory_reference import initial_payload, observations, program


class MemoryReferenceProtocolTests(unittest.TestCase):
    def vectors(self, bank="m", operand="$m0v"):
        return "\n".join(f"0\t{bank}\t{operand}\t{cycle}\t{cycle}\t{cycle+1}\t0" for cycle in range(4))

    def test_four_cycles_and_both_longwords(self):
        text, expected = program(self.vectors())
        self.assertEqual(expected, [1, 0, 2, 0, 3, 0, 4, 0])
        self.assertIn("lpassa $m0v $lls64v", text)
        self.assertIn("d get $ls64n0c0b0m0p0 8", text)
        output = "\n".join(f"DEBUG-GREG1(n0c0b0m0p0,{64+2*i}):(v:0x{x:X}) #dump" for i, x in enumerate(expected))
        self.assertEqual(observations(output, 8), expected)
        with self.assertRaises(ValueError):
            observations(output.replace("m0p0,66", "m0p0,64"), 8)

    def test_t_initialization_uses_full_cycle_writes(self):
        text, _ = program(self.vectors("t", "$t"))
        self.assertIn("lpassa $llr0v $t", text)
        self.assertNotIn("d set $lt", text)
        self.assertEqual(initial_payload(2), "12345678124DBC85")

    def test_rejects_incomplete_or_reordered_cycles(self):
        with self.assertRaises(ValueError):
            program("\n".join(self.vectors().splitlines()[:3]))
        with self.assertRaises(ValueError):
            program("\n".join(reversed(self.vectors().splitlines())))


if __name__ == "__main__":
    unittest.main()
