import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_dynamic_address_reference import observations, program


class DynamicAddressReferenceProtocolTests(unittest.TestCase):
    def vectors(self):
        return "\n".join(
            f"0\tm\t$llmt4092v\t4095\t{0x100000001 + pe * 4 + cycle}\t{pe}\t{cycle}\t0\t{pe*4+cycle+1}\t0"
            for pe in range(4) for cycle in range(4))

    def test_reads_all_pes_and_cycles(self):
        _, expected = program(self.vectors())
        self.assertEqual(expected, [value for n in range(1, 17) for value in (n, 0)])
        output = "\n".join(
            f"DEBUG-GREG1(n0c0b0m0p{(i//8)%4},{64+2*(i%8)}):(v:0x{word:X}) #dump"
            for i, word in enumerate(expected))
        self.assertEqual(observations(output, 32), expected)
        with self.assertRaises(ValueError):
            observations(output.replace("m0p3,64", "m0p2,64"), 32)

    def test_preserves_64_bit_t_values_and_nonzero_low_bus_words(self):
        text, _ = program(self.vectors())
        self.assertIn("0000000100000001A5A5A5A55A5A5A5A", text)
        self.assertIn("d set $ls32n0c0b0m0p3 1 00000FFF00000000", text)
        self.assertIn("lpassa $ls32 $mb", text)
        self.assertIn("lpassa $llmt4092v $lls64v", text)

    def test_rejects_incomplete_or_inconsistent_group(self):
        with self.assertRaises(ValueError):
            program("\n".join(self.vectors().splitlines()[:15]))
        with self.assertRaises(ValueError):
            program(self.vectors().replace("4095\t4294967297", "4094\t4294967297"))


if __name__ == "__main__":
    unittest.main()
