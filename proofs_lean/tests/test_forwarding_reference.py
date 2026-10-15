import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_forwarding_reference import check_values, classify, program


class ForwardingReferenceProtocolTests(unittest.TestCase):
    def test_unrelated_crash_is_not_a_known_forwarding_failure(self):
        self.assertEqual(classify(-6, "RuntimeError: bad floating-point format"), "unclassified_runtime_error")
        self.assertEqual(classify(-9, "OOM killed"), "unclassified_runtime_error")
        self.assertEqual(classify(-6, "Accessing to IALU forwarding register failed. IALU is disabled\nRuntimeError"), "failure")

    def test_long_mask_and_flush_do_not_disable_all_writes(self):
        long_mask, dump = program("alu", "disabled-long-off")
        self.assertIn("lpassa $aluf $lls64v/0000p", long_mask)
        flush, _ = program("alu", "disabled-flush-off")
        self.assertIn("lpassa/ll0000 $aluf $lls64v", flush)
        masked, _ = program("alu", "disabled-mask-off")
        self.assertIn("lpassa $aluf $lls64v/ll0000", masked)
        self.assertTrue(dump)

    def test_discard_chain_forces_the_poison_later(self):
        text, dump = program("mau", "disabled-chain")
        self.assertIn("lpassa $mauf $nowrite\nlpassa $aluf $lls64v", text)
        self.assertTrue(dump)
        _, discard_dump = program("mau", "disabled-discard")
        self.assertFalse(discard_dump)

    def test_value_check_requires_every_cycle_and_correct_addresses(self):
        output = "\n".join(f"DEBUG-GREG1(n0c0b0m0p0,{64+2*i}):(v:0x{1 if i%2==0 else 2:X}) #dump" for i in range(8))
        self.assertTrue(check_values(output, 1, 2))
        self.assertFalse(check_values(output.replace("p0,66", "p0,64"), 1, 2))
        self.assertFalse(check_values("\n".join(output.splitlines()[:-1]), 1, 2))


if __name__ == "__main__":
    unittest.main()
