import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_lbf_encoded_reference import pe_words, sources, splice


class EncodedLBFProtocolTests(unittest.TestCase):
    def test_splice_preserves_every_original_word(self):
        producer = "j " + "0" * 426
        consumer = "j " + "1" * 426
        driver = "j " + "01" * 213
        template = "d set $lr0 1 0000000000000000\n" + producer + "\n" + consumer + "\n"
        result = splice(template, driver + "\n")
        self.assertEqual(pe_words(result), [producer, driver, consumer])
        self.assertTrue(result.startswith("d set $lr0"))

    def test_rejects_width_changes_or_mv_words(self):
        for bad in ["j " + "0" * 425, "j " + "2" * 426, "m 000"]:
            with self.assertRaises(ValueError):
                pe_words(bad)

    def test_discard_source_and_driver_remain_distinct(self):
        template, driver, full, dump = sources("disabled-discard")
        self.assertNotIn("\nzero $nowrite\n", template)
        self.assertEqual(driver, "zero $nowrite\n")
        self.assertIn("l1bmm $lb0 $nowrite\nzero $nowrite\nlpassa $lbf $nowrite", full)
        self.assertFalse(dump)

    def test_distinct_new_producer_value_and_noforward(self):
        _, driver, full, dump = sources("noforward-producer-new")
        self.assertIn("4000000000000000", driver)
        self.assertIn("noforward; l1bmm $lb0 $nowrite", full)
        self.assertTrue(dump)


if __name__ == "__main__":
    unittest.main()
