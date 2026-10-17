import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check import expected_axiom_reports, validate_axioms, validate_source


class ProofGate(unittest.TestCase):
    def test_unproved_assumptions_are_rejected(self):
        for escape in ("axiom fabricated : False", "example : False := by sorry",
                       "example : False := by admit", "unsafe def fabricated := true",
                       "example : 1 = 1 := by native_decide",
                       "example : 1 = 1 := by decide +native",
                       "example : 1 = 1 := by decide (config := { native := true })"):
            with self.subTest(escape=escape), self.assertRaises(ValueError):
                validate_source(escape, "bad.lean")

    def test_bv_decide_is_permitted(self):
        validate_source("import Std.Tactic.BVDecide\n"
                        "theorem t (x : BitVec 8) : x &&& x = x := by bv_decide",
                        "good.lean")

    def test_comments_and_strings_do_not_create_false_alarms(self):
        validate_source('/- sorry /- axiom -/ admit -/\n-- unsafe\ndef name := "sorry"', "good.lean")

    def test_mathlib_imports_are_allowed_but_lookalikes_are_rejected(self):
        validate_source("import Mathlib", "good.lean")
        validate_source("import Mathlib.Data.Fintype.Card", "good.lean")
        for module in ("Mathlibx.Foo", "Aesop", "Batteries.Data.List.Basic"):
            with self.subTest(module=module), self.assertRaises(ValueError):
                validate_source(f"import {module}", "bad.lean")

    def test_legacy_olean_cannot_be_imported(self):
        with self.assertRaisesRegex(ValueError, "stale import"):
            validate_source("import ProofsLean.Pkg12", "bad.lean")

    def test_label_is_not_a_certificate(self):
        with self.assertRaises(ValueError):
            validate_source("inductive Verdict where | optimalProven", "bad.lean")

    def test_kernel_escape_is_rejected(self):
        good = "'theorem' depends on axioms: [propext, Quot.sound]\n" * 11
        validate_axioms(good, 11)
        for name in ("sorryAx", "Lean.trustMeBro", "madeUpLowerBound"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_axioms(good.replace("propext", name, 1), 11)

    def test_bv_decide_axiom_report_is_accepted(self):
        validate_axioms(
            "'t' depends on axioms: [propext, Classical.choice, Quot.sound]\n", 1)
        validate_axioms(
            "'t' depends on axioms: [propext, Classical.choice, Quot.sound,"
            " t._native.bv_decide.ax_1_5]\n", 1)
        for name in ("t._native.bv_decide.ax_", "t._native.bv_decide.ax_1_5.evil",
                     "_native.bv_decide.ax_1"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                validate_axioms(f"'t' depends on axioms: [propext, {name}]\n", 1)

    def test_missing_axiom_report_is_rejected(self):
        with self.assertRaises(ValueError):
            validate_axioms("", 1)
        with self.assertRaises(ValueError):
            validate_axioms("'t' depends on axioms: [propext]\n" * 2, 3)

    def test_expected_reports_follow_check_source(self):
        source = ("import ProofsLean\n#print axioms A.b\n-- #print axioms C.d\n"
                  "/- #print axioms E.f -/\n#print axioms G.h\n")
        self.assertEqual(expected_axiom_reports(source), 2)
        with self.assertRaises(ValueError):
            expected_axiom_reports("import ProofsLean\n")

    def test_repository_check_source_is_countable(self):
        root = Path(__file__).resolve().parents[1]
        self.assertGreater(expected_axiom_reports((root / "Check.lean").read_text()), 0)
