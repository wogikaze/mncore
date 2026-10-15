"""The kernel must reject arithmetic masquerading as optimality and missing ISA coverage."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class NegativeKernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Preflight.lean"
            source.write_text("import ProofsLean\n"
                              "#check ProofsLean.FiniteExample.two_lines_optimal\n"
                              "#check ProofsLean.FiniteExample.fill_correct_on_one_case\n"
                              "#check ProofsLean.FiniteExample.missing_cannot_be_sealed\n"
                              "#check ProofsLean.MNCore.UntypedALU.unresolved_rotation_is_unknown\n"
                              "#check ProofsLean.MNCore.UntypedALU.reference_differs_from_manual_when_lsb_nonzero\n"
                              "#check ProofsLean.MNCore.PEMemory.address_aligned\n"
                              "#check ProofsLean.MNCore.PEMemory.read_after_write\n"
                              "#check ProofsLean.MNCore.Masks.long_write_copies_low\n"
                              "#check ProofsLean.MNCore.Masks.flush_preserves_flags\n"
                              "#check ProofsLean.MNCore.Forwarding.unknown_not_discardable\n"
                              "#check ProofsLean.MNCore.Forwarding.noforward_preserves\n")
            result = subprocess.run([cls.lake, "env", "lean", str(source)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise AssertionError("build the valid semantic models before negative tests:\n" + result.stdout + result.stderr)

    def reject(self, body):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Negative.lean"
            source.write_text("import ProofsLean\nopen ProofsLean ProofsLean.FiniteExample\n" + body)
            result = subprocess.run([self.lake, "env", "lean", str(source)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=60)
            self.assertNotEqual(result.returncode, 0, "invalid proof unexpectedly accepted")
            self.assertIn("error:", result.stdout + result.stderr)
            self.assertNotIn("unknown module", result.stdout + result.stderr)
            self.assertNotIn("Unknown identifier", result.stdout + result.stderr)
            self.assertNotIn("Unknown constant", result.stdout + result.stderr)
            self.assertNotIn("object file", result.stdout + result.stderr)

    def test_arithmetic_equality_does_not_prove_lower_bound(self):
        self.reject("example : LowerBound machine problem 3 := by\n  exact (rfl : 3 = 3)\n")

    def test_omitting_an_instruction_does_not_prove_coverage(self):
        self.reject("example : ∀ line : machine.Line, line ∈ [Line.flipLeft, Line.flipRight] := by\n  intro line\n  cases line <;> decide\n")

    def test_testcase_proof_cannot_be_relabelled_general(self):
        self.reject("example : Correct machine problem [Line.fillTrue] := fill_correct_on_one_case\n")

    def test_unknown_semantics_cannot_be_sealed_as_complete(self):
        self.reject("example : missingSemantics.Complete := by\n  intro line state h\n  cases h\n")

    def test_reference_profile_cannot_resolve_unqualified_rotation(self):
        self.reject("open ProofsLean.MNCore.UntypedALU\n"
                    "example (input : MABInput) (pe : Fin 4) :\n"
                    "  partialEvaluate .msl input pe =\n"
                    "    .ok (evaluateWithPolicy .referenceBinary .msl input pe) := by rfl\n")

    def test_manual_rotation_cannot_be_relabelled_reference_semantics(self):
        self.reject("open ProofsLean.MNCore.UntypedALU\n"
                    "example (input : MABInput) (pe : Fin 4) :\n"
                    "  (evaluateWithPolicy .referenceBinary .msl input pe).value =\n"
                    "    (evaluateWithPolicy .manualReading .msl input pe).value := by rfl\n")

    def test_lm1_cannot_use_t_indirect(self):
        self.reject("open ProofsLean.MNCore.PEMemory\n"
                    "example : Adjustment.Allowed (.tIndirect 1) .lm1 := by decide\n")

    def test_unaligned_static_long_address_is_not_well_formed(self):
        self.reject("open ProofsLean.MNCore.PEMemory\n"
                    "example : Schedule.WellFormed (.auto 1 2) .lm0 .long := by decide\n")

    def test_zero_long_mask_does_not_preserve_entire_old_bus(self):
        self.reject("open ProofsLean.MNCore.Masks\n"
                    "example : writeBus .long 0 ⟨1, 2⟩ ⟨3, 4⟩ = ⟨1, 2⟩ := by decide\n")

    def test_zero_mask_register_write_does_not_preserve_old_flags(self):
        self.reject("open ProofsLean.MNCore.Masks\n"
                    "example : writeRegister (fun _ _ => 15) 0 0 15 0 0 0 = 15 := by decide\n")

    def test_unknown_forwarding_is_not_a_known_execution_failure(self):
        self.reject("open ProofsLean.MNCore.Forwarding\n"
                    "example : consume (.memory true) (Value.unknown : Value Nat) = .failure := by rfl\n")

    def test_discarding_unknown_does_not_complete_unsupported_semantics(self):
        self.reject("open ProofsLean.MNCore.Forwarding\n"
                    "example : consume .discard (Value.unknown : Value Nat) = .ok ⟨⟩ := by rfl\n")

    def test_absent_producer_does_not_prove_all_forwarding_invalid(self):
        self.reject("open ProofsLean.MNCore.Forwarding\n"
                    "example (old : Slots) : advance old (.issue false (fun _ => none)) =\n"
                    "  .ok (fun _ _ => .poison) := by rfl\n")
