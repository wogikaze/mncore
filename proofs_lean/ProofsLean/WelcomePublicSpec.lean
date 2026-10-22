import ProofsLean.WelcomeWholeMachineOptimal

/-! # The public Welcome problem: specification, correctness, optimality

## What the public statement actually asks

`problems/challenge/1.plus-one/problem.md` (snapshot fetched 2026-10-14) ends
with these two normative lines:

```
## Inputs

* \(X\) (\(0 \le X[{i}] \le 50\)): Int `$lm[0:16]`, `/((8:1, 2_W:1); B@[PE,MAB,L1B,L2B])`

## Outputs

* \(Y\): Int `$ln[0:16]`, `/((8:1, 2_W:1))`
```

Three facts follow, and they settle the two doubts raised in
`research/experiments/audit/REPORT.md` §1.3.

1. **The domain is bounded.**  `0 ≤ X[i] ≤ 50` is part of the public input
   description, so the public domain is *not* all of `PlusOne.Words`
   (`Fin 16 → BitVec 32`); it is `fun input => ∀ i, (input i).toNat ≤ 50`,
   which is exactly `welcomeSpec.admissible`.  (The audit report's Caveat 1,
   "the public problem statement has no such bound", is not correct for the
   fetched page: the bound is in the `## Inputs` line quoted above.  The prose
   *body* of the page does not repeat it, which may be what the audit read.)
2. **The input is broadcast over every PE.**  The `B@[PE,MAB,L1B,L2B]`
   annotation broadcasts the 16 words along the PE, MAB, L1B and L2B axes, so
   every PE starts with the same 16 LM0 words; that is precisely
   `welcomeInitialState`.  `(8:1, 2_W:1)` means "two 32-bit words inside each
   long word, eight consecutive long words", i.e. the consecutive words
   `0..15`; `problems/17.dram-dl-256-16/problem.md` spells this notation out.
3. **The observed output is PE 0's 16 LM1 words.**  `testcase.vsm` checks
   exactly

   ```
   d getd $ln0n0c0b0m0p0 1 ... d getd $ln14n0c0b0m0p0 1
   ```

   The explicit `p0` coordinate selects PE 0; the "coordinate may be omitted"
   expansion of the emulator tutorial (`p[0:3]は省略可能`, i.e. an *omitted*
   `p` is expanded over the four PEs of a MAB) does not apply to a coordinate
   that is written out.  The output layout `/((8:1, 2_W:1))` carries no `PE`
   axis and no broadcast annotation, consistent with a single 16-word tensor
   read at the canonical location `n0c0b0m0p0`.  So the judged postcondition
   is PE 0 only — again exactly `welcomeSpec.post`.

Consequently `welcomePublicSpec` below is *definitionally* `welcomeWholeSpec`,
and the already unconditional theorems `welcomeWholeMachine_correct` and
`welcomeWholeMachine_lowerBound_two` are already the public theorems.  The
audit's Caveat 1 is void; Caveat 2 is factually right about the testcase but is
not a gap, because PE-0-only *is* the public check.

## The stronger statements

A reader who insists that "add one to 16 32-bit integers" is mathematically
about all 32-bit values, or that a broadcast input should be computed in every
PE, is asking for a strictly harder specification.  We prove all four
combinations, with the same two-line program:

| specification | domain | observed |
|---|---|---|
| `welcomePublicSpec` | `0..50` | PE 0 (`welcomeSpec`) |
| `welcomePublicSpecBoundedAllPEs` | `0..50` | every PE |
| `welcomePublicSpecUnbounded` | all 32-bit words | PE 0 |
| `welcomePublicSpecAllPEs` | all 32-bit words | every PE |

The lower bound transfers to each harder specification because a larger domain
and a stronger postcondition only make `Correct` harder
(`lowerBound_of_harder_spec`).  Hence the two-line answer is optimal under every
reading of the public statement, not only under the literal one.

No `sorry`, no `admit`, no `native_decide`, no new axioms: the two value
proofs are the same four-cycle `.long` load/increment/store readback argument as
`welcomeAnswer_correct`, generalised from `welcomePE` to an arbitrary `PEId` and
with the `0..50` hypothesis dropped (it was never used).
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The literal public specification -/

/-- The specification the public plus-one statement asks for, read from
`problems/challenge/1.plus-one/problem.md` (`X`, `0 ≤ X[i] ≤ 50`, broadcast
over `PE, MAB, L1B, L2B`) and from `testcase.vsm` (the eight `d getd
$ln…n0c0b0m0p0` reads, i.e. PE 0's 16 LM1 words).

* domain: the 16 input words are in `0..50` (the public `## Inputs` bound);
* initial state: every PE carries those 16 words in LM0 and is otherwise zero,
  which is the broadcast `B@[PE,MAB,L1B,L2B]` input;
* postcondition: PE 0's LM1 word `i` is the wrapping 32-bit successor of input
  word `i`. -/
noncomputable def welcomePublicSpec : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun input => ∀ i : Fin 16, (input i).toNat ≤ 50
  initial := fun input => HazardAwareState.initial (welcomeInitialState input)
  post := fun input state => ∀ i : Fin 16,
    (state.machine.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1

/-- The public specification is the specification already proved optimal: the
bounded domain and the PE-0 postcondition of `welcomeSpec`, transported to the
hazard-aware machine. -/
theorem welcomePublicSpec_eq_welcomeWholeSpec : welcomePublicSpec = welcomeWholeSpec := rfl

/-- **Correctness for the public specification.**  Re-export of
`welcomeWholeMachine_correct` through the definitional equality of the two
specifications. -/
theorem welcomePublicMachine_correct :
    ProofsLean.Correct welcomeWholeMachine welcomePublicSpec welcomeAnswer := by
  rw [welcomePublicSpec_eq_welcomeWholeSpec]
  exact welcomeWholeMachine_correct

/-- **`LowerBound welcomeWholeMachine welcomePublicSpec 2`.**  Re-export of the
unconditional two-line lower bound. -/
theorem welcomePublicMachine_lowerBound_two :
    ProofsLean.LowerBound welcomeWholeMachine welcomePublicSpec 2 := by
  rw [welcomePublicSpec_eq_welcomeWholeSpec]
  exact welcomeWholeMachine_lowerBound_two

/-- **`Optimal welcomeWholeMachine welcomePublicSpec welcomeAnswer`**, i.e.
optimality for the specification the public statement literally asks for. -/
theorem welcomePublicMachine_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomePublicSpec welcomeAnswer := by
  rw [welcomePublicSpec_eq_welcomeWholeSpec]
  exact welcomeWholeMachine_optimal

/-! ## 2. Reading a Welcome line back at an arbitrary PE

`welcomeLineReadback` (`WelcomeOptimal.lean`) is stated for `welcomePE`.  The
underlying commit lemma is PE-generic, so the readback is too.  This is the only
new value lemma the stronger specifications need. -/

/-- Reading a word back from the four committed writes of line `base` at an
arbitrary PE returns the increment of that PE's LM0 source word. -/
theorem welcomeLineReadbackAt (pe : PEId) (base : Nat) (bounded : base = 0 ∨ base = 8)
    (state next : State) (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerInstructionLine (.pe [(welcomeExpr base)])
      state = .ok next)
    (word : Fin 16) (cycle : Fin 4) (index : Fin 4)
    (startEq : (welcomeDestinationAddress base cycle).val = welcomeWordLongStart word)
    (indexEq : index.val = word.val % 2) :
    (next.peRegisters pe).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
    ProofsLean.MNCore.PlusOne.increment
      ((state.peRegisters pe).lm0
        ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩) := by
  have value := welcome_executeIntegerProducerInstructionLine_peRegisters base state next
    invariant executed pe
  have read := welcomeCommit_readback_word (state.peRegisters pe) (state.peRegisters pe)
    base bounded word cycle index startEq indexEq
  rw [← readDirectAccess_welcomeWord (next.peRegisters pe) word, value]
  exact read

/-! ## 3. All inputs, every PE: the strongest value theorem -/

/-- **The two accepted lines compute `n_i = m_i + 1` in every PE for every
32-bit input.**  This is `welcomeAnswer_correct` with the `0..50` hypothesis
removed and `welcomePE` replaced by an arbitrary `PEId`; the bound was unused in
that proof, and the per-PE write equation is uniform (`welcomeSealed_step`). -/
theorem welcomeSealedAnswer_values_allPEs (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ result,
      ProofsLean.execute welcomeSealedMachine welcomeAnswer (welcomeInitialState input) =
        some result ∧
      ∀ (pe : PEId) (i : Fin 16),
        (result.peRegisters pe).lm1
          ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1 := by
  let machineInput : ProofsLean.MNCore.PlusOne.Words := input
  obtain ⟨s1, step1, line1, invariant1, _value1⟩ :=
    welcomeSealed_step 0 (welcomeInitialState machineInput) (welcomeInitialState_invariant input)
  obtain ⟨s2, step2, line2, _invariant2, value2⟩ :=
    welcomeSealed_step 8 s1 invariant1
  refine ⟨s2, ?_, ?_⟩
  · simp only [ProofsLean.execute, welcomeAnswer]
    rw [step1]
    simp [step2]
  · intro pe i
    have hi := i.isLt
    have hdivmod := Nat.div_add_mod i.val 2
    have hmodlt := Nat.mod_lt i.val (by decide : 0 < 2)
    have initialLM0 : ((welcomeInitialState machineInput).peRegisters pe).lm0
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = machineInput i := by
      simpa [welcomeInitialState] using welcomeInitialPERegisters_lm0 machineInput i
    by_cases low : i.val < 8
    · -- word 0..7: line 0 wrote it; line 1 preserves it
      let c : Fin 4 := ⟨i.val / 2, by omega⟩
      have startEq : (welcomeDestinationAddress 0 c).val = welcomeWordLongStart i := by
        rw [welcomeDestinationAddress_val 0 (Or.inl rfl) c]
        simp [welcomeWordLongStart, c]
      have read0 := welcomeLineReadbackAt pe 0 (Or.inl rfl) (welcomeInitialState machineInput) s1
        (welcomeInitialState_invariant input) line1 i c (welcomeWordIndex i)
        startEq rfl
      have preserve := welcomeBase8Writes_preserves_read_literal
        (s1.peRegisters pe) (s1.peRegisters pe)
        (welcomeWordLongAddress i) (welcomeWordIndex i)
        (welcomeWordIndex_lt_two i)
        (by simp [welcomeWordLongAddress, welcomeWordLongStart, welcomeWordIndex]; omega)
      have s2lm1 : (s2.peRegisters pe).lm1
          ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
          (s1.peRegisters pe).lm1
            ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ := by
        rw [← readDirectAccess_welcomeWord (s2.peRegisters pe) i]
        rw [value2 pe]
        rw [preserve]
        rw [readDirectAccess_welcomeWord]
      rw [s2lm1, read0, initialLM0]
      exact ProofsLean.MNCore.PlusOne.increment_eq_add_one (machineInput i)
    · -- word 8..15: line 1 wrote it
      have high : 8 ≤ i.val := by omega
      let c : Fin 4 := ⟨i.val / 2 - 4, by omega⟩
      have startEq : (welcomeDestinationAddress 8 c).val = welcomeWordLongStart i := by
        rw [welcomeDestinationAddress_val 8 (Or.inr rfl) c]
        simp [welcomeWordLongStart, c]
        omega
      have read8 := welcomeLineReadbackAt pe 8 (Or.inr rfl) s1 s2 invariant1 line2 i c
        (welcomeWordIndex i) startEq rfl
      have lm0preserved := welcomeLineLm0Preserved 0 (welcomeInitialState machineInput) s1
        (welcomeInitialState_invariant input) line1 pe
      rw [read8, lm0preserved, initialLM0]
      exact ProofsLean.MNCore.PlusOne.increment_eq_add_one (machineInput i)

/-! ## 4. The two stronger specifications -/

/-- The sealed-machine value specification for all inputs and all PEs.  Used to
derive both stronger whole-machine specifications from one value theorem. -/
noncomputable def welcomeSealedAllPEsSpec : ProofsLean.Problem welcomeSealedMachine where
  admissible := fun _ => True
  initial := welcomeInitialState
  post := fun input state => ∀ (pe : PEId) (i : Fin 16),
    (state.peRegisters pe).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1

/-- `Correct welcomeSealedMachine welcomeSealedAllPEsSpec welcomeAnswer`. -/
theorem welcomeSealedAllPEs_correct :
    ProofsLean.Correct welcomeSealedMachine welcomeSealedAllPEsSpec welcomeAnswer :=
  ⟨trivial, fun input _ => welcomeSealedAnswer_values_allPEs input⟩

/-- All 32-bit inputs, PE 0 observed: the public postcondition without the
public input bound. -/
noncomputable def welcomePublicSpecUnbounded : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun _ => True
  initial := fun input => HazardAwareState.initial (welcomeInitialState input)
  post := fun input state => welcomeSpec.post input state.machine

/-- All 32-bit inputs, every PE observed: the strongest reading of "the same 16
increments are computed by the broadcast PE instruction". -/
noncomputable def welcomePublicSpecAllPEs : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun _ => True
  initial := fun input => HazardAwareState.initial (welcomeInitialState input)
  post := fun input state => ∀ (pe : PEId) (i : Fin 16),
    (state.machine.peRegisters pe).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1

/-- The public `0..50` domain with every PE observed: the remaining reading of
the statement (bounded domain, PE-uniform output). -/
noncomputable def welcomePublicSpecBoundedAllPEs : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun input => ∀ i : Fin 16, (input i).toNat ≤ 50
  initial := fun input => HazardAwareState.initial (welcomeInitialState input)
  post := fun input state => ∀ (pe : PEId) (i : Fin 16),
    (state.machine.peRegisters pe).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1

/-- **Correctness for all inputs and all PEs on the whole machine.**  The
hazard-aware run exists (`welcomeWholeAnswer_execute`), projects onto the sealed
run (`welcomeWholeExecute_project`), and the sealed machine is deterministic, so
the final machine carries the values of `welcomeSealedAnswer_values_allPEs`. -/
theorem welcomePublicAllPEs_correct :
    ProofsLean.Correct welcomeWholeMachine welcomePublicSpecAllPEs welcomeAnswer := by
  refine ⟨trivial, ?_⟩
  intro input _
  obtain ⟨s2, run⟩ := welcomeWholeAnswer_execute input
  have projected := welcomeWholeExecute_project welcomeAnswer welcomeWholeAnswer_noWait
    (HazardAwareState.initial (welcomeInitialState input)) s2 rfl run
  obtain ⟨result, sealedRun, sealedPost⟩ := welcomeSealedAnswer_values_allPEs input
  have projected' : ProofsLean.execute welcomeSealedMachine welcomeAnswer
      (welcomeInitialState input) = some s2.machine := projected
  have same : s2.machine = result := by
    rw [projected'] at sealedRun
    exact Option.some.inj sealedRun
  refine ⟨s2, ?_, ?_⟩
  · exact (welcomeWholeExecute_eq_execute welcomeAnswer
      (HazardAwareState.initial (welcomeInitialState input))).symm.trans run
  intro pe i
  show (s2.machine.peRegisters pe).lm1
    ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = input i + 1
  rw [same]
  exact sealedPost pe i

/-- **Correctness for all inputs, PE 0 observed**: the PE-0 projection of
`welcomePublicAllPEs_correct`. -/
theorem welcomePublicUnbounded_correct :
    ProofsLean.Correct welcomeWholeMachine welcomePublicSpecUnbounded welcomeAnswer := by
  obtain ⟨legal, correct⟩ := welcomePublicAllPEs_correct
  refine ⟨legal, ?_⟩
  intro input _
  obtain ⟨result, run, post⟩ := correct input trivial
  refine ⟨result, ?_, fun i => post welcomePE i⟩
  exact run

/-- **Correctness for the public `0..50` domain with every PE observed**: the
all-PE theorem restricted to the public domain. -/
theorem welcomePublicBoundedAllPEs_correct :
    ProofsLean.Correct welcomeWholeMachine welcomePublicSpecBoundedAllPEs welcomeAnswer := by
  obtain ⟨legal, correct⟩ := welcomePublicAllPEs_correct
  refine ⟨legal, ?_⟩
  intro input _
  exact correct input trivial

/-! ## 5. Transferring the lower bound to a harder specification -/

/-- **A lower bound for an easier specification transfers to a harder one.**
`Correct` is monotone in the specification: a larger domain and a stronger
postcondition make it harder, so every program that is correct for `hard` is
also correct for `easy`, and the bound for `easy` applies. -/
theorem lowerBound_of_harder_spec {m : ProofsLean.Machine}
    {easy hard : ProofsLean.Problem m} {bound : Nat}
    (lower : ProofsLean.LowerBound m easy bound)
    (domain : ∀ input, easy.admissible input → hard.admissible input)
    (initial : ∀ input, hard.initial input = easy.initial input)
    (post : ∀ input state, hard.post input state → easy.post input state) :
    ProofsLean.LowerBound m hard bound := by
  intro program correct
  apply lower program
  refine ⟨correct.1, ?_⟩
  intro input admissible
  obtain ⟨result, run, satisfies⟩ := correct.2 input (domain input admissible)
  refine ⟨result, ?_, post input result satisfies⟩
  rw [← initial input]
  exact run

/-- **`LowerBound welcomeWholeMachine welcomePublicSpecUnbounded 2`.**  The
public lower bound transferred to the unbounded domain (the postcondition is
unchanged). -/
theorem welcomePublicUnbounded_lowerBound_two :
    ProofsLean.LowerBound welcomeWholeMachine welcomePublicSpecUnbounded 2 :=
  lowerBound_of_harder_spec welcomeWholeMachine_lowerBound_two
    (fun _ _ => trivial) (fun _ => rfl) (fun _ _ satisfies => satisfies)

/-- **`LowerBound welcomeWholeMachine welcomePublicSpecAllPEs 2`.**  The public
lower bound transferred to the unbounded all-PE specification (PE 0 is one of
the observed PEs). -/
theorem welcomePublicAllPEs_lowerBound_two :
    ProofsLean.LowerBound welcomeWholeMachine welcomePublicSpecAllPEs 2 :=
  lowerBound_of_harder_spec welcomeWholeMachine_lowerBound_two
    (fun _ _ => trivial) (fun _ => rfl) (fun _ _ satisfies => satisfies welcomePE)

/-- **`LowerBound welcomeWholeMachine welcomePublicSpecBoundedAllPEs 2`.**  The
public bounded lower bound transferred to the bounded all-PE specification. -/
theorem welcomePublicBoundedAllPEs_lowerBound_two :
    ProofsLean.LowerBound welcomeWholeMachine welcomePublicSpecBoundedAllPEs 2 :=
  lowerBound_of_harder_spec welcomeWholeMachine_lowerBound_two
    (fun _ admissible => admissible) (fun _ => rfl)
    (fun _ _ satisfies => satisfies welcomePE)

/-! ## 6. Optimality under the stronger readings -/

theorem welcomeAnswer_wholeScore : ProofsLean.score welcomeWholeMachine welcomeAnswer = 2 := by
  simp [welcomeAnswer, ProofsLean.score, welcomeWholeMachine, InstructionLine.cost]

/-- **`Optimal` for all inputs and every PE.** -/
theorem welcomePublicAllPEs_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomePublicSpecAllPEs welcomeAnswer := by
  refine ⟨welcomePublicAllPEs_correct, ?_⟩
  rw [welcomeAnswer_wholeScore]
  exact welcomePublicAllPEs_lowerBound_two

/-- **`Optimal` for all inputs, PE 0 observed.** -/
theorem welcomePublicUnbounded_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomePublicSpecUnbounded welcomeAnswer := by
  refine ⟨welcomePublicUnbounded_correct, ?_⟩
  rw [welcomeAnswer_wholeScore]
  exact welcomePublicUnbounded_lowerBound_two

/-- **`Optimal` for the public `0..50` domain with every PE observed.** -/
theorem welcomePublicBoundedAllPEs_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomePublicSpecBoundedAllPEs welcomeAnswer := by
  refine ⟨welcomePublicBoundedAllPEs_correct, ?_⟩
  rw [welcomeAnswer_wholeScore]
  exact welcomePublicBoundedAllPEs_lowerBound_two

/-! ## 7. Axiom report -/

#print axioms welcomePublicMachine_correct
#print axioms welcomePublicMachine_lowerBound_two
#print axioms welcomePublicMachine_optimal
#print axioms welcomePublicAllPEs_correct
#print axioms welcomePublicUnbounded_correct
#print axioms welcomePublicAllPEs_lowerBound_two
#print axioms welcomePublicUnbounded_lowerBound_two
#print axioms welcomePublicAllPEs_optimal
#print axioms welcomePublicUnbounded_optimal
#print axioms welcomePublicBoundedAllPEs_correct
#print axioms welcomePublicBoundedAllPEs_lowerBound_two
#print axioms welcomePublicBoundedAllPEs_optimal

end ProofsLean.MNCore
