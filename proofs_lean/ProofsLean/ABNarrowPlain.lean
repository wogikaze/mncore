import ProofsLean.ABLowerBound
import ProofsLean.PlainALUDestination

/-! # The narrow `1.a-b` refutation, instantiated for the `iinc` one-liner

`ProofsLean/ABLowerBound.lean` proves the `1.a-b` narrow value argument
(`ab_not_correct_of_narrowAtOnes`): a line whose PE 0 write list at the input
`A = 1.0, B = 0` is covered by at most four windows of at most two words leaves
an observed word at its initial `0` and is therefore incorrect.

This module produces that shape for one concrete plain-ALU family: the single
Welcome `iinc` row `iinc $lm<base>v $ln<base>v`.  Its four committed `.long`
writes are known at **every** state
(`welcome_executeIntegerProducerInstructionLine_peRegisters`, whose only
hypothesis is the mask/BAR invariant), and each write's destination is
`some (welcomeDestinationAccess base cycle)`, i.e. one of four two-word windows.
This is the `1.a-b` instance of the state-general destination analysis in
`ProofsLean/PlainALUDestination.lean`; the other plain-ALU rows need the
line-level plumbing described there.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- **The `iinc` write list is narrow at the `A = 1.0, B = 0` input.**  The four
committed writes are the four `.long` accesses of the row, so they fit in the
four two-word windows `[welcomeDestinationAddress base 0, ..., base 3]`. -/
theorem abNarrowAtOnes_welcomeExpr (base : Nat) : ABNarrowAtOnes [welcomeExpr base] := by
  intro next step
  have executed : executeNormalizedLine (NormalizedLine.pe [welcomeExpr base])
      (abInitialState abOneLeftInput) = .ok next := abSealed_step_ok step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [welcomeExpr base])
      (abInitialState abOneLeftInput) = .ok next := executed
  refine ⟨[welcomePreparedWrite ((abInitialState abOneLeftInput).peRegisters abPE) base 0,
           welcomePreparedWrite ((abInitialState abOneLeftInput).peRegisters abPE) base 1,
           welcomePreparedWrite ((abInitialState abOneLeftInput).peRegisters abPE) base 2,
           welcomePreparedWrite ((abInitialState abOneLeftInput).peRegisters abPE) base 3],
          [(welcomeDestinationAddress base 0, count .lm1 .long),
           (welcomeDestinationAddress base 1, count .lm1 .long),
           (welcomeDestinationAddress base 2, count .lm1 .long),
           (welcomeDestinationAddress base 3, count .lm1 .long)],
          ?_, ?_, ?_, ?_⟩
  · exact welcome_executeIntegerProducerInstructionLine_peRegisters base
      (abInitialState abOneLeftInput) next (abInitialState_invariant abOneLeftInput)
      lineExecuted abPE
  · intro write member width address destination
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      simp only [welcomePreparedWrite] at destination
      have accessEq : welcomeDestinationAccess base _ = ⟨.lm1, width, address⟩ :=
        Option.some.inj destination
      simp only [welcomeDestinationAccess] at accessEq
      cases accessEq
      simp [count]
  · simp
  · intro window member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> (show count .lm1 .long ≤ 2; decide)

/-- **The `iinc` one-liner is incorrect for `1.a-b`**, obtained by instantiating
the narrow refutation with `abNarrowAtOnes_welcomeExpr`. -/
theorem abPE_singleWelcomeLine_not_correct_of_narrow (base : Nat) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [welcomeExpr base]] : List InstructionLine) :=
  ab_not_correct_of_narrowAtOnes _ (abNarrowAtOnes_welcomeExpr base)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
