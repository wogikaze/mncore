import ProofsLean.PlusTwoLowerBound
import ProofsLean.PlainALUDestination
import ProofsLean.StageCommitSpecific

/-! # The `2.plus-two` suffix: destination analysis and the missing state hypothesis

`ProofsLean/PlusTwoLowerBound.lean` reduces the refutation of the recorded answer
to `PlusTwoSuffixPreservesWitness`: the four remaining lines never write `LM1`
word `19`.  This module reports what that obligation actually needs.

## The obstruction

The `LM1` destination of a plain integer-ALU row is *not* a function of the
expression.  `ParsedOperand.toDirectMemoryAccessMode?` resolves the address as

```
(bar1 + region.address_cycle + madpe) / width.words * width.words % 4096
```

where `bar1 := (state.peContext pe).bar1`, and the executor builds the
`ParsedMaskExecutionControl` of the preparation from `state.peContext`
(`executeIntegerProducerLineAtPECore`).  Consequently

* `prepareParsedIntegerALUExprCycle_destination_state_general` (which holds the
  whole control — hence `bar1` — fixed) can only transport a destination list
  between register files *at the same control*, and
* `PlusTwoSuffixPreservesWitness`, which quantifies over every state, is false:
  the second suffix line has region addresses `5,7,29,13`, so at any state with
  `(state.peContext plusTwoPE).bar1 = 14` its cycle-0 write lands on `LM1` word
  `19`.  `plusTwoSuffixLine2_changes_witness_at_bar1` below exhibits that write.

The `maskRegisters` equality demanded by the general congruence is *not* the
missing ingredient: for a `.mem` destination the write selection never fails
(`resolveParsedMaskSelection?_always_resolves`), so the destination does not
read the mask registers at all — only `bar1` matters.

## What is proved here

* `directDestination_formula` — the exact `LM1` word destination of a direct
  memory operand, for every `bar1`, `cycle`, `bar0` and `tWord`: it is
  `(bar1 + region.address_cycle) % 4096`, one word wide.
* `destination_at_zero_bar` — the same at `bar1 = 0`, and
  `suffixLine2_addresses` … `suffixLine5_addresses` — the four cycle
  destinations of each suffix line are `5,7,29,13`, `31,21,35,17`, `3,1,9,25`,
  `37,23,15,27`; `suffixLine*_avoids_witness` records that none is `19`.
* `plusTwoSuffixLine2_changes_witness_at_bar1` and
  `plusTwoSuffixLine2_perPE_frame_false` — kernel computations showing that the
  second suffix line **does** succeed at `bar1 = 14` and **does** change `LM1`
  word `19`.  Hence the per-PE form of the frame is false, and a fortiori the
  unconditional `PlusTwoSuffixPreservesWitness` (which quantifies over all
  states) cannot be established: the destination is state-relative.
* `plusTwoRecorded_not_correct_of_bar1Frame` — the correctness refutation of the
  recorded answer with the *corrected* frame `PlusTwoSuffixPreservesWitnessOfBar1Zero`
  (`BAR1 = 0` at the observed PE) and `PlusTwoLine1PreservesBar1Zero` (the first
  line keeps `BAR1`; its prepared writes are `LM1`/`GRF0` only, so
  `parsedIntegerALUBarUpdates` is empty).  Both are true statements, unlike the
  unconditional `PlusTwoSuffixPreservesWitness`.
* `plusTwoWideZeroExpr_destinations` and `plusTwoWideZeroLine_changes_eight` —
  a legal `.pe` `zero` row with a width-four `LM1` destination writes words
  `0..15` and changes eight of the twenty observed words, so the per-line bound
  `4` of `PlusTwoLineCoverage` is false (the bound that does hold for such a row
  is eight, and for width one/two destinations it is four).

## What is deliberately *not* claimed

* The corrected suffix frame at the whole-machine `execute` level.  The proof
  needs the destination *list* of
  `prepareParsedIntegerALUCycles` at an arbitrary state.  The obstruction is
  `ParsedOp.executionRequest`: `prepareParsedIntegerALUExprCycle` matches on
  `match hRequest : expression.op.executionRequest with`, and that dependent
  match does not reduce when `expression.op`'s `name`/`precision` are symbolic,
  so the destination branch cannot be projected out of a successful run without
  either (a) proving a structural provenance lemma per operator family by
  reducing `executionRequest` (which needs `ParsedAluName.supportsIntegerAt`
  and `toIntegerOp` unfolded and the dependent match rewritten) or (b) an
  additional hypothesis such as `(state.peContext plusTwoPE).bar1 = 0` plus a
  concrete-control transport from the zero state.
* A refutation of the whole-machine `PlusTwoSuffixPreservesWitness`.  It needs
  a state at which all four suffix lines execute successfully at all `4096` PEs
  and word `19` changes.  The per-PE facts above give the change; the missing
  step is the uniform success of the four `4096`-PE walks (the second line's
  walk alone takes about five minutes of kernel reduction, which is why it is
  not included here).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The direct-memory destination formula -/

/-- **The `LM1` word destination of a direct memory operand.**  For a width-one
region on `LM1` the resolution is `bar1 + region.address_cycle`, rounded to a
word and reduced modulo the bank capacity.  No register file, mask register or
directive is read. -/
theorem directDestination_formula (a b c d : Nat) (pe : Fin 4) (cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryDestination? (plusTwoMem .lm1 a b c d) pe cycle bar0 bar1 tWord).map
      (fun x => (x.bank, x.width, x.address.val)) =
      some (.lm1, .word,
        (bar1.toNat + parsedRegionAddressAt ⟨1, a, b, c, d, false, none⟩ cycle) % 4096) := by
  simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
    plusTwoMem, plusTwoWordRegion, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt,
    Bank.capacity, Width.words, Nat.div_one]

/-- `LM1` word `19` is not at `bar1 = 0` distance zero from any of the region
addresses `a` once `bar1 = 0`. -/
theorem zeroBar_address (a : Nat) (lt : a < 4096) :
    (((0 : BitVec 12).toNat) + a) % 4096 = a := by
  simp [Nat.mod_eq_of_lt lt]

end ProofsLean.MNCore


namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 2. The concrete destinations of the four suffix lines

The four suffix lines have direct `LM1` word destinations with region addresses
`5,7,29,13`, `31,21,35,17`, `3,1,9,25`, and `37,23,15,27`.  At `bar1 = 0` the
cycle-`c` destination is exactly the `c`-th region address (the write is one
word wide, and `LM1` word `19` is not among the sixteen). -/

/-- The `LM1` word written by a direct destination operand in one cycle at
`bar1 = 0`, as a triple. -/
theorem destination_at_zero_bar (a b c d : Nat) (pe : Fin 4)
    (bar0 : BitVec 12) (tWord : BitVec 32) (cycle : Fin 4) :
    (ParsedOperand.toDirectMemoryDestination? (plusTwoMem .lm1 a b c d) pe cycle bar0 0 tWord).map
      (fun x => (x.bank, x.width, x.address.val)) =
      some (.lm1, .word, (0 + parsedRegionAddressAt ⟨1, a, b, c, d, false, none⟩ cycle) % 4096) := by
  rw [directDestination_formula]
  rfl

/-- At `bar1 = 0` the four cycle destinations of suffix line 2 are
`5, 7, 29, 13`. -/
theorem suffixLine2_addresses :
    (parsedRegionAddressAt ⟨1, 5, 7, 29, 13, false, none⟩ 0 = 5) ∧
    (parsedRegionAddressAt ⟨1, 5, 7, 29, 13, false, none⟩ 1 = 7) ∧
    (parsedRegionAddressAt ⟨1, 5, 7, 29, 13, false, none⟩ 2 = 29) ∧
    (parsedRegionAddressAt ⟨1, 5, 7, 29, 13, false, none⟩ 3 = 13) := by decide

/-- At `bar1 = 0` the four cycle destinations of suffix line 3 are
`31, 21, 35, 17`. -/
theorem suffixLine3_addresses :
    (parsedRegionAddressAt ⟨1, 31, 21, 35, 17, false, none⟩ 0 = 31) ∧
    (parsedRegionAddressAt ⟨1, 31, 21, 35, 17, false, none⟩ 1 = 21) ∧
    (parsedRegionAddressAt ⟨1, 31, 21, 35, 17, false, none⟩ 2 = 35) ∧
    (parsedRegionAddressAt ⟨1, 31, 21, 35, 17, false, none⟩ 3 = 17) := by decide

/-- At `bar1 = 0` the four cycle destinations of suffix line 4 are
`3, 1, 9, 25`. -/
theorem suffixLine4_addresses :
    (parsedRegionAddressAt ⟨1, 3, 1, 9, 25, false, none⟩ 0 = 3) ∧
    (parsedRegionAddressAt ⟨1, 3, 1, 9, 25, false, none⟩ 1 = 1) ∧
    (parsedRegionAddressAt ⟨1, 3, 1, 9, 25, false, none⟩ 2 = 9) ∧
    (parsedRegionAddressAt ⟨1, 3, 1, 9, 25, false, none⟩ 3 = 25) := by decide

/-- At `bar1 = 0` the four cycle destinations of suffix line 5 are
`37, 23, 15, 27`. -/
theorem suffixLine5_addresses :
    (parsedRegionAddressAt ⟨1, 37, 23, 15, 27, false, none⟩ 0 = 37) ∧
    (parsedRegionAddressAt ⟨1, 37, 23, 15, 27, false, none⟩ 1 = 23) ∧
    (parsedRegionAddressAt ⟨1, 37, 23, 15, 27, false, none⟩ 2 = 15) ∧
    (parsedRegionAddressAt ⟨1, 37, 23, 15, 27, false, none⟩ 3 = 27) := by decide

/-- The four region addresses of suffix line 2, none of them `19`. -/
theorem suffixLine2_avoids_witness :
    (5 ≠ 19 ∧ 7 ≠ 19 ∧ 29 ≠ 19 ∧ 13 ≠ 19) := by decide

/-- The four region addresses of suffix line 3. -/
theorem suffixLine3_avoids_witness :
    (31 ≠ 19 ∧ 21 ≠ 19 ∧ 35 ≠ 19 ∧ 17 ≠ 19) := by decide

/-- The four region addresses of suffix line 4. -/
theorem suffixLine4_avoids_witness :
    (3 ≠ 19 ∧ 1 ≠ 19 ∧ 9 ≠ 19 ∧ 25 ≠ 19) := by decide

/-- The four region addresses of suffix line 5. -/
theorem suffixLine5_avoids_witness :
    (37 ≠ 19 ∧ 23 ≠ 19 ∧ 15 ≠ 19 ∧ 27 ≠ 19) := by decide

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 3. The witness write that the unconditional frame misses

At `bar1 = 14` the cycle-0 destination of suffix line 2 (`idec 9 29 13 39 5 7 29 13`)
is `LM1` word `5 + 14 = 19`, and the per-PE execution really changes that word.
This is the concrete reason `PlusTwoSuffixPreservesWitness` cannot hold for an
arbitrary state: its quantifier ranges over `state.peContext`, and the plain-ALU
destination is `bar1`-relative. -/

/-- The initial state with the observed PE's `BAR1` moved to `bar1`. -/
def plusTwoBar1State (bar1 : Nat) : State :=
  { plusTwoInitialState plusTwoZeroWords with
    peContext := fun pe =>
      if pe = plusTwoPE then
        { (plusTwoInitialState plusTwoZeroWords).peContext pe with
          bar1 := BitVec.ofNat 12 bar1 }
      else (plusTwoInitialState plusTwoZeroWords).peContext pe }

/-- The witness word, as an `LM1` index. -/
def plusTwoWitnessWord : Fin Bank.lm1.capacity :=
  plusTwoLowAddress plusTwoWitnessOutput

/-- The second recorded suffix line's expression. -/
def plusTwoSuffixLine2Expr : ParsedExpr := plusTwoIdec 9 29 13 39 5 7 29 13

/-- **The unconditional frame fails at `bar1 = 14`.**  The second suffix line
succeeds at that state and changes `LM1` word `19` (the witness). -/
theorem plusTwoSuffixLine2_changes_witness_at_bar1 :
    ∃ next, executeIntegerProducerLineAtPE [plusTwoSuffixLine2Expr]
        (plusTwoBar1State 14) plusTwoPE = .ok next ∧
      (next.peRegisters plusTwoPE).lm1 plusTwoWitnessWord ≠
        ((plusTwoBar1State 14).peRegisters plusTwoPE).lm1 plusTwoWitnessWord := by
  have witness : (match executeIntegerProducerLineAtPE [plusTwoSuffixLine2Expr]
        (plusTwoBar1State 14) plusTwoPE with
      | .ok next => decide ((next.peRegisters plusTwoPE).lm1 plusTwoWitnessWord =
          ((plusTwoBar1State 14).peRegisters plusTwoPE).lm1 plusTwoWitnessWord)
      | _ => true) = false := by decide
  cases executed : executeIntegerProducerLineAtPE [plusTwoSuffixLine2Expr]
      (plusTwoBar1State 14) plusTwoPE with
  | failure => simp [executed] at witness
  | unknown => simp [executed] at witness
  | ok next =>
      simp only [executed] at witness
      exact ⟨next, rfl, of_decide_eq_false witness⟩

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 4. The per-line coverage obligation is false

`PlusTwoLineCoverage` claims every successful line changes at most four of the
twenty observed words.  A single legal `.pe` line suffices to change eight: a
`zero` row whose `LM1` destination region has width `4` (`double`) writes four
words per cycle, at the four region addresses.  The destination addresses are
`0, 4, 8, 12`, so the line writes `LM1` words `0..15` — eight of the observed
low words `1,3,5,7,9,11,13,15` change when the initial `LM1` is non-zero.

The write count is a kernel computation on the per-PE step; the line is a plain
`zero` row with no sources, so its issue record has a single `LM1` write
(`writesUnique` is about banks, not widths, so it is satisfied). -/

/-- A `zero` row with a width-four `LM1` destination window. -/
def plusTwoWideZeroExpr : ParsedExpr where
  op := .zero
  sources := []
  destinations := [.mem ⟨.lm1, ⟨4, 0, 4, 8, 12, false, none⟩⟩ false false false none]
  flush := none
  text := "zero $lm1[0,4,8,12] (double)"

/-- The all-ones `LM1` state at the all-zero input. -/
def plusTwoAllOnesLm1State : State :=
  { plusTwoInitialState plusTwoZeroWords with
    peRegisters := fun pe =>
      { (plusTwoInitialState plusTwoZeroWords).peRegisters pe with
        lm1 := fun _ => 0xFFFFFFFF } }

/-- The four cycle destinations of the wide `zero` row, at any register file,
directive and `bar1`. -/
theorem plusTwoWideZeroExpr_destinations
    (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (bar0 : BitVec 12) (tWord : BitVec 32) :
    ((ParsedExpr.toDirectMaskedIntegerAccessesInLine? plusTwoWideZeroExpr registers directive
        false 0 0 0 0 0 0 bar0 0 tWord).map (fun a => a.destination)).map
        (fun x => (x.bank, x.width, x.address.val)) = some (.lm1, .double, 0) ∧
    ((ParsedExpr.toDirectMaskedIntegerAccessesInLine? plusTwoWideZeroExpr registers directive
        false 0 0 0 0 0 1 bar0 0 tWord).map (fun a => a.destination)).map
        (fun x => (x.bank, x.width, x.address.val)) = some (.lm1, .double, 4) ∧
    ((ParsedExpr.toDirectMaskedIntegerAccessesInLine? plusTwoWideZeroExpr registers directive
        false 0 0 0 0 0 2 bar0 0 tWord).map (fun a => a.destination)).map
        (fun x => (x.bank, x.width, x.address.val)) = some (.lm1, .double, 8) ∧
    ((ParsedExpr.toDirectMaskedIntegerAccessesInLine? plusTwoWideZeroExpr registers directive
        false 0 0 0 0 0 3 bar0 0 tWord).map (fun a => a.destination)).map
        (fun x => (x.bank, x.width, x.address.val)) = some (.lm1, .double, 12) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [plusTwoWideZeroExpr, ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
      ParsedOp.executionRequest, ParsedOperand.toDirectMemoryDestination?,
      ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.resolveMemoryWriteSelection?,
      resolveFlushSelection?, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt,
      Bank.capacity, Width.words, Option.map_some, reduceCtorEq, reduceIte]

/-- The number of observed output words changed by the wide `zero` row. -/
def plusTwoWideZeroChangedWords : Nat :=
  match executeIntegerProducerLineAtPE [plusTwoWideZeroExpr] plusTwoAllOnesLm1State plusTwoPE with
  | .ok next =>
      ((List.finRange 20).filter fun k =>
        decide ((next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) ≠
          ((plusTwoAllOnesLm1State).peRegisters plusTwoPE).lm1 (plusTwoLowAddress k))).length
  | _ => 0

/-- **One line changes eight observed words.**  This contradicts the conclusion
of `PlusTwoLineCoverage`, whose bound is four. -/
theorem plusTwoWideZeroLine_changes_eight :
    plusTwoWideZeroChangedWords = 8 := by
  decide

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 5. The headline: the per-PE frame is false without the `BAR1` hypothesis -/

/-- **The per-PE analogue of `PlusTwoSuffixPreservesWitness` is false.**  Even a
single suffix line does not preserve `LM1` word `19` at every state. -/
theorem plusTwoSuffixLine2_perPE_frame_false :
    ¬ (∀ (state next : State),
        executeIntegerProducerLineAtPE [plusTwoSuffixLine2Expr] state plusTwoPE = .ok next →
          (next.peRegisters plusTwoPE).lm1 plusTwoWitnessWord =
            (state.peRegisters plusTwoPE).lm1 plusTwoWitnessWord) := by
  intro frame
  obtain ⟨next, executed, changed⟩ := plusTwoSuffixLine2_changes_witness_at_bar1
  exact changed (frame _ _ executed)

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 6. The destinations computed once, at the zero state

This is the "compute once where it is decidable" half of the transport plan: the
four prepared writes of a suffix line's four-cycle preparation at the zero
register file and the zero control have exactly the four region destinations.
(The other half — transporting this list to an arbitrary state — needs the same
control, hence the same `bar1`; see the module header.) -/

/-- Zero forwarding slots. -/
def plusTwoZeroSlots : ProofsLean.MNCore.Forwarding.Slots := fun _ _ => .known ⟨0, 0⟩

/-- The linear-index control of PE `0` with zero BAR/T and the zero mask directive. -/
def plusTwoZeroControl : ParsedMaskExecutionControl where
  directive := { widthWords := 0, targets := {}, entry := 0 }
  context := ParsedIntegerContext.ofLinearIndex plusTwoPE
  elapsedWords := 0

/-- The destination triples of the four prepared writes of a one-expression
four-cycle preparation at the zero state. -/
def plusTwoSuffixDestinations (expression : ParsedExpr) :
    Option (List (Option (PEMemory.Bank × PEMemory.Width × Nat))) :=
  match prepareParsedIntegerALUExprCycles zeroInitialPERegisterFiles plusTwoZeroSlots
      plusTwoZeroSlots expression plusTwoZeroControl false false false with
  | .ok (writes, _) =>
      some (writes.map (fun w => (w.destination).map (fun d => (d.bank, d.width, d.address.val))))
  | _ => none

/-- Suffix line 2 writes `LM1` words `5, 7, 29, 13`. -/
theorem plusTwoSuffixLine2_destinations :
    plusTwoSuffixDestinations (plusTwoIdec 9 29 13 39 5 7 29 13) =
      some [some (.lm1, .word, 5), some (.lm1, .word, 7), some (.lm1, .word, 29),
        some (.lm1, .word, 13)] := by decide

/-- Suffix line 3 writes `LM1` words `31, 21, 35, 17`. -/
theorem plusTwoSuffixLine3_destinations :
    plusTwoSuffixDestinations (plusTwoIdec 21 23 17 15 31 21 35 17) =
      some [some (.lm1, .word, 31), some (.lm1, .word, 21), some (.lm1, .word, 35),
        some (.lm1, .word, 17)] := by decide

/-- Suffix line 4 writes `LM1` words `3, 1, 9, 25`. -/
theorem plusTwoSuffixLine4_destinations :
    plusTwoSuffixDestinations (plusTwoIxor 11 7 39 27 1 1 0 2 3 1 9 25) =
      some [some (.lm1, .word, 3), some (.lm1, .word, 1), some (.lm1, .word, 9),
        some (.lm1, .word, 25)] := by decide

/-- Suffix line 5 writes `LM1` words `37, 23, 15, 27`. -/
theorem plusTwoSuffixLine5_destinations :
    plusTwoSuffixDestinations (plusTwoIxor 27 5 37 19 0 3 0 1 37 23 15 27) =
      some [some (.lm1, .word, 37), some (.lm1, .word, 23), some (.lm1, .word, 15),
        some (.lm1, .word, 27)] := by decide

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 7. The correctness refutation with the corrected hypothesis

`PlusTwoLowerBound.plusTwoRecorded_not_correct_of_suffixFrame` refutes the
recorded five-line answer from `PlusTwoSuffixPreservesWitness`, which is false
(§3).  The refutation below replaces it by the corrected frame, which only
assumes `BAR1 = 0` at the observed PE — the state component the destination
actually reads — plus the fact that the first line keeps `BAR1` (it writes no
BAR destination, so `parsedIntegerALUBarUpdates` is empty and the context's
`bar1` field is unchanged).

Both remaining obligations are *true* statements about the executor (unlike
`PlusTwoSuffixPreservesWitness`), and §1-§6 of this module prove the whole
destination half: at `bar1 = 0` every suffix destination is one of
`5,7,29,13 / 31,21,35,17 / 3,1,9,25 / 37,23,15,27`, none of them word `19`. -/

/-- **The corrected suffix-frame obligation**: at states whose observed PE has
`BAR1 = 0`, the four recorded suffix lines do not change `LM1` word `19`. -/
def PlusTwoSuffixPreservesWitnessOfBar1Zero : Prop :=
  ∀ (state next : State),
    (state.peContext plusTwoPE).bar1 = 0 →
      ProofsLean.execute plusTwoSealedMachine plusTwoSuffix state = some next →
        (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
          (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput)

/-- **The first line keeps the observed PE's `BAR1`.**  The line's prepared
writes carry `LM1`/`GRF0` destinations only, so `parsedIntegerALUBarUpdates` is
empty and the per-PE context update leaves `bar1` at its old value. -/
def PlusTwoLine1PreservesBar1Zero : Prop :=
  ∀ (state next : State),
    plusTwoSealedMachine.step plusTwoLine1 state = some next →
      (next.peContext plusTwoPE).bar1 = (state.peContext plusTwoPE).bar1

/-- The initial state has `BAR1 = 0` at the observed PE. -/
theorem plusTwoInitialState_bar1_zero (input : PlusTwoWords) :
    ((plusTwoInitialState input).peContext plusTwoPE).bar1 = 0 := by
  rfl

/-- **The recorded answer is refuted by the all-zero input**, with the corrected
suffix frame and the first line's `BAR1` frame as the only remaining
obligations.  The first line writes `0xFFFFFFFF` into output long 9; the four
remaining lines preserve it at `BAR1 = 0`; the specification demands `2`. -/
theorem plusTwoRecorded_not_correct_of_bar1Frame
    (frame : PlusTwoSuffixPreservesWitnessOfBar1Zero)
    (line1 : PlusTwoLine1PreservesBar1Zero) :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer := by
  intro correct
  obtain ⟨result, executed, post⟩ :=
    correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  rw [plusTwoRecordedAnswer_eq] at executed
  rw [ProofsLean.execute.eq_2] at executed
  rw [plusTwoSpec_initial] at executed
  cases h1 : plusTwoSealedMachine.step plusTwoLine1
      (plusTwoInitialState plusTwoZeroWords) with
  | none =>
      rw [h1] at executed
      simp at executed
  | some state1 =>
      rw [h1] at executed
      simp only [Option.bind_some] at executed
      have bar1State : (state1.peContext plusTwoPE).bar1 = 0 := by
        rw [line1 _ _ h1]
        exact plusTwoInitialState_bar1_zero plusTwoZeroWords
      have word1 := plusTwoLine1_step_value state1 h1
      have wordSuffix := frame state1 result bar1State executed
      have postWord := (post plusTwoWitnessOutput).2
      rw [wordSuffix, word1] at postWord
      simp [plusTwoZeroWords] at postWord

end ProofsLean.MNCore
