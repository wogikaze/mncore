import ProofsLean.StageCommitSpecific
import ProofsLean.WelcomeBoundTwo

/-! # One-stage value provenance for a PE issue line

This module isolates the **data half** of a one-line lower-bound argument, in
the same problem-free style as `ProofsLean/PlainALUDestination.lean` isolates the
destination half.

The central object is the closure `OneStageValue S`: the 32-bit words generated
from a set `S` of old words by

* the old words themselves and `0`,
* one application of `evaluateParsedIntegerAlu` to two buses whose 32-bit words
  are already in the closure (this covers `.alu`, `.zero` and `.immediate`),
* a masked merge of an old and a new word, and
* a half-precision rounding of two words packed into one 32-bit word.

The executor lemmas proved here are state-general and mention no machine,
problem or input:

* `prepareParsedMaskedWriteWithForwarding_data_eq` — the prepared write's data
  is exactly the flushed `evaluateParsedIntegerAlu` result of its two
  `readWithForwarding` sources;
* `prepareParsedMaskedWriteWithForwarding_data_in_closure` — hence its words lie
  in `OneStageValue S` whenever the source words do;
* `welcomeCommitStep_lm1_closure` and `commitParsedMaskedWrites_lm1_closure` —
  a commit whose `.lm1` writes have data in the closure keeps every `.lm1` word
  in the closure;
* `executeIntegerProducerLineAtPECore_lm1_closure_of_commit` — the line-level
  form, from a pinned commit list.

The remaining executor link is stated explicitly in the final section: the
read-source closure (`readWithForwarding` words lie in the closure when the
register-file and forwarding words do) and the per-expression prepared-write
list assembly.  The direct plain-ALU branch is the first case of
`prepareParsedIntegerALUExprCycle`; the mask/OMR/BAR/constant/no-write branches
need the same induction.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 1. The one-stage value closure -/

/-- The one-stage value closure of a set `S` of 32-bit words.  Every constructor
is an operation the plain integer-ALU executor can perform in one issue line. -/
inductive OneStageValue (S : Set (BitVec 32)) : BitVec 32 → Prop where
  /-- A word that was already present. -/
  | old {w : BitVec 32} : w ∈ S → OneStageValue S w
  /-- The zero word. -/
  | zero : OneStageValue S 0
  /-- A word of a flushed `evaluateParsedIntegerAlu` result. -/
  | alu {op : ParsedOp} {x y : IntegerALU.Bus} {output : IntegerALU.BusResult}
      {selection : Option PEWordSelection} {index : Fin 4} {reduced : Bool} :
      evaluateParsedIntegerAlu op x y reduced = .ok output →
      (∀ i : Fin 4, OneStageValue S (unpackALUBus x i)) →
      (∀ i : Fin 4, OneStageValue S (unpackALUBus y i)) →
      OneStageValue S
        (unpackALUBus (parsedOutputAfterFlush selection output.value) index)
  /-- A masked store merge of an old and a new word. -/
  | merge {old new enable : BitVec 32} :
      OneStageValue S old → OneStageValue S new →
      OneStageValue S (mergeSelectedWord old new enable)
  /-- Half-precision rounding of two words packed into one 32-bit word. -/
  | rounded {low high : BitVec 32} :
      OneStageValue S low → OneStageValue S high →
      OneStageValue S (roundSingleWordToHalf low ++ roundSingleWordToHalf high)

/-! ## 2. The prepared write's data is an ALU image of its two reads -/

/-- **The prepared-write data equation.**  Every successful
`prepareParsedMaskedWriteWithForwarding` returns a write whose `data` bus is
exactly `unpackALUBus` of the flushed `evaluateParsedIntegerAlu` result.  The
sources are the two `readWithForwarding` buses. -/
theorem prepareParsedMaskedWriteWithForwarding_data_eq
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x ∧
      ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data =
        unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value) := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x =>
      cases readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp [readX, readY] at prepared
      | unknown => simp [readX, readY] at prepared
      | ok y =>
          cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [readX, readY, evaluated] at prepared
          | unknown => simp [readX, readY, evaluated] at prepared
          | ok output =>
              simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, evaluated, rfl⟩

/-- **The prepared write's data lies in the closure.**  If the two read buses
have their 32-bit words in `OneStageValue S`, then every word of the prepared
write's data bus does too. -/
theorem prepareParsedMaskedWriteWithForwarding_data_in_closure
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (S : Set (BitVec 32))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write)
    (x y : IntegerALU.Bus)
    (readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y)
    (hX : ∀ i : Fin 4, OneStageValue S (unpackALUBus x i))
    (hY : ∀ i : Fin 4, OneStageValue S (unpackALUBus y i)) :
    ∀ i : Fin 4, OneStageValue S (write.data i) := by
  obtain ⟨x', y', output, readX', readY', evaluated, dataEq⟩ :=
    prepareParsedMaskedWriteWithForwarding_data_eq files slots cycle accesses reduced write
      prepared
  have xEq : x' = x := by rw [readX] at readX'; exact (StepResult.ok.inj readX').symm
  have yEq : y' = y := by rw [readY] at readY'; exact (StepResult.ok.inj readY').symm
  subst xEq
  subst yEq
  intro i
  rw [dataEq]
  exact OneStageValue.alu evaluated hX hY

/-! ## 3. Masked commits preserve the closure -/

/-- **One commit step preserves the closure at an LM1 word.**  If the old word is
in the closure and the write's `.lm1` destination either avoids the word or
stores a bus word in the closure, the committed word is in the closure. -/
theorem welcomeCommitStep_lm1_closure
    (files : IntegerRegisterFiles) (write : PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (S : Set (BitVec 32))
    (oldClosed : OneStageValue S (files.lm1 target))
    (keeps : ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
        (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (∀ i : Fin 4, OneStageValue S (data i))) :
    OneStageValue S ((welcomeCommitStep files write).lm1 target) := by
  cases write with
  | mk destination maskUpdate data selection =>
      cases maskUpdate with
      | some update =>
          simp only [welcomeCommitStep]
          exact oldClosed
      | none =>
          cases destination with
          | none =>
              simp only [welcomeCommitStep]
              exact oldClosed
          | some access =>
              cases access with
              | mk bank width address =>
                  cases bank with
                  | lm1 =>
                      simp only [welcomeCommitStep]
                      by_cases within : distance .lm1 address target < count .lm1 width
                      · rw [writeDirectAccessMasked_lm1_apply]
                        rw [writeWordsMasked_at .lm1 width files.lm1 address target data
                          selection.flags selection.longLong within]
                        have dataClosed :=
                          ((keeps width address data selection rfl rfl rfl).resolve_left
                            (Nat.not_le.mpr within))
                        exact OneStageValue.merge oldClosed
                          (dataClosed ⟨distance .lm1 address target,
                            Nat.lt_of_lt_of_le within (count_le_four .lm1 width)⟩)
                      · rw [writeDirectAccessMasked_lm1_apply]
                        rw [writeWordsMasked_preserves_outside .lm1 width files.lm1 address
                          target data selection.flags selection.longLong (Nat.le_of_not_lt within)]
                        exact oldClosed
                  | lm0 =>
                      simp only [welcomeCommitStep]
                      rw [show (writeDirectAccessMasked files
                          ⟨.lm0, width, address⟩ data selection).lm1 = files.lm1 from
                        writeDirectAccessMasked_lm1_eq files .lm0 width address data selection
                          (by decide)]
                      exact oldClosed
                  | grf0 =>
                      simp only [welcomeCommitStep]
                      rw [show (writeDirectAccessMasked files
                          ⟨.grf0, width, address⟩ data selection).lm1 = files.lm1 from
                        writeDirectAccessMasked_lm1_eq files .grf0 width address data selection
                          (by decide)]
                      exact oldClosed
                  | grf1 =>
                      simp only [welcomeCommitStep]
                      rw [show (writeDirectAccessMasked files
                          ⟨.grf1, width, address⟩ data selection).lm1 = files.lm1 from
                        writeDirectAccessMasked_lm1_eq files .grf1 width address data selection
                          (by decide)]
                      exact oldClosed
                  | t =>
                      simp only [welcomeCommitStep]
                      rw [show (writeDirectAccessMasked files
                          ⟨.t, width, address⟩ data selection).lm1 = files.lm1 from
                        writeDirectAccessMasked_lm1_eq files .t width address data selection
                          (by decide)]
                      exact oldClosed

/-- **A commit keeps every LM1 word in the closure.** -/
theorem commitParsedMaskedWrites_lm1_closure
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (S : Set (BitVec 32))
    (oldClosed : OneStageValue S (files.lm1 target))
    (keeps : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (∀ i : Fin 4, OneStageValue S (data i))) :
    OneStageValue S ((commitParsedMaskedWrites files writes).lm1 target) := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using oldClosed
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · exact welcomeCommitStep_lm1_closure files write target S oldClosed
          (fun width address data selection destination dataEq selectionEq =>
            keeps write (by simp) width address data selection destination dataEq
              selectionEq)
      · intro item member
        exact keeps item (List.mem_cons_of_mem _ member)

/-! ## 4. The line-level value link -/

/-- **Line-level closure from a pinned commit list.**  If the next register file
is the commit of `prepared ++ floatWrites`, the old LM1 word is in the closure,
and every committed write's data words are in the closure, then the next LM1
word is in the closure.  The lists are explicit so that a caller can obtain them
from `executeIntegerProducerLineAtPECore_peRegisters_commit_list`. -/
theorem executeIntegerProducerLineAtPECore_lm1_closure_of_commit
    (state next : State) (pe : PEId) (prepared floatWrites : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (S : Set (BitVec 32))
    (commitEq : next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) (prepared ++ floatWrites))
    (oldClosed : OneStageValue S ((state.peRegisters pe).lm1 target))
    (intKeeps : ∀ write ∈ prepared, ∀ i : Fin 4, OneStageValue S (write.data i))
    (floatKeeps : ∀ write ∈ floatWrites, ∀ i : Fin 4, OneStageValue S (write.data i)) :
    OneStageValue S ((next.peRegisters pe).lm1 target) := by
  rw [commitEq]
  apply commitParsedMaskedWrites_lm1_closure
  · exact oldClosed
  · intro write mem width address data selection destination dataEq selectionEq
    rcases List.mem_append.mp mem with inPrepared | inFloat
    · exact Or.inr (by rw [← dataEq]; exact intKeeps write inPrepared)
    · exact Or.inr (by rw [← dataEq]; exact floatKeeps write inFloat)

/-- **The line-level theorem, stated directly on the executor.**  Given the
pinned commit list from `executeIntegerProducerLineAtPECore_peRegisters_commit_list`,
if every write of the integer preparation and of the float stage has its data
words in the closure, then every LM1 word of the next state is in the closure.
No branch of the executor is unfolded here; the hypotheses are exactly the
per-write data facts that the prepared-write lemma supplies. -/
theorem executeIntegerProducerLineAtPECore_lm1_closure
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next)
    (S : Set (BitVec 32)) (target : Fin Bank.lm1.capacity)
    (oldClosed : OneStageValue S ((state.peRegisters pe).lm1 target))
    (dataClosed : ∀ (prepared : List PreparedParsedMaskedWrite ×
        ProofsLean.MNCore.Forwarding.Slots × List (Bool × BitVec 12))
        (floatWrites : List PreparedParsedMaskedWrite),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok prepared →
      next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe)
        (prepared.1 ++ floatWrites) →
      (∀ write ∈ prepared.1, ∀ i : Fin 4, OneStageValue S (write.data i)) ∧
      (∀ write ∈ floatWrites, ∀ i : Fin 4, OneStageValue S (write.data i))) :
    OneStageValue S ((next.peRegisters pe).lm1 target) := by
  obtain ⟨prepared, floatWrites, preparedEq, commitEq⟩ :=
    executeIntegerProducerLineAtPECore_peRegisters_commit_list expressions state next pe
      executed
  obtain ⟨intKeeps, floatKeeps⟩ := dataClosed prepared floatWrites preparedEq commitEq
  exact executeIntegerProducerLineAtPECore_lm1_closure_of_commit state next pe
    prepared.1 floatWrites target S commitEq oldClosed intKeeps floatKeeps

/-- **The line-level theorem for a float-free line.**  When the line has no
supported float-MAU producer, `executeIntegerProducerLineAtPECore` commits
exactly the integer stage's own preparation list
(`executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward`).  The
only data obligation is therefore on that integer list. -/
theorem executeIntegerProducerLineAtPECore_lm1_closure_floatFree
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (S : Set (BitVec 32)) (target : Fin Bank.lm1.capacity)
    (oldClosed : OneStageValue S ((state.peRegisters pe).lm1 target))
    (intDataClosed : ∀ (prepared : List PreparedParsedMaskedWrite ×
        ProofsLean.MNCore.Forwarding.Slots × List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok prepared →
      ∀ write ∈ prepared.1, ∀ i : Fin 4, OneStageValue S (write.data i)) :
    OneStageValue S ((next.peRegisters pe).lm1 target) := by
  obtain ⟨prepared, preparedEq, commitEq⟩ :=
    executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward expressions state
      next pe floatEmpty executed
  have commitEq' : next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) (prepared.1 ++ []) := by
    simpa using commitEq
  exact executeIntegerProducerLineAtPECore_lm1_closure_of_commit state next pe
    prepared.1 [] target S commitEq' oldClosed (intDataClosed prepared preparedEq)
    (by intro write mem; simp at mem)

/-- **The named line-level data obligation.**  For the actual integer
preparation list of `executeIntegerProducerLineAtPECore`, every write's data
words are in the closure.  This is the single statement the per-expression
branch induction has to produce; the direct-memory branch is already its first
case. -/
def LinePreparedDataInClosure (state : State) (pe : PEId)
    (expressions : List ParsedExpr) (S : Set (BitVec 32)) : Prop :=
  ∀ (prepared : List PreparedParsedMaskedWrite ×
      ProofsLean.MNCore.Forwarding.Slots × List (Bool × BitVec 12)),
    prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
        (stateForwardingSlots state pe)
        (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
          (ParsedIntegerContext.ofLinearIndex pe).l2b
          (ParsedIntegerContext.ofLinearIndex pe).l1b)
        (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
        { directive := state.maskDirective
          context :=
            { (ParsedIntegerContext.ofLinearIndex pe) with
              bar0 := (state.peContext pe).bar0
              bar1 := (state.peContext pe).bar1
              tWord := (state.peContext pe).tWord }
          elapsedWords := state.hazardClock } false = .ok prepared →
    ∀ write ∈ prepared.1, ∀ i : Fin 4, OneStageValue S (write.data i)

/-- **The line-level closure theorem with the named obligation.**  For a
float-free issue line, `LinePreparedDataInClosure` is the only remaining data
hypothesis. -/
theorem executeIntegerProducerLineAtPECore_lm1_closure_floatFree_of_line
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (S : Set (BitVec 32)) (target : Fin Bank.lm1.capacity)
    (oldClosed : OneStageValue S ((state.peRegisters pe).lm1 target))
    (lineData : LinePreparedDataInClosure state pe expressions S) :
    OneStageValue S ((next.peRegisters pe).lm1 target) :=
  executeIntegerProducerLineAtPECore_lm1_closure_floatFree expressions state next pe
    executed floatEmpty S target oldClosed lineData

/-! ## 5. The exact remaining executor link -/

/-- **Read-source closure.**  If every 32-bit word of the register files and of
every known forwarding bus at the PE lies in `S`, then both reads used by a
prepared write have their words in `S`.  The rounded (`.e`/rounding) operands
need the `rounded` constructor of `OneStageValue`; the memory and forwarding
cases are direct, and the fixed case is a constant supplied by the caller. -/
def ReadWordsInClosure (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (S : Set (BitVec 32)) : Prop :=
  (∀ (bank : PEMemory.Bank) (width : PEMemory.Width)
      (address : Fin bank.capacity) (i : Fin 4), OneStageValue S (readDirectAccess files ⟨bank, width, address⟩ i)) ∧
  (∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (bus : IntegerALU.Bus),
      slots unit cycle = .known bus →
        ∀ i : Fin 4, OneStageValue S (unpackALUBus bus i)) ∧
  (∀ (value : IntegerALU.Bus) (i : Fin 4), OneStageValue S (unpackALUBus value i))

/-- **The remaining line-level obligation.**  A successful prepared write of the
plain integer-ALU cycle has all its data words in `OneStageValue S` whenever the
file/forwarding words are in `S`.  This is the exact induction over the eight
`prepareParsedIntegerALUExprCycle` branches that remains to be written out; the
direct-memory branch is discharged by
`prepareParsedMaskedWriteWithForwarding_data_in_closure`. -/
def PlainALUPreparedDataInClosure : Prop :=
  ∀ (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (S : Set (BitVec 32)),
    ReadWordsInClosure files slots cycle S →
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced = .ok write →
    ∀ i : Fin 4, OneStageValue S (write.data i)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
