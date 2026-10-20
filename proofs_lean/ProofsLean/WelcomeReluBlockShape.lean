import ProofsLean.WelcomeSpecialShape

/-! # The float-relu and block-float folds; three of the named remainders discharged

`WelcomeSpecialShape.lean` (round 37) reduced the special-ALU row analysis to six
named `Prop`s.  Of the five this module targets, it proves three outright.  Of
the other two, `WelcomePEFloatReluZeroReadCopy` is *refuted* outright and
`WelcomePEBlockFloatMabShape` cannot be closed as stated: its proof needs the
third-word copy of the block-float output bus, an assumption the `Prop` does not
have.  Both gaps are stated as kernel-checked theorems, and the block-float fold
is proved in full with that missing hypothesis supplied.

## What is proved here

1. `welcomePEFloatReluFlushCopy : WelcomePEFloatReluFlushCopy` (§1).  The
   `parsedOutputAfterFlush` wrapper is the flush selection plus an AND, and the
   AND preserves a copy; the general wrapper lemma
   `parsedOutputAfterFlush_unpack_two_isWelcomeCopy` is proved once and the
   float-relu instance follows from the raw-bus copy already in
   `WelcomeSpecialShape`.
2. `welcomePEFloatReluCyclesShape : WelcomePEFloatReluCyclesShape` (§2).  The
   destination fold and the four-cycle fold of `executeParsedFloatReluAtPE` are
   the verbatim analogue of `mslMsr_writeDestinations_lm1Facts` /
   `mslMsr_runCycles_lm1Facts`: the same lowered-write split, the same
   `some`-branch definitional ascription, and the same counting bound.
3. `welcomePEBlockFloatHalfZeroInputCopy : WelcomePEBlockFloatHalfZeroInputCopy`
   (§3).  At the zero input every lane of `parsedBlockFloat .half` is `0` for
   every `keep` and `extended` (`parsedBlockFloatMab_h_zero`), so the low half —
   and hence the third bus word — is zero.
4. `welcomePEBlockFloatMabShape_of_busCopy` (§4): the block-float per-coordinate
   `apply`/`writePEs`/`runCycles` folds, with the third-word copy of the row's
   output bus as an explicit hypothesis.  The hypothesis is discharged
   unconditionally for `.d`/`.f`/`.g`
   (`welcomePEBlockFloatMabShape_of_precision_low_zero`), whose low half is
   structurally zero.

## The two named `Prop`s that are not theorems, and why

`WelcomePEFloatReluZeroReadCopy` is false as stated, and
`WelcomePEBlockFloatMabShape` is under-hypothesised; both quantify over data the
all-zero state does not control.

* `not_welcomePEFloatReluZeroReadCopy` (§5): a float-relu row may have a
  `.fixed` source, and the fixed value is read off the *lowering context*.
  With precision `.f`, source `.fixed .l2bid` and `context.group = 1`, the
  lowering yields `.fixed (replicateIntegerLane .word 2)`, whose read is
  `⟨0x0000000200000002, 0x0000000200000002⟩`; its copied word is `2`, and
  `IsWelcomeCopy 2` is false (`2 &&& 0x80008000 = 0 ≠ 2`).  At PE 0 all fixed
  values are `0` or `msb1` (that is the `WelcomePlainStep` lemma), but the named
  `Prop` quantifies an arbitrary PE and an arbitrary context, so the PE-0
  argument does not transport.  The exact missing fact is the PE restriction
  (and the state's own context): the statement is true at `welcomePE` with the
  zero-state context, which is the case the observed PE needs.
* `WelcomePEBlockFloatMabShape` (§4) admits `.h` block float, whose low half is
  built from the input lanes 4-7.  The third word is a copy for `.d`/`.f`/`.g`
  only; at the arbitrary `readState` the `Prop` quantifies,
  `parsedBlockFloatMab .h 9 false (fun _ => ⟨0, 0x3f023f023f023f02⟩) 0` has low
  `0x3f813f813f813f81`, whose third word `0x3f813f81` is not a copy
  (`parsedBlockFloatMab_h_third_word_not_copy`).  The exact missing fact is the
  third-word copy of the block-float output bus, which
  `welcomePEBlockFloatMabShape_of_busCopy` takes as a hypothesis and
  `welcomePEBlockFloatMabShape_of_precision_low_zero` discharges for the three
  precisions whose low half is zero.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing here claims
`LowerBound 2`, `Optimal`, or any line-level shape.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The flush case of the float-relu third word
`WelcomePEFloatReluFlushCopy` -/

/-- The `parsedOutputAfterFlush` wrapper preserves a copied third bus word: the
wrapper only selects `.long`/`.double` and ANDs the bus, and both flush arms
preserve a copy (`flushBus_long_word_two_copy`, `flushBus_double_word_two_copy`).
This is the wrapper's case analysis in `unpackALUBus` form. -/
theorem parsedOutputAfterFlush_unpack_two_isWelcomeCopy
    (selection : Option PEWordSelection) (data : IntegerALU.Bus) (bound : 2 < 4)
    (copy : IsWelcomeCopy ((unpackALUBus data) ⟨2, bound⟩)) :
    IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush selection data)) ⟨2, bound⟩) := by
  rw [unpackALUBus_of_val_eq_two (parsedOutputAfterFlush selection data) ⟨2, bound⟩ rfl]
  rw [unpackALUBus_of_val_eq_two data ⟨2, bound⟩ rfl] at copy
  exact parsedOutputAfterFlush_word_two_isWelcomeCopy selection data copy

/-- **`WelcomePEFloatReluFlushCopy`.** -/
theorem welcomePEFloatReluFlushCopy : WelcomePEFloatReluFlushCopy := by
  intro precision name unsigned left right selection bound copy
  exact parsedOutputAfterFlush_unpack_two_isWelcomeCopy selection _ bound
    (parsedFloatRelu_raw_output_word_two_copy precision name unsigned left right bound copy)

/-! ## 2. The float-relu folds
`WelcomePEFloatReluCyclesShape` -/

theorem executeParsedFloatReluAtPE_writeDestinations_lm1Facts
    (currentState : State) (hasSingleLineMask : Bool) (coordinates : ParsedIntegerContext)
    (cycle : Fin 4) (flags : BitVec 4) (output : IntegerALU.Bus) (w : PEMemory.Width)
    (destinations : List ParsedOperand)
    (staticWidth : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedFloatReluAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        coordinates cycle flags output destinations files bar0 bar1 =
          some (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              executeParsedFloatReluAtPE.runCycles.writeDestinations currentState
                hasSingleLineMask coordinates cycle flags output rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = some (nextFiles, nextBar0, nextBar1) := executed
          obtain ⟨prepared, commitEq, shape, provenance⟩ :=
            writeParsedMslMsrDestination?_facts files destination
              { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 }
              output flags cycle currentState.maskDirective hasSingleLineMask write w
              (fun bank width pair bankEq => staticWidth destination (by simp) bank width pair bankEq)
              dataCopy lowered
          obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
            ih (fun item member => staticWidth item (List.mem_cons_of_mem _ member))
              write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              nextFiles nextBar0 nextBar1 tailExecuted
          refine ⟨prepared :: restWrites, ?_, ?_, ?_⟩
          · rw [restCommit, commitEq]
            simpa using (commitParsedMaskedWrites_append files [prepared] restWrites).symm
          · have appended := lm1WriteFacts_append w [prepared] restWrites shape restShape
            simpa using appended
          · by_cases isLm1 : PreparedParsedMaskedWrite.isLm1Write prepared = true
            · have destinationLm1 : ParsedOperand.isLm1MemoryDestination destination = true := by
                rcases prepared with ⟨headDestination, headUpdate, headData, headSelection⟩
                cases headDestination with
                | none => simp [PreparedParsedMaskedWrite.isLm1Write] at isLm1
                | some access =>
                    simp only [PreparedParsedMaskedWrite.isLm1Write, beq_iff_eq] at isLm1
                    cases access with
                    | mk bank width address =>
                        cases isLm1
                        exact provenance width address rfl
              have leftEq : ((prepared :: restWrites).filter
                  PreparedParsedMaskedWrite.isLm1Write).length =
                  (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length + 1 := by
                simp [isLm1]
              have rightEq : (List.filter ParsedOperand.isLm1MemoryDestination
                    (destination :: rest)).length =
                  (List.filter ParsedOperand.isLm1MemoryDestination rest).length + 1 := by
                simp [destinationLm1]
              rw [leftEq, rightEq]
              omega
            · have isLm1False : PreparedParsedMaskedWrite.isLm1Write prepared = false := by
                simpa using isLm1
              have leftEq : ((prepared :: restWrites).filter
                  PreparedParsedMaskedWrite.isLm1Write).length =
                  (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length := by
                simp [isLm1False]
              rw [leftEq]
              refine le_trans restCount ?_
              cases hd : ParsedOperand.isLm1MemoryDestination destination <;>
                simp [hd]

theorem executeParsedFloatReluAtPE_runCycles_lm1Facts
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext)
    (w : PEMemory.Width) :
    ∀ (cycles : List (Fin 4)),
      (∀ cycle ∈ cycles, ∀ accesses : ParsedFloatReluAccesses,
        lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
        ∀ destination ∈ accesses.destinations,
          ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
            ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
              bank = PEMemory.Bank.lm1 → width = w) →
      (∀ cycle ∈ cycles, ∀ accesses : ParsedFloatReluAccesses,
        lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
        (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1) →
      (∀ cycle ∈ cycles, ∀ accesses : ParsedFloatReluAccesses,
        lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
        ∀ sourceA : IntegerALU.Bus,
          ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
            (stateForwardingSlots readState pe) cycle accesses.sourceA = .ok sourceA →
          IsWelcomeCopy (sourceA.low.extractLsb' 32 32)) →
      cycles.length ≤ 4 →
      ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
        (outputs : Fin 4 → IntegerALU.Bus) (registers : IntegerRegisterFiles)
        (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
        executeParsedFloatReluAtPE.runCycles readState currentState expression pe
          hasSingleLineMask coordinates sourceContext cycles files bar0 bar1 outputs =
            .ok (registers, nextBar0, nextBar1, nextOutputs) →
        ∃ writes : List PreparedParsedMaskedWrite,
          registers = commitParsedMaskedWrites files writes ∧
          Lm1WriteFacts w writes ∧
          (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  intro cycles
  induction cycles with
  | nil =>
      intro staticWidth countBound dataCopy cycleBound files bar0 bar1 outputs registers
        nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons cycle rest ih =>
      intro staticWidth countBound dataCopy cycleBound files bar0 bar1 outputs registers
        nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      dsimp only at executed
      cases lower : lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } with
      | none =>
          rw [lower] at executed
          dsimp only at executed
          simp at executed
      | some accesses =>
          rw [lower] at executed
          dsimp only at executed
          obtain ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩ := accesses
          cases readA : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (stateForwardingSlots readState pe) cycle sourceAInput with
          | failure =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | ok sourceA =>
              rw [readA] at executed
              dsimp only at executed
              cases sourceB? : sourceBOption with
              | none =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
                  | none =>
                      rw [flush] at executed
                      dsimp only at executed
                      simp at executed
                  | some flushSelection =>
                      rw [flush] at executed
                      dsimp only at executed
                      split at executed
                      · simp at executed
                      · rename_i middleFiles middleBar0 middleBar1 wrote
                        have sourceACopy : IsWelcomeCopy (sourceA.low.extractLsb' 32 32) :=
                          dataCopy cycle (by simp)
                            ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩
                            lower sourceA readA
                        obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
                          executeParsedFloatReluAtPE_writeDestinations_lm1Facts currentState
                            hasSingleLineMask coordinates cycle _ _ w destinations
                            (fun destination member bank width pair bankEq =>
                              staticWidth cycle (by simp)
                                ⟨precision, name, unsigned, sourceAInput, sourceBOption,
                                  destinations⟩ lower destination member bank width pair bankEq)
                            (fun bound => welcomePEFloatReluFlushCopy
                              precision name unsigned sourceA none flushSelection bound sourceACopy)
                            files bar0 bar1 middleFiles middleBar0 middleBar1 wrote
                        obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
                          ih (fun cycle' member => staticWidth cycle' (List.mem_cons_of_mem _ member))
                            (fun cycle' member => countBound cycle' (List.mem_cons_of_mem _ member))
                            (fun cycle' member => dataCopy cycle' (List.mem_cons_of_mem _ member))
                            (by simp only [List.length_cons] at cycleBound; omega)
                            middleFiles middleBar0 middleBar1 _ registers nextBar0 nextBar1
                            nextOutputs executed
                        refine ⟨headWrites ++ restWrites, ?_, ?_, ?_⟩
                        · rw [restCommit, headCommit]
                          exact (commitParsedMaskedWrites_append files headWrites restWrites).symm
                        · exact lm1WriteFacts_append w headWrites restWrites headShape restShape
                        · rw [List.filter_append, List.length_append]
                          have headLe :
                              (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 :=
                            le_trans headCount
                              (countBound cycle (by simp)
                                ⟨precision, name, unsigned, sourceAInput, sourceBOption,
                                  destinations⟩ lower)
                          have bound :
                              (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length +
                                (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
                                rest.length + 1 := by omega
                          simpa [List.length_cons] using bound
              | some sourceBInput =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases readB : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
                      (stateForwardingSlots readState pe) cycle sourceBInput with
                  | failure =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | unknown =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | ok sourceB =>
                      rw [readB] at executed
                      dsimp only at executed
                      cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
                      | none =>
                          rw [flush] at executed
                          dsimp only at executed
                          simp at executed
                      | some flushSelection =>
                          rw [flush] at executed
                          dsimp only at executed
                          split at executed
                          · simp at executed
                          · rename_i middleFiles middleBar0 middleBar1 wrote
                            have sourceACopy : IsWelcomeCopy (sourceA.low.extractLsb' 32 32) :=
                              dataCopy cycle (by simp)
                                ⟨precision, name, unsigned, sourceAInput, sourceBOption,
                                  destinations⟩ lower sourceA readA
                            obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
                              executeParsedFloatReluAtPE_writeDestinations_lm1Facts currentState
                                hasSingleLineMask coordinates cycle _ _ w destinations
                                (fun destination member bank width pair bankEq =>
                                  staticWidth cycle (by simp)
                                    ⟨precision, name, unsigned, sourceAInput, sourceBOption,
                                      destinations⟩ lower destination member bank width pair bankEq)
                                (fun bound => welcomePEFloatReluFlushCopy
                                  precision name unsigned sourceA (some sourceB) flushSelection bound
                                  sourceACopy)
                                files bar0 bar1 middleFiles middleBar0 middleBar1 wrote
                            obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
                              ih (fun cycle' member =>
                                  staticWidth cycle' (List.mem_cons_of_mem _ member))
                                (fun cycle' member =>
                                  countBound cycle' (List.mem_cons_of_mem _ member))
                                (fun cycle' member => dataCopy cycle' (List.mem_cons_of_mem _ member))
                                (by simp only [List.length_cons] at cycleBound; omega)
                                middleFiles middleBar0 middleBar1 _ registers nextBar0 nextBar1
                                nextOutputs executed
                            refine ⟨headWrites ++ restWrites, ?_, ?_, ?_⟩
                            · rw [restCommit, headCommit]
                              exact (commitParsedMaskedWrites_append files headWrites restWrites).symm
                            · exact lm1WriteFacts_append w headWrites restWrites headShape restShape
                            · rw [List.filter_append, List.length_append]
                              have headLe :
                                  (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 :=
                                le_trans headCount
                                  (countBound cycle (by simp)
                                    ⟨precision, name, unsigned, sourceAInput, sourceBOption,
                                      destinations⟩ lower)
                              have bound :
                                  (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length +
                                    (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
                                    rest.length + 1 := by omega
                              simpa [List.length_cons] using bound


theorem welcomePEFloatReluCyclesShape : WelcomePEFloatReluCyclesShape := by
  intro readState currentState expression pe hasSingleLineMask coordinates sourceContext w
    staticWidth countBound dataCopy files bar0 bar1 outputs registers nextBar0 nextBar1
    nextOutputs executed
  obtain ⟨writes, commitEq, shape, count⟩ :=
    executeParsedFloatReluAtPE_runCycles_lm1Facts readState currentState expression pe
      hasSingleLineMask coordinates sourceContext w [0, 1, 2, 3]
      (fun cycle member => staticWidth cycle (by simpa using member))
      (fun cycle member => countBound cycle (by simpa using member))
      (fun cycle member => dataCopy cycle (by simpa using member))
      (by simp)
      files bar0 bar1 outputs registers nextBar0 nextBar1 nextOutputs executed
  refine ⟨writes, commitEq, ?_⟩
  by_cases isDouble : w = PEMemory.Width.double
  · left
    rw [isDouble] at shape
    exact lm1WriteFacts_doubleCopy writes shape
  · right
    exact lm1WriteFacts_narrow writes w shape isDouble (by simpa using le_trans count (by simp))

/-! ## 3. Half-precision block float at the zero input
`WelcomePEBlockFloatHalfZeroInputCopy` -/

/-- Any `[i]?` lookup in a list of zeros has default `0`. -/
theorem list_getElem?_getD_zero (l : List Nat) (h : ∀ x ∈ l, x = 0) (i : Nat) :
    (l[i]?).getD 0 = 0 := by
  cases hh : l[i]? with
  | none => rfl
  | some x =>
      rw [h x (List.mem_of_getElem? hh)]
      rfl

/-- **Half-precision block float at the zero input is the zero bus, for every
`keep` and `extended`.**  The `parsedBlockFloat .half` branch taken at zero
values is the `maxExponent = 0` branch, which returns the sign of the zero
value, i.e. `0`; the common exponent never reaches `exponentMax = 63` because it
is at most `1 + (9 - keep) ≤ 10`. -/
theorem parsedBlockFloatMab_h_zero (keep : Nat) (extended : Bool) (pe : Fin 4) :
    parsedBlockFloatMab .h keep extended (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) pe =
      ⟨0, 0⟩ := by
  have hf : parsedFloatFormat ParsedPrecision.h = RRN.FloatPrecision.half := rfl
  have hm : RRN.FloatPrecision.half.mantissaBits = 9 := rfl
  have he : RRN.FloatPrecision.half.exponentMax = 63 := rfl
  have hw : RRN.FloatPrecision.half.width = 16 := rfl
  have hcommon : (if (0 : Nat) = 2 ^ keep - 1 then 1 else 0) + (9 - keep) < 63 := by
    have h4 : 9 - keep ≤ 9 := by omega
    have h5 : (if (0 : Nat) = 2 ^ keep - 1 then 1 else 0) ≤ 1 := by split <;> omega
    omega
  simp [parsedBlockFloatMab, parsedBlockFloat, hf, hm, he, hw, hcommon,
    list_getElem?_getD_zero]

/-- **`WelcomePEBlockFloatHalfZeroInputCopy`.** -/
theorem welcomePEBlockFloatHalfZeroInputCopy : WelcomePEBlockFloatHalfZeroInputCopy := by
  intro keep extended pe selection bound
  rw [parsedBlockFloatMab_h_zero keep extended pe]
  rw [unpackALUBus_two_zero _ (parsedOutputAfterFlush_low_zero selection _ rfl) bound]
  exact isWelcomeCopy_zero

/-! ## 4. The block-float per-coordinate folds
`WelcomePEBlockFloatMabShape`, conditional on the third-word copy -/

theorem executeParsedBlockFloatAtMAB_apply_lm1Facts
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (output : IntegerALU.Bus) (oldContext coords : ParsedIntegerContext) (w : PEMemory.Width)
    (destinations : List ParsedOperand)
    (staticWidth : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output oldContext
        coords destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_2] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
          output 0 cycle currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
                oldContext coords rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = .ok (nextFiles, nextBar0, nextBar1) := executed
          obtain ⟨prepared, commitEq, shape, provenance⟩ :=
            writeParsedMslMsrDestination?_facts files destination
              { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
              output 0 cycle currentState.maskDirective hasSingleLineMask write w
              (fun bank width pair bankEq => staticWidth destination (by simp) bank width pair bankEq)
              dataCopy lowered
          obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
            ih (fun item member => staticWidth item (List.mem_cons_of_mem _ member))
              write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              nextFiles nextBar0 nextBar1 tailExecuted
          refine ⟨prepared :: restWrites, ?_, ?_, ?_⟩
          · rw [restCommit, commitEq]
            simpa using (commitParsedMaskedWrites_append files [prepared] restWrites).symm
          · have appended := lm1WriteFacts_append w [prepared] restWrites shape restShape
            simpa using appended
          · by_cases isLm1 : PreparedParsedMaskedWrite.isLm1Write prepared = true
            · have destinationLm1 : ParsedOperand.isLm1MemoryDestination destination = true := by
                rcases prepared with ⟨headDestination, headUpdate, headData, headSelection⟩
                cases headDestination with
                | none => simp [PreparedParsedMaskedWrite.isLm1Write] at isLm1
                | some access =>
                    simp only [PreparedParsedMaskedWrite.isLm1Write, beq_iff_eq] at isLm1
                    cases access with
                    | mk bank width address =>
                        cases isLm1
                        exact provenance width address rfl
              have leftEq : ((prepared :: restWrites).filter
                  PreparedParsedMaskedWrite.isLm1Write).length =
                  (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length + 1 := by
                simp [isLm1]
              have rightEq : (List.filter ParsedOperand.isLm1MemoryDestination
                    (destination :: rest)).length =
                  (List.filter ParsedOperand.isLm1MemoryDestination rest).length + 1 := by
                simp [destinationLm1]
              rw [leftEq, rightEq]
              omega
            · have isLm1False : PreparedParsedMaskedWrite.isLm1Write prepared = false := by
                simpa using isLm1
              have leftEq : ((prepared :: restWrites).filter
                  PreparedParsedMaskedWrite.isLm1Write).length =
                  (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length := by
                simp [isLm1False]
              rw [leftEq]
              refine le_trans restCount ?_
              cases hd : ParsedOperand.isLm1MemoryDestination destination <;>
                simp [hd]


theorem executeParsedBlockFloatAtMAB_writePEs_lm1Facts
    (expression : ParsedExpr)
    (writeDestinations : Fin 4 → Fin 4 → IntegerALU.Bus → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → StepResult (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (w : PEMemory.Width)
    (writeFacts : ∀ (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (outputCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
      (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12),
      writeDestinations pe cycle output files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧ Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1)
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (busesCopy : ∀ (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (buses pe)) ⟨2, bound⟩))
    (target : Fin 4) :
    ∀ (pes : List (Fin 4)), pes.Nodup →
      ∀ (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
        (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
        (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
        executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses pes files
          bar0 bar1 outputs = .ok results →
        ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
          Lm1WriteFacts w writes ∧
          (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
            (if target ∈ pes then 1 else 0) := by
  intro pes
  induction pes with
  | nil =>
      intro nodup files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      refine ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons pe rest ih =>
      intro nodup files bar0 bar1 outputs results executed
      obtain ⟨headNotMem, restNodup⟩ := List.nodup_cons.mp nodup
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          dsimp only at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeDestinations pe cycle
              (parsedOutputAfterFlush flushSelection (buses pe)) (files pe) (bar0 pe) (bar1 pe) with
          | failure =>
              rw [wrote] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              dsimp only at executed
              simp at executed
          | ok result =>
              obtain ⟨nextPEFiles, nextBar0, nextBar1⟩ := result
              rw [wrote] at executed
              dsimp only at executed
              obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
                writeFacts pe cycle (parsedOutputAfterFlush flushSelection (buses pe))
                  (fun bound => parsedOutputAfterFlush_unpack_two_isWelcomeCopy flushSelection
                    (buses pe) bound (busesCopy pe bound))
                  (files pe) (bar0 pe) (bar1 pe) nextPEFiles nextBar0 nextBar1 wrote
              obtain ⟨tailWrites, tailCommit, tailShape, tailCount⟩ :=
                ih restNodup
                  (fun other => if (other == pe) = true then nextPEFiles else files other)
                  (fun other => if (other == pe) = true then nextBar0 else bar0 other)
                  (fun other => if (other == pe) = true then nextBar1 else bar1 other)
                  (fun other index =>
                    if (other == pe && index == cycle) = true
                    then parsedOutputAfterFlush flushSelection (buses pe)
                    else outputs other index)
                  results executed
              by_cases same : target = pe
              · have notMemRest : target ∉ rest := fun member => headNotMem (same ▸ member)
                refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
                · rw [tailCommit]
                  simp only [beq_iff_eq, same, ite_true]
                  rw [headCommit, commitParsedMaskedWrites_append]
                · exact lm1WriteFacts_append w headWrites tailWrites headShape tailShape
                · rw [List.filter_append, List.length_append]
                  have tailZero :
                      (tailWrites.filter PreparedParsedMaskedWrite.isLm1Write).length = 0 := by
                    have bound := tailCount
                    have hif : (if target ∈ rest then (1 : Nat) else 0) = 0 := by
                      rw [if_neg notMemRest]
                    rw [hif] at bound
                    omega
                  have goalOne : (if target ∈ pe :: rest then (1 : Nat) else 0) = 1 := by
                    rw [if_pos (by simp [same])]
                  rw [tailZero, goalOne]
                  simpa using headCount
              · refine ⟨tailWrites, ?_, ?_, ?_⟩
                · rw [tailCommit]
                  have different : (target == pe) = false := by
                    simp [beq_iff_eq, same]
                  simp [different]
                · exact tailShape
                · have hiff : (target ∈ pe :: rest) ↔ (target ∈ rest) := by
                    simp [List.mem_cons, same]
                  by_cases hmem : target ∈ rest
                  · rw [if_pos (hiff.mpr hmem)]
                    rw [if_pos hmem] at tailCount
                    exact tailCount
                  · rw [if_neg (fun hc => hmem (hiff.mp hc))]
                    rw [if_neg hmem] at tailCount
                    exact tailCount


theorem executeParsedBlockFloatAtMAB_runCycles_lm1Facts
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (w : PEMemory.Width)
    (writeFacts : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (busesCopy : ∀ (pe : Fin 4) (bound : 2 < 4),
        IsWelcomeCopy ((unpackALUBus (buses pe)) ⟨2, bound⟩))
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∀ target : Fin 4, ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1)
    (busCopy : ∀ (buses : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
        accesses.extended buses pe)) ⟨2, bound⟩))
    (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1
        outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_2] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i inputBuses ranRead
        split at executed
        · simp at executed
        · simp at executed
        · rename_i results' ranWrite
          obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
            writeFacts cycle
              (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
              (fun pe bound => busCopy _ pe bound)
              files bar0 bar1 outputs results' ranWrite target
          obtain ⟨tailWrites, tailCommit, tailShape, tailCount⟩ :=
            ih (fun pe => (results' pe).1) (fun pe => (results' pe).2.1)
              (fun pe => (results' pe).2.2.1) (fun pe index => (results' pe).2.2.2 index)
              results executed
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · exact lm1WriteFacts_append w headWrites tailWrites headShape tailShape
          · rw [List.filter_append, List.length_append]
            have bound : (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length +
                (tailWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
                rest.length + 1 := by omega
            simpa [List.length_cons] using bound

theorem executeParsedBlockFloat_writeCycle_lm1Facts
    (currentState : State) (hasSingleLineMask : Bool) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (form : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus),
      writeCycle cycle buses files bar0 bar1 outputs =
        Id.run (executeParsedBlockFloatAtMAB.writePEs expression
          (fun pe cycle output files bar0 bar1 =>
            Id.run (executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
              (currentState.peContext (physicalPEId coordinate pe))
              (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
              accesses.destinations files bar0 bar1))
          cycle buses (List.finRange 4) files bar0 bar1 outputs))
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (busesCopy : ∀ (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (buses pe)) ⟨2, bound⟩))
    (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (executed : writeCycle cycle buses files bar0 bar1 outputs = .ok results)
    (target : Fin 4) :
    ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
      Lm1WriteFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 := by
  rw [form cycle buses files bar0 bar1 outputs] at executed
  obtain ⟨writes, commitEq, shape, count⟩ :=
    executeParsedBlockFloatAtMAB_writePEs_lm1Facts expression _ w
      (fun pe cyc out outCopy fl b0 b1 nf nb0 nb1 hh => by
        obtain ⟨ws, wsCommit, wsShape, wsCount⟩ :=
          executeParsedBlockFloatAtMAB_apply_lm1Facts currentState hasSingleLineMask cyc out
            (currentState.peContext (physicalPEId coordinate pe))
            (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe)) w
            accesses.destinations staticWidth outCopy fl b0 b1 nf nb0 nb1 hh
        exact ⟨ws, wsCommit, wsShape, le_trans wsCount countBound⟩)
      cycle buses busesCopy target
      (List.finRange 4) (List.nodup_finRange 4) files bar0 bar1 outputs results executed
  refine ⟨writes, commitEq, shape, ?_⟩
  have one : (if target ∈ List.finRange 4 then (1 : Nat) else 0) = 1 := by simp
  rwa [one] at count



theorem blockFloatPEId_inj (coordinate : MABCoordinate) {a b : Fin 4}
    (h : physicalPEId coordinate a = physicalPEId coordinate b) : a = b := by
  have := congrArg Fin.val h
  simp only [physicalPEId] at this
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem blockFloatPEId_beq (coordinate : MABCoordinate) (a b : Fin 4) :
    (physicalPEId coordinate a == physicalPEId coordinate b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · have h' : physicalPEId coordinate a ≠ physicalPEId coordinate b :=
      fun e => h (blockFloatPEId_inj coordinate e)
    simp [h, h']







theorem blockFloatFoldl_peRegisters_frame (noForward : Bool) (coordinate : MABCoordinate)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (p : PEId) :
    ∀ (pes : List (Fin 4)) (state : State),
      (∀ pe ∈ pes, p ≠ physicalPEId coordinate pe) →
      ((pes.foldl (fun state pe =>
        let peId := physicalPEId coordinate pe
        let (files, bar0, bar1, outputs) := results pe
        let forwarding : Forwarding.Slots := fun unit cycle =>
          if noForward then state.forwarding peId unit cycle
          else if unit == .alu then .known (outputs cycle)
          else state.forwarding peId unit cycle
        let forwardingValid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
          if noForward then state.forwardingValid peId unit cycle
          else if unit == .alu then true
          else state.forwardingValid peId unit cycle
        { state with
          peRegisters := fun other => if other == peId then files else state.peRegisters other
          forwarding := fun other => if other == peId then forwarding else state.forwarding other
          forwardingValid := fun other => if other == peId then forwardingValid else state.forwardingValid other
          peContext := fun other => if other == peId then
            { state.peContext other with bar0 := bar0, bar1 := bar1 }
            else state.peContext other }) state)).peRegisters p = state.peRegisters p := by
  intro pes
  induction pes with
  | nil =>
      intro state _
      rfl
  | cons pe rest ih =>
      intro state notTouched
      rw [List.foldl_cons]
      rw [ih _ (fun pe' member => notTouched pe' (by simp [member]))]
      simp only []
      simp [beq_iff_eq, notTouched pe (by simp)]

theorem blockFloatFoldl_peRegisters_target (noForward : Bool) (coordinate : MABCoordinate)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (state : State), pes.Nodup → target ∈ pes →
      ((pes.foldl (fun state pe =>
        let peId := physicalPEId coordinate pe
        let (files, bar0, bar1, outputs) := results pe
        let forwarding : Forwarding.Slots := fun unit cycle =>
          if noForward then state.forwarding peId unit cycle
          else if unit == .alu then .known (outputs cycle)
          else state.forwarding peId unit cycle
        let forwardingValid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
          if noForward then state.forwardingValid peId unit cycle
          else if unit == .alu then true
          else state.forwardingValid peId unit cycle
        { state with
          peRegisters := fun other => if other == peId then files else state.peRegisters other
          forwarding := fun other => if other == peId then forwarding else state.forwarding other
          forwardingValid := fun other => if other == peId then forwardingValid else state.forwardingValid other
          peContext := fun other => if other == peId then
            { state.peContext other with bar0 := bar0, bar1 := bar1 }
            else state.peContext other }) state)).peRegisters (physicalPEId coordinate target) =
        (results target).1 := by
  intro pes
  induction pes with
  | nil =>
      intro state _ member
      simp at member
  | cons pe rest ih =>
      intro state nodup member
      obtain ⟨headNotMem, restNodup⟩ := List.nodup_cons.mp nodup
      rw [List.foldl_cons]
      by_cases same : target = pe
      · subst same
        rw [blockFloatFoldl_peRegisters_frame noForward coordinate results
          (physicalPEId coordinate target) rest _
          (fun pe' member hpe' => headNotMem ((blockFloatPEId_inj coordinate hpe').symm ▸ member))]
        simp only []
        simp
      · have memberRest : target ∈ rest := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h same
          · exact h
        exact ih _ restNodup memberRest


theorem welcomePEBlockFloatMabShape_of_busCopy
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (busCopy : ∀ (buses : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
        accesses.extended buses pe)) ⟨2, bound⟩))
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∀ pe : Fin 4,
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters (physicalPEId coordinate pe) =
          commitParsedMaskedWrites
            (currentState.peRegisters (physicalPEId coordinate pe)) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  intro pe
  rw [executeParsedBlockFloatAtMAB.eq_1, lowered] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i results ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, shape, count⟩ :=
      executeParsedBlockFloatAtMAB_runCycles_lm1Facts accesses _ _ w
        (fun cycle buses busesCopy files bar0 bar1 outputs results h target =>
          executeParsedBlockFloat_writeCycle_lm1Facts currentState hasSingleLineMask expression coordinate accesses w
            staticWidth countBound _ (fun _ _ _ _ _ _ => rfl) cycle buses busesCopy files bar0 bar1
            outputs results h target)
        busCopy pe [0, 1, 2, 3] _ _ _ _ results ran
    subst executed
    refine ⟨writes, ?_, ?_⟩
    · rw [blockFloatFoldl_peRegisters_target noForward coordinate results pe
        (List.finRange 4) currentState (List.nodup_finRange 4) (List.mem_finRange pe)]
      simpa using committed
    · by_cases isDouble : w = PEMemory.Width.double
      · left
        rw [isDouble] at shape
        exact lm1WriteFacts_doubleCopy writes shape
      · right
        exact lm1WriteFacts_narrow writes w shape isDouble (by simpa using count)

/-- **The block-float coordinate shape for the precisions whose low half is
zero.**  For `.d`, `.f` and `.g` the low half of `parsedBlockFloatMab` is
structurally zero, so the third-word copy hypothesis of
`welcomePEBlockFloatMabShape_of_busCopy` is discharged unconditionally. -/
theorem welcomePEBlockFloatMabShape_of_precision_low_zero
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (lowZero : accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g)
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∀ pe : Fin 4,
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters (physicalPEId coordinate pe) =
          commitParsedMaskedWrites
            (currentState.peRegisters (physicalPEId coordinate pe)) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  refine welcomePEBlockFloatMabShape_of_busCopy readState currentState expression coordinate
    noForward hasSingleLineMask next accesses w lowered staticWidth countBound ?_ executed
  intro buses pe bound
  rcases lowZero with h | h | h
  · rw [h]
    rw [unpackALUBus_two_zero _ (parsedBlockFloatMab_low_zero_d _ _ _ _) bound]
    exact isWelcomeCopy_zero
  · rw [h]
    rw [unpackALUBus_two_zero _ (parsedBlockFloatMab_low_zero_f _ _ _ _) bound]
    exact isWelcomeCopy_zero
  · rw [h]
    rw [unpackALUBus_two_zero _ (parsedBlockFloatMab_low_zero_g _ _ _ _) bound]
    exact isWelcomeCopy_zero

/-- **The `.h` obstruction.**  Half-precision block float does not have a zero
low half, and at a nonzero input its third word is not a copy: with input bus
`⟨0, 0x3f023f023f023f02⟩` the low half is `0x3f813f813f813f81`, whose third word
`0x3f813f81` has bits outside `welcomeCopyMask = 0x80008000`.  This is exactly
the data the named `WelcomePEBlockFloatMabShape` does not control. -/
theorem parsedBlockFloatMab_h_third_word_not_copy :
    ¬ IsWelcomeCopy
      ((parsedBlockFloatMab .h 9 false
        (fun _ => (⟨0, 0x3f023f023f023f02⟩ : IntegerALU.Bus)) 0).low.extractLsb' 32 32) := by
  unfold IsWelcomeCopy welcomeCopyMask
  decide

/-! ## 5. The zero-state float-relu read
`WelcomePEFloatReluZeroReadCopy` is refuted -/

/-- **`WelcomePEFloatReluZeroReadCopy` is false as stated.**  The all-zero state
fixes the register files and the forwarding slots, but not the lowering
`context`, and a `.fixed` float-relu source is read off that context.  Take
precision `.f` and source `.fixed .l2bid` with `context.group = 1`: the lowering
is `.fixed (replicateIntegerLane .word 2)`, the read is `.ok` of that bus, and
its copied word is `2`, which is not a welcome copy.  The missing hypothesis is
the PE restriction (with the state's own context); at `welcomePE` every fixed
value is `0` or `msb1`, which is the `WelcomePlainStep` lemma. -/
theorem not_welcomePEFloatReluZeroReadCopy : ¬ WelcomePEFloatReluZeroReadCopy := by
  intro h
  let expression : ParsedExpr :=
    { op := .alu .passa (some .f) false none
      sources := [.fixed .l2bid]
      destinations := [.nowrite]
      flush := none
      text := "" }
  let context : ParsedIntegerContext :=
    { pe := 0, cycle := 0, bar0 := 0, bar1 := 0, tWord := 0,
      group := 1, l2b := 0, l1b := 0, mab := 0 }
  have lowered : lowerParsedFloatRelu? expression context =
      some ⟨.f, .passa, false, .fixed (replicateIntegerLane .word 2), none,
        [.nowrite]⟩ := by
    simp [lowerParsedFloatRelu?, expression, context, ParsedOperand.toParsedIntegerInput?,
      ParsedFixed.integerValue, ParsedPrecision.laneWidth]
  have read : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState welcomeZeroWords).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState welcomeZeroWords) 0) 0
      (.fixed (replicateIntegerLane .word 2)) =
      .ok (replicateIntegerLane .word 2) := by
    simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]
  have copy := h 0 0 expression context _ lowered (replicateIntegerLane .word 2) read
  have value : (replicateIntegerLane IntegerALU.Precision.word 2).low.extractLsb' 32 32 =
      (2 : BitVec 32) := by
    decide
  rw [value] at copy
  unfold IsWelcomeCopy welcomeCopyMask at copy
  revert copy
  decide

end ProofsLean.MNCore
