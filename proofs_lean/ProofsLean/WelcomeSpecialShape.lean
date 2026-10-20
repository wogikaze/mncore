import ProofsLean.WelcomeGapShape

/-! # The three special ALU families: row-level write shapes at the all-zero state

`WelcomeGapShape.lean` (round 35, item F5) proves that the six-family split of
the supported `.pe` producer set is incomplete: `parsedExprIsSupportedPELineProducer`
also accepts the three *special ALU* stages

* `msl` / `msr`  (`executeParsedMslMsrProducers`, per PE `executeParsedMslMsrAtPE`),
* the float-relu name set (`executeParsedFloatReluProducers`, per PE
  `executeParsedFloatReluAtPE`), and
* block float `bfn` / `bfe` (`executeParsedBlockFloatProducer`, per MAB
  coordinate `executeParsedBlockFloatAtMAB`),

and that these rows write PE register files through `writeParsedMslMsrDestination?`
(`writeDirectAccessMasked` / `Masks.writeRegister`), so a line containing one of
them is not covered by the plain obligation nor by any of the six family
obligations.

This module starts the row-level analysis of the three families at the all-zero
initial state.  The shape target is the one `WelcomeValueBound.lean` §5/§6
consumes for a single row: either every `.lm1` destination of the row's prepared
write list is a 4-aligned `.double` block whose third bus word is copied
(`Lm1WritesDoubleCopy`), or the row's `.lm1` writes fit in at most four windows
of at most two words (`Lm1WritesNarrow`).

## What is proved here

1. **The shared destination writer.**  A successful
   `writeParsedMslMsrDestination?` is exactly the commit of a one-element
   prepared write list, and the per-destination `.lm1` facts (static width,
   alignment, third-word copy) transport to that list.  This is the lemma all
   three families need.
2. **The MSL/MSR row.**  The destination fold and the four-cycle fold of
   `executeParsedMslMsrAtPE` keep the two `.lm1` shape facts, with at most one
   `.lm1` write per cycle and at most four in the row.  The MSL/MSR output bus
   has a zero low half (`mslMsrOutputBus`), so its third data word is always a
   copy: no read hypothesis is needed.
3. The exact row statement `WelcomePEMslMsrRowShape` and the precise residual
   statement for the other two families, whose data words are *not* copies
   unconditionally (float-relu keeps the first source's low half; half-precision
   block float builds its low half from lanes 4–7).

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing here claims
`LowerBound 2`, `Optimal`, or any line-level (as opposed to row-level) shape.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 0. The special-ALU output buses -/

theorem mslMsrOutputBus_low (source : IntegerALU.Bus) :
    (mslMsrOutputBus source).low = 0 := rfl

/-- **The MSL/MSR third bus word is always copied.**  The row shifts the
neighbouring PE's high long-word into the high half and zeroes the low half, and
a flush only ANDs the bus. -/
theorem mslMsr_output_word_two_copy (selection : Option PEWordSelection)
    (source : IntegerALU.Bus) (bound : 2 < 4) :
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection (mslMsrOutputBus source)))
        ⟨2, bound⟩) := by
  have lowZero : (parsedOutputAfterFlush selection (mslMsrOutputBus source)).low = 0 :=
    parsedOutputAfterFlush_low_zero selection _ (mslMsrOutputBus_low source)
  rw [unpackALUBus_two_zero _ lowZero bound]
  exact isWelcomeCopy_zero

/-- The float-relu stage only rewrites the high half: the lower half is the
first source bus, unchanged. -/
theorem parsedFloatReluBus_low (precision : ParsedPrecision) (name : ParsedAluName)
    (unsigned : Bool) (left : IntegerALU.Bus) (right : Option IntegerALU.Bus) :
    (parsedFloatReluBus precision name unsigned left right).1.low = left.low := rfl

/-- For the 64- and 32-bit block-float formats the low half of the result is
zero, so the third bus word is a copy. -/
theorem parsedBlockFloatMab_low_zero_d (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) :
    (parsedBlockFloatMab .d keep extended inputs pe).low = 0 := rfl

theorem parsedBlockFloatMab_low_zero_f (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) :
    (parsedBlockFloatMab .f keep extended inputs pe).low = 0 := rfl

theorem parsedBlockFloatMab_low_zero_g (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) :
    (parsedBlockFloatMab .g keep extended inputs pe).low = 0 := rfl

/-- **The shared per-destination facts.**  Any successful
`writeParsedMslMsrDestination?` is the commit of a *single* prepared write, and
that write carries the row's static `.lm1` width, the alignment of its resolved
direct access and the copy property of the output's third word.  The
provenance conjunct (last component) says that a `.lm1` destination of the
prepared write always comes from an `.lm1` *memory destination operand*, which
is what bounds the number of `.lm1` writes by the number of `.lm1` destinations. -/
theorem writeParsedMslMsrDestination?_facts
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (w : PEMemory.Width)
    (staticWidth : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank = PEMemory.Bank.lm1 → width = w)
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ prepared : PreparedParsedMaskedWrite,
      write.files = commitParsedMaskedWrites files [prepared] ∧
      Lm1WriteFacts w [prepared] ∧
      (∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        prepared.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
          ParsedOperand.isLm1MemoryDestination destination = true) := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination? (ParsedOperand.mem access negated extended
          rounded mask) context.pe cycle context.bar0 context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.mem access negated
              extended rounded mask) found.bank files.maskRegisters cycle directive
              hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              have alignedAll : found.address.val % found.width.words = 0 :=
                parsedOperand_toDirectMemoryAccessMode_aligned
                  (ParsedOperand.mem access negated extended rounded mask) true context.pe
                  cycle context.bar0 context.bar1 context.tWord found h
              have static := ParsedOperand.toDirectMemoryDestination?_bankWidth
                (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
                context.bar0 context.bar1 context.tWord
              rw [h] at static
              simp only [Option.map_some] at static
              simp [writeParsedMslMsrDestination?, h, h2] at lowered
              obtain rfl := lowered
              refine ⟨⟨some found, none, unpackALUBus output, selection⟩, ?_, ?_, ?_⟩
              · simp [commitParsedMaskedWrites, writeDirectAccessMasked]
              · intro other member width address dest
                simp only [List.mem_singleton] at member
                subst member
                simp only [Option.some.injEq] at dest
                obtain rfl : found = ⟨PEMemory.Bank.lm1, width, address⟩ := dest
                have widthEq : width = w := staticWidth _ _ static.symm rfl
                refine ⟨widthEq, ?_, ?_⟩
                · intro isDouble
                  have h4 : width.words = 4 := by rw [isDouble]; rfl
                  rw [h4] at alignedAll
                  exact alignedAll
                · exact dataCopy
              · intro width address dest
                obtain rfl : found = ⟨PEMemory.Bank.lm1, width, address⟩ := by
                  simpa only [Option.some.injEq] using dest
                exact directDestinationBankWidth_isLm1 _ width static.symm
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [writeParsedMslMsrDestination?, h, h2] at lowered
              obtain rfl := lowered
              refine ⟨⟨none, some (found, cycle, flags), unpackALUBus output, ⟨selection, false⟩⟩,
                ?_, ?_, ?_⟩
              · simp [commitParsedMaskedWrites]
              · intro other member width address dest
                simp [List.mem_singleton] at member
                subst member
                simp at dest
              · intro width address dest
                simp at dest
  | bar lm1 width mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [writeParsedMslMsrDestination?, h] at lowered
          obtain rfl := lowered
          refine ⟨⟨none, none, unpackALUBus output, selection⟩, ?_, ?_, ?_⟩
          · simp [commitParsedMaskedWrites]
          · intro other member width' address dest
            simp [List.mem_singleton] at member
            subst member
            simp at dest
          · intro width' address dest
            simp at dest
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      refine ⟨⟨none, none, unpackALUBus output, ⟨0, false⟩⟩, ?_, ?_, ?_⟩
      · simp [commitParsedMaskedWrites]
      · intro other member width address dest
        simp [List.mem_singleton] at member
        subst member
        simp at dest
      · intro width address dest
        simp at dest
  | forward kind neg ext rnd => simp [writeParsedMslMsrDestination?] at lowered
  | fixed value => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar value => simp [writeParsedMslMsrDestination?] at lowered

/-- A prepared write whose `isLm1Write` test is true names an actual `.lm1`
direct access. -/
theorem preparedIsLm1Write_destination (write : PreparedParsedMaskedWrite)
    (isLm1 : PreparedParsedMaskedWrite.isLm1Write write = true) :
    ∃ access : DirectMemoryAccess, write.destination = some access ∧
      access.bank = PEMemory.Bank.lm1 := by
  rcases write with ⟨destination, update, data, selection⟩
  cases destination with
  | none => simp [PreparedParsedMaskedWrite.isLm1Write] at isLm1
  | some access =>
      refine ⟨access, rfl, ?_⟩
      cases access with
      | mk bank width address =>
          simpa [PreparedParsedMaskedWrite.isLm1Write, beq_iff_eq] using isLm1

/-! ## 1. The destination fold of the MSL/MSR row

`executeParsedMslMsrAtPE.runCycles.writeDestinations` applies
`writeParsedMslMsrDestination?` to a list of destination operands.  At the
all-zero state the output bus is `mslMsrOutputBus` (third word copied), so one
call of the fold produces at most one `.lm1` write per `.lm1`-memory
destination operand, and the commit/shape facts of the single destination
compose. -/

theorem mslMsr_writeDestinations_lm1Facts
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus) (w : PEMemory.Width)
    (destinations : List ParsedOperand)
    (staticWidth : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        context cycle output destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      simp only [executeParsedMslMsrAtPE.runCycles.writeDestinations,
        Option.some.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      unfold executeParsedMslMsrAtPE.runCycles.writeDestinations at executed
      simp only at executed
      cases hw : writeParsedMslMsrDestination? files destination
          { pe := context.pe, cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := context.tWord,
            group := context.group, l2b := context.l2b, l1b := context.l1b, mab := context.mab }
          output 0 cycle currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [hw] at executed
          simp at executed
      | some write =>
          rw [hw] at executed
          simp only [Bind.bind, Option.bind] at executed
          obtain ⟨prepared, commitEq, shape, provenance⟩ :=
            writeParsedMslMsrDestination?_facts files destination
              { pe := context.pe, cycle := cycle, bar0 := bar0, bar1 := bar1,
                tWord := context.tWord, group := context.group, l2b := context.l2b,
                l1b := context.l1b, mab := context.mab }
              output 0 cycle currentState.maskDirective hasSingleLineMask write w
              (fun bank width pair bankEq => staticWidth destination (by simp) bank width pair bankEq)
              dataCopy hw
          obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
            ih (fun item member => staticWidth item (List.mem_cons_of_mem _ member))
              write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              nextFiles nextBar0 nextBar1 executed
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
                simp [List.filter_cons, isLm1]
              have rightEq : (List.filter ParsedOperand.isLm1MemoryDestination
                    (destination :: rest)).length =
                  (List.filter ParsedOperand.isLm1MemoryDestination rest).length + 1 := by
                simp [List.filter_cons, destinationLm1]
              rw [leftEq, rightEq]
              omega
            · have isLm1False : PreparedParsedMaskedWrite.isLm1Write prepared = false := by
                simpa using isLm1
              have leftEq : ((prepared :: restWrites).filter
                  PreparedParsedMaskedWrite.isLm1Write).length =
                  (restWrites.filter PreparedParsedMaskedWrite.isLm1Write).length := by
                simp [List.filter_cons, isLm1False]
              rw [leftEq]
              refine le_trans restCount ?_
              cases hd : ParsedOperand.isLm1MemoryDestination destination <;>
                simp [List.filter_cons, hd]

/-! ## 2. The four-cycle fold of the MSL/MSR row -/

theorem mslMsr_runCycles_lm1Facts
    (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (sourcePE : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput) (w : PEMemory.Width)
    (staticWidth : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (dataCopy : ∀ (sourceBus : IntegerALU.Bus) (flush : Option PEWordSelection)
      (bound : 2 < 4),
      IsWelcomeCopy
        ((unpackALUBus (parsedOutputAfterFlush flush (mslMsrOutputBus sourceBus))) ⟨2, bound⟩))
    (countBound : (destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (cycles : List (Fin 4)) (cycleBound : cycles.length ≤ 4) :
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (registers : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations sourcePE sourceAt cycles files bar0 bar1 outputs =
          .ok (registers, nextBar0, nextBar1, nextOutputs) →
      ∃ writes : List PreparedParsedMaskedWrite,
        registers = commitParsedMaskedWrites files writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs registers nextBar0 nextBar1 nextOutputs executed
      simp only [executeParsedMslMsrAtPE.runCycles, StepResult.ok.injEq,
        Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs registers nextBar0 nextBar1 nextOutputs executed
      unfold executeParsedMslMsrAtPE.runCycles at executed
      simp only at executed
      cases hsrc : sourceAt cycle with
      | none => simp [hsrc] at executed
      | some source =>
          rw [hsrc] at executed
          dsimp only at executed
          cases hread : ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
              (stateForwardingSlots readState sourcePE) cycle source with
          | failure => simp [hread] at executed
          | unknown => simp [hread] at executed
          | ok sourceBus =>
              rw [hread] at executed
              dsimp only at executed
              cases hflush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
              | none => simp [hflush] at executed
              | some flush =>
                  rw [hflush] at executed
                  dsimp only at executed
                  cases hwrite : executeParsedMslMsrAtPE.runCycles.writeDestinations currentState
                      hasSingleLineMask context cycle
                      (parsedOutputAfterFlush flush (mslMsrOutputBus sourceBus)) destinations
                      files bar0 bar1 with
                  | none => simp [hwrite] at executed
                  | some result =>
                      obtain ⟨headFiles, headBar0, headBar1⟩ := result
                      rw [hwrite] at executed
                      dsimp only at executed
                      obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
                        mslMsr_writeDestinations_lm1Facts currentState hasSingleLineMask context
                          cycle (parsedOutputAfterFlush flush (mslMsrOutputBus sourceBus)) w
                          destinations staticWidth (fun bound => dataCopy sourceBus flush bound)
                          files bar0 bar1 headFiles headBar0 headBar1 hwrite
                      obtain ⟨restWrites, restCommit, restShape, restCount⟩ :=
                        ih (by simp only [List.length_cons] at cycleBound; omega) headFiles
                          headBar0 headBar1
                          (fun index => if index = cycle then
                            parsedOutputAfterFlush flush (mslMsrOutputBus sourceBus)
                            else outputs index)
                          registers nextBar0 nextBar1 nextOutputs executed
                      refine ⟨headWrites ++ restWrites, ?_, ?_, ?_⟩
                      · rw [restCommit, headCommit]
                        exact (commitParsedMaskedWrites_append files headWrites restWrites).symm
                      · exact lm1WriteFacts_append w headWrites restWrites headShape restShape
                      · rw [List.filter_append, List.length_append]
                        have headLe : (headWrites.filter
                            PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 :=
                          le_trans headCount countBound
                        have bound : (headWrites.filter
                            PreparedParsedMaskedWrite.isLm1Write).length +
                            (restWrites.filter
                              PreparedParsedMaskedWrite.isLm1Write).length ≤
                            rest.length + 1 := by
                          omega
                        simpa [List.length_cons] using bound

/-! ## 3. Copy preservation under the flush and at the special outputs

The MSL/MSR row needs no read hypothesis (its third word is always zero).  The
float-relu row and the 64/32-bit block-float rows need only a copy at their
source bus: the flush only ANDs the bus, and a submask of a copy is a copy
(`isWelcomeCopy_and`).  Half-precision block float is the one case whose low
half is not structurally zero; it is the named remainder
`WelcomePEBlockFloatHalfZeroInputCopy`. -/

theorem flushBus_double_word_two_copy (flags : BitVec 4)
    (data : IntegerALU.Bus) (bound : 2 < 4)
    (copy : IsWelcomeCopy ((unpackALUBus data) ⟨2, bound⟩)) :
    IsWelcomeCopy
      ((unpackALUBus (ProofsLean.MNCore.Masks.flushBus .double flags data)) ⟨2, bound⟩) := by
  have copy' : IsWelcomeCopy (data.low.extractLsb' 32 32) := by
    rwa [unpackALUBus_of_val_eq_two data ⟨2, bound⟩ rfl] at copy
  rw [unpackALUBus_of_val_eq_two _ ⟨2, bound⟩ rfl]
  show IsWelcomeCopy
    ((data.low &&& (ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 1) ++
      ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 0))).extractLsb' 32 32)
  rw [BitVec.extractLsb'_and]
  exact isWelcomeCopy_and _ _ copy'

theorem flushBus_long_word_two_copy (flags : BitVec 4)
    (data : IntegerALU.Bus) (bound : 2 < 4)
    (copy : IsWelcomeCopy ((unpackALUBus data) ⟨2, bound⟩)) :
    IsWelcomeCopy
      ((unpackALUBus (ProofsLean.MNCore.Masks.flushBus .long flags data)) ⟨2, bound⟩) := by
  have copy' : IsWelcomeCopy (data.low.extractLsb' 32 32) := by
    rwa [unpackALUBus_of_val_eq_two data ⟨2, bound⟩ rfl] at copy
  have lowEq : (ProofsLean.MNCore.Masks.flushBus .long flags data).low = data.low := by
    show data.low &&& BitVec.allOnes 64 = data.low
    exact BitVec.and_allOnes
  rw [unpackALUBus_of_val_eq_two _ ⟨2, bound⟩ rfl, lowEq]
  exact copy'

/-- The **raw** float-relu bus keeps the first source's low half, so a copied
third word at the first source is a copied third word at the output before the
flush.  The flush case is the named remainder `WelcomePEFloatReluFlushCopy`. -/
theorem parsedFloatRelu_raw_output_word_two_copy
    (precision : ParsedPrecision) (name : ParsedAluName) (unsigned : Bool)
    (left : IntegerALU.Bus) (right : Option IntegerALU.Bus) (bound : 2 < 4)
    (copy : IsWelcomeCopy (left.low.extractLsb' 32 32)) :
    IsWelcomeCopy
      ((unpackALUBus (parsedFloatReluBus precision name unsigned left right).1) ⟨2, bound⟩) := by
  have lowEq := parsedFloatReluBus_low precision name unsigned left right
  rw [unpackALUBus_of_val_eq_two _ ⟨2, bound⟩ rfl, lowEq]
  exact copy

theorem parsedBlockFloatMab_d_word_two_copy (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (selection : Option PEWordSelection)
    (bound : 2 < 4) :
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (parsedBlockFloatMab .d keep extended inputs pe))) ⟨2, bound⟩) := by
  rw [unpackALUBus_two_zero _
    (parsedOutputAfterFlush_low_zero selection _
      (parsedBlockFloatMab_low_zero_d keep extended inputs pe)) bound]
  exact isWelcomeCopy_zero

theorem parsedBlockFloatMab_f_word_two_copy (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (selection : Option PEWordSelection)
    (bound : 2 < 4) :
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (parsedBlockFloatMab .f keep extended inputs pe))) ⟨2, bound⟩) := by
  rw [unpackALUBus_two_zero _
    (parsedOutputAfterFlush_low_zero selection _
      (parsedBlockFloatMab_low_zero_f keep extended inputs pe)) bound]
  exact isWelcomeCopy_zero

theorem parsedBlockFloatMab_g_word_two_copy (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (selection : Option PEWordSelection)
    (bound : 2 < 4) :
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (parsedBlockFloatMab .g keep extended inputs pe))) ⟨2, bound⟩) := by
  rw [unpackALUBus_two_zero _
    (parsedOutputAfterFlush_low_zero selection _
      (parsedBlockFloatMab_low_zero_g keep extended inputs pe)) bound]
  exact isWelcomeCopy_zero

/-! ## 4. The MSL/MSR four-cycle row shape

The mathematical content of the `msl`/`msr` row is complete: at **every**
incoming state, for every destination list and static `.lm1` width, the
four-cycle fold returns a commit list that is either all copied `.double`
blocks or fits in four narrow windows. -/

def WelcomePEMslMsrCyclesShape : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (sourcePE : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput) (w : PEMemory.Width) (cycles : List (Fin 4)),
    (∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w) →
    (destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 →
    cycles.length ≤ 4 →
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (outputs : Fin 4 → IntegerALU.Bus)
      (registers : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
      (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations sourcePE sourceAt cycles files bar0 bar1 outputs =
          .ok (registers, nextBar0, nextBar1, nextOutputs) →
      ∃ writes : List PreparedParsedMaskedWrite,
        registers = commitParsedMaskedWrites files writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

theorem welcomePEMslMsrCyclesShape : WelcomePEMslMsrCyclesShape := by
  intro readState currentState expression hasSingleLineMask context destinations sourcePE
    sourceAt w cycles staticWidth countBound cycleBound files bar0 bar1 outputs registers
    nextBar0 nextBar1 nextOutputs executed
  obtain ⟨writes, commitEq, shape, count⟩ :=
    mslMsr_runCycles_lm1Facts readState currentState expression hasSingleLineMask context
      destinations sourcePE sourceAt w staticWidth
      (fun sourceBus flush bound => mslMsr_output_word_two_copy flush sourceBus bound)
      countBound cycles cycleBound files bar0 bar1 outputs registers nextBar0 nextBar1
      nextOutputs executed
  refine ⟨writes, commitEq, ?_⟩
  by_cases isDouble : w = PEMemory.Width.double
  · left
    rw [isDouble] at shape
    exact lm1WriteFacts_doubleCopy writes shape
  · right
    exact lm1WriteFacts_narrow writes w shape isDouble (by simpa using le_trans count cycleBound)

/-! ## 5. The exact remaining executor links

The `Prop`s of this section are the precise remainder.  None asserts a shape,
none is assumed by any theorem that claims one, and all are pure
unfolding/link statements between the three executors and the folds analysed
above.

For MSL/MSR the only missing step is that `executeParsedMslMsrAtPE` exposes its
`runCycles` call.  The difficulty is syntactic, not mathematical: the executor's
`sourceAt` lambda is compiled to the auxiliary match
`executeParsedMslMsrAtPE.match_3`, so a hand-written copy of the same lambda is a
different constant and cannot be rewritten under the executor's `match`.  The
statement below holds by `rfl` after that unfolding. -/

/-- The source-bus selector of the MSL/MSR row, factored out so that the
exposure statement and the fold statement can use the same term. -/
def mslMsrSourceAt (expression : ParsedExpr) (readState : State) (isMsl : Bool)
    (sourcePE : PEId) : Fin 4 → Option ParsedIntegerInput := fun cycle =>
  match expression.sources with
  | [source] => ParsedOperand.toParsedIntegerInput? source .long
      (ParsedIntegerContext.ofLinearIndex sourcePE).group
      (ParsedIntegerContext.ofLinearIndex sourcePE).l2b
      (ParsedIntegerContext.ofLinearIndex sourcePE).l1b
      (ParsedIntegerContext.ofLinearIndex sourcePE).mab
      (ParsedIntegerContext.ofLinearIndex sourcePE).pe cycle
      (readState.peContext sourcePE).bar0
      (readState.peContext sourcePE).bar1
      (readState.peContext sourcePE).tWord
  | _ => none

/-- **MSL/MSR executor exposure** (the remaining link for this family). -/
def WelcomePEMslMsrExecutorExposure : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool) (next : State) (isMsl : Bool)
    (destinations : List ParsedOperand),
    lowerParsedMslMsr? expression = some (isMsl, destinations) →
    executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next →
    ∃ registers bar0 bar1 outputs,
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        { pe := (ParsedIntegerContext.ofLinearIndex pe).pe,
          cycle := (ParsedIntegerContext.ofLinearIndex pe).cycle,
          bar0 := (readState.peContext pe).bar0, bar1 := (readState.peContext pe).bar1,
          tWord := (readState.peContext pe).tWord,
          group := (ParsedIntegerContext.ofLinearIndex pe).group,
          l2b := (ParsedIntegerContext.ofLinearIndex pe).l2b,
          l1b := (ParsedIntegerContext.ofLinearIndex pe).l1b,
          mab := (ParsedIntegerContext.ofLinearIndex pe).mab }
        destinations (mslMsrSourcePE pe isMsl)
        (mslMsrSourceAt expression readState isMsl (mslMsrSourcePE pe isMsl))
        [0, 1, 2, 3] (currentState.peRegisters pe) (readState.peContext pe).bar0
        (readState.peContext pe).bar1 (fun _ => ⟨0, 0⟩) = .ok (registers, bar0, bar1, outputs) ∧
      next.peRegisters pe = registers

/-- **The MSL/MSR executor row shape** conditional on the exposure link. -/
theorem welcomePEMslMsrExecutorRowShape_of_exposure
    (exposure : WelcomePEMslMsrExecutorExposure)
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool) (next : State) (isMsl : Bool)
    (destinations : List ParsedOperand) (w : PEMemory.Width)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations))
    (staticWidth : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters pe =
        commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  obtain ⟨registers, bar0, bar1, outputs, fold, finalEq⟩ :=
    exposure readState currentState expression pe noForward hasSingleLineMask next isMsl
      destinations lowered executed
  obtain ⟨writes, commitEq, shape⟩ :=
    welcomePEMslMsrCyclesShape readState currentState expression hasSingleLineMask
      { pe := (ParsedIntegerContext.ofLinearIndex pe).pe,
        cycle := (ParsedIntegerContext.ofLinearIndex pe).cycle,
        bar0 := (readState.peContext pe).bar0, bar1 := (readState.peContext pe).bar1,
        tWord := (readState.peContext pe).tWord,
        group := (ParsedIntegerContext.ofLinearIndex pe).group,
        l2b := (ParsedIntegerContext.ofLinearIndex pe).l2b,
        l1b := (ParsedIntegerContext.ofLinearIndex pe).l1b,
        mab := (ParsedIntegerContext.ofLinearIndex pe).mab }
      destinations (mslMsrSourcePE pe isMsl)
      (mslMsrSourceAt expression readState isMsl (mslMsrSourcePE pe isMsl)) w [0, 1, 2, 3]
      staticWidth countBound (by simp) (currentState.peRegisters pe) (readState.peContext pe).bar0
      (readState.peContext pe).bar1 (fun _ => ⟨0, 0⟩) registers bar0 bar1 outputs fold
  exact ⟨writes, by rw [finalEq]; exact commitEq, shape⟩

/-! ## 6. The float-relu and block-float remainders, exactly

Both stages call the shared destination writer analysed in §0, so the
third-word halves of their rows are already closed (`.d`/`.f`/`.g` block float
unconditionally, float relu modulo the zero-state read copy).  What remains is
only the destination/cycle fold of each stage, stated below at the exact
interface of the corresponding executor. -/

/-- **Float-relu row shape, at the fold level** (the remaining fold statement
for this family). -/
def WelcomePEFloatReluCyclesShape : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext)
    (w : PEMemory.Width),
    (∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
      ∀ destination ∈ accesses.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank = PEMemory.Bank.lm1 → width = w) →
    (∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
      (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1) →
    (∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses →
      ∀ sourceA : IntegerALU.Bus,
        ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
          (stateForwardingSlots readState pe) cycle accesses.sourceA = .ok sourceA →
        IsWelcomeCopy (sourceA.low.extractLsb' 32 32)) →
    ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (registers : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask coordinates sourceContext [0, 1, 2, 3] files bar0 bar1 outputs =
          .ok (registers, nextBar0, nextBar1, nextOutputs) →
      ∃ writes : List PreparedParsedMaskedWrite,
        registers = commitParsedMaskedWrites files writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

/-- **The float-relu third-word fact at the all-zero state** (the read-copy
ingredient; it is the read-copy lemma of `WelcomePlainStep` transported to an
arbitrary PE and to the float-relu lowering). -/
def WelcomePEFloatReluZeroReadCopy : Prop :=
  ∀ (pe : PEId) (cycle : Fin 4) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (accesses : ParsedFloatReluAccesses),
    lowerParsedFloatRelu? expression context = some accesses →
    ∀ sourceA : IntegerALU.Bus,
      ParsedIntegerInput.readWithForwarding
        ((welcomeInitialState welcomeZeroWords).peRegisters pe)
        (stateForwardingSlots (welcomeInitialState welcomeZeroWords) pe) cycle
        accesses.sourceA = .ok sourceA →
      IsWelcomeCopy (sourceA.low.extractLsb' 32 32)

/-- **Block-float `.h` third-word fact at the all-zero input.**  This is the one
data-copy case not proved here: half-precision block float builds its low half
from lanes 4–7, so `parsedBlockFloatMab_low_zero_h` does not hold and the zero
input has to be pushed through `parsedBlockFloat .half` (where it is zero for
every `keep` and `extended`, but that is a `parsedBlockFloat` arithmetic
argument, not a structural one). -/
def WelcomePEBlockFloatHalfZeroInputCopy : Prop :=
  ∀ (keep : Nat) (extended : Bool) (pe : Fin 4) (selection : Option PEWordSelection)
    (bound : 2 < 4),
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (parsedBlockFloatMab .h keep extended
          (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) pe))) ⟨2, bound⟩)

/-- **Block-float row shape, at the per-coordinate level** (the remaining fold
statement for this family). -/
def WelcomePEBlockFloatMabShape : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width),
    lowerParsedBlockFloat? expression = some accesses →
    (∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w) →
    (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 →
    executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next →
    ∀ pe : Fin 4,
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters (physicalPEId coordinate pe) =
          commitParsedMaskedWrites
            (currentState.peRegisters (physicalPEId coordinate pe)) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

/-- **Float-relu flush copy** (remaining third-word case for this family).  The
raw bus copy is proved (`parsedFloatRelu_raw_output_word_two_copy`); this states
that the row's flush `parsedOutputAfterFlush selection` preserves it.  The
`.long` and `.double` flush arms are proved to preserve a copy
(`flushBus_long_word_two_copy`, `flushBus_double_word_two_copy`); what is not
formalised is only the `parsedOutputAfterFlush` wrapper's case analysis. -/
def WelcomePEFloatReluFlushCopy : Prop :=
  ∀ (precision : ParsedPrecision) (name : ParsedAluName) (unsigned : Bool)
    (left : IntegerALU.Bus) (right : Option IntegerALU.Bus)
    (selection : Option PEWordSelection) (bound : 2 < 4),
    IsWelcomeCopy (left.low.extractLsb' 32 32) →
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (parsedFloatReluBus precision name unsigned left right).1)) ⟨2, bound⟩)

end ProofsLean.MNCore
