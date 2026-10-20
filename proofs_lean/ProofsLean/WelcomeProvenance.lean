import ProofsLean.WelcomeBoundTwo

/-! # Write provenance for the integer stage of a `.pe` line

`WelcomeBoundTwo.lean` reduces `LowerBound welcomeSealedMachine welcomeSpec 2`
to the refutation of `WelcomePEResidual` and names the missing executor link
`WelcomeWriteProvenance`: after a `.pe` line, PE 0's register file is the commit
of a list of prepared masked writes on the initial file.

This module proves that link **for the plain integer-ALU subclass**
(`parsedExprIsPlainIntegerALU`, i.e. `.alu`/`.zero`/`.immediate` rows outside the
legacy, MSL/MSR, float-relu and block-float families):

* `parsedIntegerMatrixReadLineFourCycleStep_ok_commit` — a successful four-cycle
  integer stage returns the commit of the write list it prepared;
* `executeIntegerProducerLineAtPECore_peRegisters_commit` — a successful per-PE
  core step with no float MAU producer in the line commits a write list on that
  PE's register file, and leaves every other PE's file untouched;
* `executeIntegerProducerLineAtPEs_peRegisters_commit` — the same for the full
  per-PE walk over a duplicate-free PE list;
* `executeIntegerProducerInstructionLine_pe_peRegisters_commit`,
  `executeNormalizedLine_pe_peRegisters_commit` and
  `welcomeWriteProvenance_of_plainIntegerALU` — the same for a whole line, hence
  `WelcomeWriteProvenance` itself for the plain subclass.

It then closes the **`.double` block argument**:

* `commitParsedMaskedWrites_lm1_word_zero_of_double` — a commit whose `.lm1`
  writes are all `.double` blocks on 4-aligned addresses with a zero third data
  word leaves every word `t` with `t % 4 = 2` at its old value;
* `prepareParsedIntegerALUExprCycle_alu_direct` and
  `prepareParsedIntegerALUExprCycle_alu_direct_double_zero` — the per-cycle
  direct-access branch of `prepareParsedIntegerALUExprCycle` yields exactly one
  write, at the lowered operand access, with a zero third data word whenever the
  first read has a zero low half (which every read of the all-zero initial file
  has, rounded or not: `welcomeZero_applyRounding_pack_low_zero`);
* `welcome_not_correct_of_doubleWrites` — a line whose all-zero PE 0 write list
  has that shape is refuted, because word 2 of PE 0 LM1 stays zero;
* `welcomeLowerBound_two_of_residualDoubleShape` and
  `welcomeLowerBound_two_of_twoShapeObligations` — `LowerBound … 2` follows from
  the corresponding write-shape obligation for every residual line.

What remains is exactly the **shape** half, stated as `Prop`s in section 5
(`WelcomePEPlainDoubleShapeObligation`,
`WelcomePEOtherDoubleShapeObligation`, the six per-family specialisations,
`WelcomePENarrowCoverageObligation` and
`WelcomePEConstantInputIndependentObligation`). None of them is assumed, and
neither `LowerBound welcomeSealedMachine welcomeSpec 2` nor
`Optimal … welcomeAnswer` is proved. `welcomeAnswer_optimal_of_lowerBound` only
records that `Optimal` follows from the lower bound.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- A successful four-cycle integer stage returns the commit of the write list
it prepared on the pre-issue register file. -/
theorem parsedIntegerMatrixReadLineFourCycleStep_ok_commit
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (registers : IntegerRegisterFiles) (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (barUpdates : List (Bool × BitVec 12))
    (executed : parsedIntegerMatrixReadLineFourCycleStep files slots store expressions control
      reduced = .ok (registers, nextSlots, barUpdates)) :
    ∃ writes, registers = commitParsedMaskedWrites files writes := by
  unfold parsedIntegerMatrixReadLineFourCycleStep at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i writes preparedSlots preparedBars prepared
    simp only [StepResult.ok.injEq, Prod.mk.injEq] at executed
    exact ⟨writes, executed.1.symm⟩

/-- A successful per-PE core step with no float MAU producer commits a write
list on that PE's register file. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_commit
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ writes, next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)] at executed
    dsimp only at executed
    simp only [updateSupportedPELineForwarding] at executed
    split at executed
    · simp at executed
    · simp at executed
    · simp only [StepResult.ok.injEq] at executed
      obtain ⟨writes, committed⟩ :=
        parsedIntegerMatrixReadLineFourCycleStep_ok_commit _ _ _ _ _ _ _ _ _ fourCycle
      refine ⟨writes, ?_⟩
      subst executed
      simpa using committed

/-- A successful per-PE core step leaves every other PE's register file
untouched. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.peRegisters other = state.peRegisters other := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · split at executed
    · simp at executed
    · simp at executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        simp [different]

/-- A successful per-PE step with no float MAU producer commits a write list on
that PE's register file. -/
theorem executeIntegerProducerLineAtPE_peRegisters_commit
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    ∃ writes, next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_peRegisters_commit expressions state next pe
      floatEmpty executed

/-- A successful per-PE step leaves every other PE's register file untouched. -/
theorem executeIntegerProducerLineAtPE_peRegisters_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.peRegisters other = state.peRegisters other := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_peRegisters_other expressions state next pe other
      different executed

/-- A successful per-PE walk over a duplicate-free PE list commits a write list
on the register file of every PE it visits. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_commit
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup) (p : PEId) (mem : p ∈ pes) :
    ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : p = pe
        · obtain ⟨writes, headCommit⟩ :=
            executeIntegerProducerLineAtPE_peRegisters_commit expressions state middle pe
              floatEmpty headExecuted
          have pNotRest : p ∉ rest := by rw [same]; exact peNotRest
          have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions rest
            middle next executed
            (fun pe other s n he different =>
              executeIntegerProducerLineAtPE_peRegisters_other expressions s n pe other
                different he)
            p pNotRest
          refine ⟨writes, ?_⟩
          rw [tailFrame, same]
          exact headCommit
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          obtain ⟨writes, tailCommit⟩ := ih middle executed restNodup pMem
          have headFrame := executeIntegerProducerLineAtPE_peRegisters_other expressions state
            middle pe p same headExecuted
          exact ⟨writes, by rw [tailCommit, headFrame]⟩

/-- A plain integer-ALU row is never a float MAU producer. -/
theorem parsedExprIsPlainIntegerALU_notFloatMAU (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
          parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsSupportedFloatMAUProducer]

/-- A successful `.pe` step of a plain integer-ALU line commits a write list on
PE 0's register file. -/
theorem executeIntegerProducerInstructionLine_pe_peRegisters_commit
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (executed : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next executed
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
      normalizedExpressions state next accepted plain executed
  have filteredPlain : ((normalizedExpressions.map NormalizedExpr.toParsed).filter
      (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)).all
      parsedExprIsPlainIntegerALU = true :=
    List.all_eq_true.mpr fun expression member =>
      List.all_eq_true.mp plain expression (List.mem_filter.mp member).1
  have floatEmpty : ((normalizedExpressions.map NormalizedExpr.toParsed).filter
      (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)).filter
      parsedExprIsSupportedFloatMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      have rowPlain := List.all_eq_true.mp filteredPlain expression member
      rw [parsedExprIsPlainIntegerALU_notFloatMAU expression rowPlain]
      simp
  obtain ⟨writes, committed⟩ :=
    executeIntegerProducerLineAtPEs_peRegisters_commit _ (List.finRange 4096) state nextPEs
      floatEmpty walkExecuted (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  refine ⟨writes, ?_⟩
  rw [nextEq]
  simpa using committed

/-- A successful normalized `.pe` step of a plain integer-ALU line commits a
write list on PE 0's register file. -/
theorem executeNormalizedLine_pe_peRegisters_commit
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (executed : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  exact executeIntegerProducerInstructionLine_pe_peRegisters_commit
    normalizedExpressions state next plain executed

/-- **Write provenance at PE 0 for the plain integer-ALU subclass.** After a
successful `.pe` line whose rows are all plain integer ALUs, PE 0's register
file is the commit of the write list prepared by the executor, on the initial
file. This is `WelcomeWriteProvenance` on that subclass. -/
theorem welcomeWriteProvenance_of_plainIntegerALU (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    WelcomeWriteProvenance expressions := by
  intro input next step
  exact executeNormalizedLine_pe_peRegisters_commit expressions (welcomeInitialState input)
    next plain (welcomeSealed_step_ok step)

/-! ## 2. The `.double` block argument -/

/-- Arithmetic of the `.double` block hole: a 4-aligned block start never covers
a target word `t` with `t % 4 = 2` except at bus index 2. -/
theorem welcomeDistance_mod_four (address target : Nat)
    (addressLt : address < 4096) (addressAligned : address % 4 = 0)
    (targetMod : target % 4 = 2) :
    (target + 4096 - address) % 4096 % 4 = 2 := by
  have divisible : (4 : Nat) ∣ 4096 := by decide
  rw [Nat.mod_mod_of_dvd _ divisible]
  have expandAddress : address = 4 * (address / 4) := by
    have := Nat.div_add_mod address 4
    omega
  have expandTarget : target = 4 * (target / 4) + 2 := by
    have := Nat.div_add_mod target 4
    omega
  have bounded : address / 4 ≤ target / 4 + 1024 := by omega
  rw [expandAddress, expandTarget]
  have rearrange : 4 * (target / 4) + 2 + 4096 - 4 * (address / 4) =
      4 * (target / 4 + 1024 - address / 4) + 2 := by omega
  rw [rearrange, Nat.mul_add_mod]

/-- **The `.double` block hole.** If every `.lm1` destination among the committed
writes is a `.double` block at a 4-aligned address with a zero third data word,
then a target word with `target % 4 = 2` is untouched (or hit at bus index 2 with
a zero word), so it keeps its old value. -/
theorem commitParsedMaskedWrites_lm1_word_zero_of_double
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetMod : target.val % 4 = 2)
    (allDouble : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
        write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
        write.selection = selection → width = .double ∧ address.val % 4 = 0 ∧
          (∀ bound : 2 < 4, data ⟨2, bound⟩ = 0))
    (oldZero : files.lm1 target = 0) :
    (commitParsedMaskedWrites files writes).lm1 target = 0 := by
  apply commitParsedMaskedWrites_lm1_word_zero files writes target _ oldZero
  intro write mem width address data selection destination dataEq selectionEq
  obtain ⟨widthEq, aligned, dataTwo⟩ :=
    allDouble write mem width address data selection destination dataEq selectionEq
  subst widthEq
  have distanceMod : distance .lm1 address target % 4 = 2 := by
    have h := welcomeDistance_mod_four address.val target.val address.isLt aligned targetMod
    simpa [distance, Bank.capacity] using h
  by_cases atTwo : distance .lm1 address target = 2
  · exact Or.inr ⟨dataTwo, atTwo⟩
  · left
    show 4 ≤ distance .lm1 address target
    rcases Nat.lt_or_ge (distance .lm1 address target) 4 with small | large
    · rw [Nat.mod_eq_of_lt small] at distanceMod
      omega
    · exact large

/-- **The `.double` write shape at PE 0.** On the all-zero input, PE 0's register
file after the line is the commit of a write list in which every `.lm1`
destination is a `.double` block at a 4-aligned address with a zero third data
word. This is the shape the `.double` block argument needs; it is *not* proved
for the executor here (see `WelcomePEDoubleWriteShapeObligation`). -/
def WelcomePEDoubleWriteShape (expressions : List NormalizedExpr) : Prop :=
  ∀ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next →
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
      ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
          write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
          write.selection = selection → width = .double ∧ address.val % 4 = 0 ∧
            (∀ bound : 2 < 4, data ⟨2, bound⟩ = 0)

theorem welcomeZero_initial_lm1_two :
    ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE).lm1
      ⟨2, by decide⟩ = 0 := by
  show (welcomeInitialPERegisters welcomeZeroWords).lm1 ⟨2, by decide⟩ = 0
  rw [welcomeInitialPERegisters_lm1]

/-- **The `.double` case is closed.** A line whose all-zero PE 0 write list has
the `.double` shape is refuted: word 2 of PE 0 LM1 stays zero, while the
specification demands one there. -/
theorem welcome_not_correct_of_doubleWrites (expressions : List NormalizedExpr)
    (shape : WelcomePEDoubleWriteShape expressions) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      obtain ⟨writes, committed, allDouble⟩ := shape next step
      have wordZero : (next.peRegisters welcomePE).lm1 ⟨2, by decide⟩ = 0 := by
        rw [committed]
        exact commitParsedMaskedWrites_lm1_word_zero_of_double _ _ ⟨2, by decide⟩
          (by decide) allDouble welcomeZero_initial_lm1_two
      exact welcome_not_correct_of_word_zero (.pe expressions) next step
        ⟨2, by decide⟩ wordZero

/-- **Conditional bound from the `.double` shape.** If every residual line has
the `.double` write shape at PE 0, then the sealed Welcome machine has lower
bound two. -/
theorem welcomeLowerBound_two_of_residualDoubleShape
    (shape : ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
      WelcomePEDoubleWriteShape expressions) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_residual fun expressions residual =>
    welcome_not_correct_of_doubleWrites expressions (shape expressions residual)

/-! ## 3. The per-cycle write shape of a direct `.double` ALU row

The lemmas below are the per-expression half of `WelcomePEDoubleWriteShape`.
They show that the first branch of `prepareParsedIntegerALUExprCycle` — the
direct-memory-access branch — produces exactly one write, whose destination is
the lowered operand access and whose third data word comes from the low half of
the first operand, hence is zero whenever that read is zero.

What is *not* proved here is that a residual line's destinations really take this
branch for all four cycles (that needs `ParsedOperand.toDirectMemoryDestination?`
and the write-selection resolvers) and that no second LM1 writer exists
(`LegalParsedLine.writesUnique`). Those are the obligations at the end of the
file. -/

/-- The prepared-write equation for memory sources with arbitrary rounding
flags; `prepareParsedMaskedWriteWithForwarding_memory_eq_flush` is the special
case of two unrounded sources. -/
theorem prepareParsedMaskedWriteWithForwarding_memory_eq_flush_general
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (sourceXAccess sourceYAccess : DirectMemoryAccess) (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp)) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (parsedOutputAfterFlush accesses.flushSelection
              (IntegerALU.evaluateBus precision aluOp
                (ParsedIntegerInput.applyRounding roundedX
                  (pack (readDirectAccess files sourceXAccess)))
                (ParsedIntegerInput.applyRounding roundedY
                  (pack (readDirectAccess files sourceYAccess))) reduced).value)
            selection := accesses.writeSelection } := by
  unfold prepareParsedMaskedWriteWithForwarding
  rw [sourceX, sourceY]
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, request, evaluateParsedExecutionRequest]

/-- **The copy fact, generalized.** The third and fourth data words of a prepared
memory-sourced integer write are zero as soon as the *first* operand's read has a
zero low half: the low half of `evaluateBus` is copied from the first operand (or
zeroed), never computed, and the flush only applies an AND mask. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_three_zero_of_low_zero
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (sourceXAccess sourceYAccess : DirectMemoryAccess) (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (readX : (ParsedIntegerInput.applyRounding roundedX
      (pack (readDirectAccess files sourceXAccess))).low = 0)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write) :
    (∀ bound : 2 < 4, write.data ⟨2, bound⟩ = 0) ∧
      (∀ bound : 3 < 4, write.data ⟨3, bound⟩ = 0) := by
  rw [prepareParsedMaskedWriteWithForwarding_memory_eq_flush_general files slots cycle accesses
    reduced sourceXAccess sourceYAccess roundedX roundedY sourceX sourceY precision aluOp
    request] at prepared
  simp only [StepResult.ok.injEq] at prepared
  subst prepared
  have lowZero : (IntegerALU.evaluateBus precision aluOp
      (ParsedIntegerInput.applyRounding roundedX (pack (readDirectAccess files sourceXAccess)))
      (ParsedIntegerInput.applyRounding roundedY (pack (readDirectAccess files sourceYAccess)))
      reduced).value.low = 0 :=
    evaluateBus_value_low_zero precision aluOp _ _ reduced readX
  have flushed := parsedOutputAfterFlush_low_zero accesses.flushSelection _ lowZero
  exact ⟨fun bound => unpackALUBus_two_zero _ flushed bound,
    fun bound => unpackALUBus_three_zero _ flushed bound⟩

/-- On the all-zero input every memory read — rounded or not — has a zero low
half: an unrounded read is the zero bus, and a rounded read zeroes bus words 2
and 3. -/
theorem welcomeZero_applyRounding_pack_low_zero (access : DirectMemoryAccess)
    (rounded : Bool) :
    (ParsedIntegerInput.applyRounding rounded
      (pack (readDirectAccess (welcomeInitialPERegisters welcomeZeroWords) access))).low = 0 := by
  rw [welcomeZero_pack_readDirectAccess_zero]
  cases rounded with
  | false => rfl
  | true =>
      show (pack (roundSingleWordBusToHalf (unpackALUBus (⟨0, 0⟩ : IntegerALU.Bus)))).low = 0
      simp [pack, roundSingleWordBusToHalf, unpackALUBus]

/-- **One integer ALU cycle through the direct-access branch.** If the direct
masked lowering of the row at this cycle yields `accesses` and the prepared write
is `write`, the cycle returns exactly `[write]` (with whatever forwarding slots
the update yields). -/
theorem prepareParsedIntegerALUExprCycle_alu_direct
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced
      = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle = .ok ([write], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  dsimp only
  rw [operation]
  dsimp only
  rw [lowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- **The per-cycle `.double` shape.** A direct-access integer ALU cycle whose
lowered destination is an `.lm1` `.double` block prepares exactly one write to
that block, and — on a zero first read — with a zero third data word (the block
hole of `commitParsedMaskedWrites_lm1_word_zero_of_double`). -/
theorem prepareParsedIntegerALUExprCycle_alu_direct_double_zero
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (address : Fin Bank.lm1.capacity)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (sourceXAccess sourceYAccess : DirectMemoryAccess) (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (readX : (ParsedIntegerInput.applyRounding roundedX
      (pack (readDirectAccess files sourceXAccess))).low = 0)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (destination : accesses.destination = ⟨.lm1, .double, address⟩)
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced
      = .ok write) :
    ∃ slots,
      prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
          hasSingleLineMask noForward reduced cycle = .ok ([write], slots) ∧
      write.destination = some ⟨.lm1, .double, address⟩ ∧
      (∀ bound : 2 < 4, write.data ⟨2, bound⟩ = 0) := by
  obtain ⟨two, three⟩ :=
    prepareParsedMaskedWriteWithForwarding_data_two_three_zero_of_low_zero files oldSlots cycle
      accesses reduced write sourceXAccess sourceYAccess roundedX roundedY sourceX sourceY
      readX precision aluOp request prepared
  have destinationEq : write.destination = some ⟨.lm1, .double, address⟩ := by
    rw [prepareParsedMaskedWriteWithForwarding_memory_eq_flush_general files oldSlots cycle
      accesses reduced sourceXAccess sourceYAccess roundedX roundedY sourceX sourceY precision
      aluOp request] at prepared
    simp only [StepResult.ok.injEq] at prepared
    subst prepared
    rw [destination]
  have updated : ∃ slots,
      updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward = .ok slots := by
    cases noForward <;> simp [updateParsedIntegerALUForwardingCycle]
  obtain ⟨slots, updatedEq⟩ := updated
  exact ⟨slots,
    prepareParsedIntegerALUExprCycle_alu_direct files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle accesses write slots isAlu lowered prepared
      updatedEq,
    destinationEq, two⟩

/-! ## 5. The remaining obligations, one exact `Prop` per producer family

What is proved so far in this file is the *provenance* half of the `.pe` write
analysis: PE 0's register file is a commit of the executor's prepared writes
(for the plain integer-ALU subclass), and the `.double` block hole argument
turns an all-`.double` write list into a refuted line.

What is **not** proved is the *shape* half: that the prepared write list really
has the `.double` shape. That is the per-expression lowering analysis of
`prepareParsedIntegerALUExprCycle` (direct-access branch: proved above, but the
hypotheses that the lowering succeeds and that every destination is `.lm1`
`.double` are open), of `prepareParsedMatrixReadExprCycles`, of the MAU and
matrix-write stages, and of the L1BM/L2BM producers. Each obligation below is
the exact shape statement still missing for one producer family; none of them is
assumed anywhere in this module. -/

/-- Obligation (integer stage, all-`.double` write shape). For every residual
line whose rows are all plain integer ALUs, the all-zero PE 0 write list has the
`.double` shape of `WelcomePEDoubleWriteShape`. The per-cycle half is
`prepareParsedIntegerALUExprCycle_alu_direct_double_zero`; what is missing is
that every cycle actually takes that branch (the operand must lower through
`ParsedOperand.toDirectMemoryDestination?` to an `.lm1` `.double` access and the
write/flush selections must resolve) and that no second LM1 writer exists
(`LegalParsedLine.writesUnique`). -/
def WelcomePEPlainDoubleShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (non-plain rows, all-`.double` write shape). The counterpart of
`WelcomePEPlainDoubleShapeObligation` for lines that contain at least one row
outside the plain integer-ALU class: `.matrixRead`, a `.mau` family,
`.matrixWrite`, an L1BM producer or an L2BM producer. The missing analysis is the
write shape of `prepareParsedMatrixReadExprCycles`, `executeParsedFloatMAUsAtPE`,
`executeParsedMatrixMAUAndWrites`, `executeParsedL1ToPEProducers` and
`executeParsedL2BMProducers`; the per-cycle direct-access result above does not
apply to them because they bypass `prepareParsedIntegerALUExprCycle`. -/
def WelcomePEOtherDoubleShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    WelcomePEDoubleWriteShape expressions

/-- **Conditional bound from the two shape obligations.** If every residual line
is either all-plain or not, and satisfies the corresponding `.double` write
shape, then the sealed Welcome machine has lower bound two. -/
theorem welcomeLowerBound_two_of_twoShapeObligations
    (plain : WelcomePEPlainDoubleShapeObligation)
    (other : WelcomePEOtherDoubleShapeObligation) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  apply welcomeLowerBound_two_of_residual
  intro expressions residual
  by_cases allPlain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true
  · exact welcome_not_correct_of_doubleWrites expressions
      (plain expressions residual allPlain)
  · have notPlain : (expressions.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = false := by
      cases h : (expressions.map NormalizedExpr.toParsed).all
          parsedExprIsPlainIntegerALU <;> simp_all
    exact welcome_not_correct_of_doubleWrites expressions
      (other expressions residual notPlain)

/-! ### Per-family specialisations of the shape obligation

These are the same statement restricted by the producer predicate of each
family, so that each open family is named separately. The aggregate obligation
`WelcomePEOtherDoubleShapeObligation` is what
`welcomeLowerBound_two_of_twoShapeObligations` consumes; these `Prop`s record
which producer families that aggregate still contains. -/

/-- Obligation (`.matrixRead` family): the four-cycle matrix-read preparation
`prepareParsedMatrixReadExprCycles` writes `.double` LM1 blocks with a zero third
data word. Open: its destination is a matrix access, not a
`ParsedOperand.toDirectMemoryDestination?` lowering, so the direct-access cycle
lemma does not apply. -/
def WelcomePEMatrixReadDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixReadProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.mau` matrix family): the matrix MAU stage
(`executeParsedMatrixMAUAndWrites`) emits `.double` LM1 writes with a zero third
data word. Open. -/
def WelcomePEMatrixMAUDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixMAUProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.mau` float family): `executeParsedFloatMAUsAtPE` emits
`.double` LM1 writes whose third data word is zero on the zero input. Open: the
float MAU stage writes `registersWithFloat`, which the provenance lemmas of this
file exclude by `floatEmpty`. -/
def WelcomePEFloatMAUDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSupportedFloatMAUProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.matrixWrite` family): the D/F/G/H matrix-write stage emits
`.double` LM1 writes with a zero third data word. Open. -/
def WelcomePEMatrixWriteDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixWriteProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.l1bm` family, including `.distrib`): the L1BM-to-PE producer
stage emits `.double` LM1 writes with a zero third data word. Open. -/
def WelcomePEL1ToPEDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL1ToPEProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.l2bm` family): the L2BM producer stage emits `.double` LM1
writes with a zero third data word. Open. -/
def WelcomePEL2BMDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL2BMProducer = true →
    WelcomePEDoubleWriteShape expressions

/-- Obligation (`.word`/`.long` destinations). A residual line — one whose
all-zero step rewrites all sixteen PE 0 LM1 words — cannot contain a `.lm1`
`.word`/`.long` prepared write. One expression's four cycles cover at most eight
words, and `LegalParsedLine.writesUnique` (which every accepted line satisfies)
excludes a second LM1 writer, so some observed word would stay zero. This is the
complementary case to the `.double` hole: it is what makes the `.double` shape
obligations exhaustive. Open: neither `writesUnique` nor the per-expression word
count is connected to the executor here. -/
def WelcomePENarrowCoverageObligation : Prop :=
  ∀ (expressions : List NormalizedExpr) (next : State)
    (writes : List PreparedParsedMaskedWrite),
    WelcomePEResidual expressions →
    welcomeSealedMachine.step (.pe expressions) (welcomeInitialState welcomeZeroWords) = some next →
    next.peRegisters welcomePE =
      commitParsedMaskedWrites
        ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes →
    ¬ ∃ write ∈ writes, ∃ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
        (_data : WordBus) (_selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ ∧ width ≠ .double

/-- Obligation (constant rows are input-independent). A line consisting only of
`.zero` and `.immediate` rows produces the same PE 0 LM1 output for the all-zero
and all-five inputs: the execution request of those rows ignores both operand
buses (`Issue.zero_execution_ignores_inputs`,
`Issue.immediate_execution_ignores_inputs`), and the initial mask registers,
addresses and selections are input-independent. Open: the executor preparation
is not yet shown to factor through the operand buses. -/
def WelcomePEConstantInputIndependentObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      expression.op = .zero ∨ ∃ value sparse, expression.op = .immediate value sparse) →
    WelcomePEInputIndependent expressions

/-! ## 6. Optimality is conditional on the lower bound -/

/-- The Welcome answer has score two. -/
theorem welcomeAnswer_score :
    ProofsLean.score welcomeSealedMachine welcomeAnswer = 2 := by
  simp [welcomeAnswer, ProofsLean.score, welcomeSealedMachine, InstructionLine.cost]

/-- **`Optimal` from the lower bound.** `welcomeAnswer_correct` is already
proved; `Optimal` follows as soon as `LowerBound welcomeSealedMachine welcomeSpec
2` exists. This theorem does **not** prove the lower bound: it is exactly the
missing piece. -/
theorem welcomeAnswer_optimal_of_lowerBound
    (lower : ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer := by
  refine ⟨welcomeAnswer_correct, ?_⟩
  rw [welcomeAnswer_score]
  exact lower

end ProofsLean.MNCore
