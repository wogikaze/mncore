import ProofsLean.WelcomeReluBlockShape
import ProofsLean.WelcomeLm1Frame

/-! # Corrected relu/block-float shapes at PE 0 and the `.lm1` frames

`WelcomeReluBlockShape.lean` (round 38) refuted the arbitrary-PE
`WelcomePEFloatReluZeroReadCopy` and showed that `WelcomePEBlockFloatMabShape`
needs the third-word copy of the block-float output bus as a hypothesis.  This
module supplies the corrected statements that the observed PE actually needs,
and then attacks the two `.lm1` frames of `WelcomeAssembly.lean` that the
line-level argument consumes.

## What is proved here

1. **The corrected relu read-copy fact** (§1).  At PE 0 with the zero-state
   context — the context the float-relu executor itself builds from
   `readState.peContext welcomePE` and `ofLinearIndex welcomePE` —
   every successful read of the lowered first source has a copied high word.
   The proof destructures `expression.op` / `expression.sources` out of the
   lowering `do` block (`lowerParsedFloatRelu?_sourceA_lowering`) and then
   applies the `WelcomePlainStep` read-copy lemma
   `welcomeZero_toParsedIntegerInput_read_copy`.  This is
   `welcomePEFloatReluZeroReadCopy_at_welcomePE`.

2. **The corrected block-float shapes** (§2).  Two `Prop`s in exactly the
   shape of the original `WelcomePEBlockFloatMabShape`:
   `WelcomePEBlockFloatMabShapeOfBusCopy` adds the third-word copy of the row's
   output bus as an explicit hypothesis, and
   `WelcomePEBlockFloatMabShapeLowPrecision` restricts the precision to
   `.d`/`.f`/`.g`, where that copy is automatic.  Both are proved as `Prop`s, so
   downstream code switches by changing one name.

3. **The `.lm1` frames** (§3).  `WelcomePEIntegerStageLm1Frame` is discharged
   *with the corrected hypothesis*: besides the integer-stage rows, the
   float-MAU rows (whose writes happen inside the same stage) must also avoid
   bank `.lm1` (`WelcomePEIntegerStageLm1FrameCorrected`).  The MSL/MSR,
   float-relu and block-float stage frames of `WelcomePEStageLm1Frame` are then
   proved unconditionally from `WelcomeRowHasNoLm1Destination`, each by the
   loop induction of its executor (`writeDestinations`, `runCycles`, the
   per-PE walk and the family filter).  The matrix-MAU/write and L1BM-to-PE
   conjuncts are reduced to the named residuals
   `WelcomePEMatrixMAUStageLm1Frame` and `WelcomePEL1ToPEStageLm1Frame`, which
   are stated exactly at the interface of the two remaining executors, so
   `welcomePEStageLm1Frame_of_residuals` yields the full
   `WelcomePEStageLm1Frame` from those two facts alone.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing here claims
`LowerBound 2`, `Optimal`, or any line-level shape.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 0. The zero-state control context at PE 0 -/

/-- The hazard-control context of PE 0 at the all-zero state is exactly the
linear-index context, so `welcomeFixedValue` applies to it. -/
theorem welcomeZeroControl_context_eq :
    welcomeZeroControl.context = ParsedIntegerContext.ofLinearIndex welcomePE := rfl

/-- The context the float-relu executor builds at the all-zero state and PE 0 is
the context of `WelcomePEFloatReluZeroReadCopyAtWelcomePE` with the cycle
overridden. -/
theorem welcomeZero_sourceContext (cycle : Fin 4) :
    { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
          bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
          bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
          tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
        ParsedIntegerContext) with cycle := cycle } =
      { ParsedIntegerContext.ofLinearIndex welcomePE with cycle := cycle } := rfl

/-! ## 1. The float-relu lowering exposes its first source
`WelcomePEFloatReluZeroReadCopy` at PE 0 -/

/-- **The first lowered source of a float-relu row.**  A successful
`lowerParsedFloatRelu?` comes from an `.alu` row with one or two source
operands, and its first source is the `ParsedOperand.toParsedIntegerInput?`
lowering of one of the row's source operands.  This is the step the round-38
analysis was missing: the lowering `do` block has to be destructured before the
read-copy lemma applies. -/
theorem lowerParsedFloatRelu?_sourceA_lowering
    (expression : ParsedExpr) (context : ParsedIntegerContext)
    (accesses : ParsedFloatReluAccesses)
    (lowered : lowerParsedFloatRelu? expression context = some accesses) :
    ∃ (operand : ParsedOperand) (laneWidth : IntegerALU.Precision),
      ParsedOperand.toParsedIntegerInput? operand laneWidth context.group context.l2b
        context.l1b context.mab context.pe context.cycle context.bar0 context.bar1
        context.tWord = some accesses.sourceA := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [lowerParsedFloatRelu?] at lowered
      | some parsedPrecision =>
          cases sources with
          | nil => simp [lowerParsedFloatRelu?] at lowered
          | cons first rest =>
              cases destinations with
              | nil => simp [lowerParsedFloatRelu?] at lowered
              | cons destination tail =>
                  simp only [lowerParsedFloatRelu?, Bind.bind, Option.bind, guard] at lowered
                  repeat' (first | split at lowered | simp_all)
                  all_goals (try (subst accesses; exact ⟨_, _, by assumption⟩))
  | zero => simp [lowerParsedFloatRelu?] at lowered
  | immediate payload sparse => simp [lowerParsedFloatRelu?] at lowered
  | mau precision matrix kind half round => simp [lowerParsedFloatRelu?] at lowered
  | matrixWrite precision => simp [lowerParsedFloatRelu?] at lowered
  | matrixRead precision => simp [lowerParsedFloatRelu?] at lowered
  | wait tag => simp [lowerParsedFloatRelu?] at lowered
  | noforward => simp [lowerParsedFloatRelu?] at lowered
  | l1bm operation => simp [lowerParsedFloatRelu?] at lowered
  | l2bm operation => simp [lowerParsedFloatRelu?] at lowered

/-- **The corrected float-relu zero-read Prop.**  This is
`WelcomePEFloatReluZeroReadCopy` with the PE fixed to the observed PE `0` and
the lowering context fixed to the zero-state context — exactly the data the
`executeParsedFloatReluAtPE` row itself uses.  The unrestricted version is false
(`not_welcomePEFloatReluZeroReadCopy`); this one is proved below. -/
def WelcomePEFloatReluZeroReadCopyAtWelcomePE : Prop :=
  ∀ (cycle : Fin 4) (expression : ParsedExpr) (accesses : ParsedFloatReluAccesses),
    lowerParsedFloatRelu? expression
      { ParsedIntegerContext.ofLinearIndex welcomePE with cycle := cycle } = some accesses →
    ∀ sourceA : IntegerALU.Bus,
      ParsedIntegerInput.readWithForwarding
        ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
        (stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE) cycle
        accesses.sourceA = .ok sourceA →
      IsWelcomeCopy (sourceA.low.extractLsb' 32 32)

/-- **`WelcomePEFloatReluZeroReadCopyAtWelcomePE`.** -/
theorem welcomePEFloatReluZeroReadCopy_at_welcomePE :
    WelcomePEFloatReluZeroReadCopyAtWelcomePE := by
  intro cycle expression accesses lowered sourceA read
  have contextEq : { ParsedIntegerContext.ofLinearIndex welcomePE with cycle := cycle } =
      { welcomeZeroControl.context with cycle := cycle } := by
    rw [welcomeZeroControl_context_eq]
  rw [contextEq] at lowered
  obtain ⟨operand, laneWidth, sourceLowered⟩ :=
    lowerParsedFloatRelu?_sourceA_lowering expression _ accesses lowered
  exact welcomeZero_toParsedIntegerInput_read_copy operand laneWidth cycle accesses.sourceA
    sourceLowered sourceA read

/-- **The read-copy fact in the exact context of `executeParsedFloatReluAtPE`.**
At the all-zero state and PE 0 the executor lowers with
`{sourceContext with cycle := cycle}`, where `sourceContext` is built from
`readState.peContext welcomePE`; this is the context of the corrected Prop. -/
theorem welcomeZero_executeParsedFloatRelu_read_copy
    (cycle : Fin 4) (expression : ParsedExpr) (accesses : ParsedFloatReluAccesses)
    (lowered : lowerParsedFloatRelu? expression
      { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
          bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
          bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
          tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
        ParsedIntegerContext) with cycle := cycle } = some accesses)
    (sourceA : IntegerALU.Bus)
    (read : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
      (stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE) cycle
      accesses.sourceA = .ok sourceA) :
    IsWelcomeCopy (sourceA.low.extractLsb' 32 32) := by
  rw [welcomeZero_sourceContext] at lowered
  exact welcomePEFloatReluZeroReadCopy_at_welcomePE cycle expression accesses lowered sourceA read

/-! ## 2. The block-float shapes, restated with their real hypothesis

The original `WelcomePEBlockFloatMabShape` is not provable: for `.h` precision
the third bus word is not a copy (`parsedBlockFloatMab_h_third_word_not_copy`).
The two `Prop`s below have exactly the quantification and conclusion of the
original, differing only in the added hypothesis.  Downstream code that assumed
`WelcomePEBlockFloatMabShape` switches by changing one name. -/

/-- **The block-float coordinate shape with the output-bus copy hypothesis.** -/
def WelcomePEBlockFloatMabShapeOfBusCopy : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width),
    lowerParsedBlockFloat? expression = some accesses →
    (∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w) →
    (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 →
    (∀ (buses : Fin 4 → IntegerALU.Bus) (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
        accesses.extended buses pe)) ⟨2, bound⟩)) →
    executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next →
    ∀ pe : Fin 4,
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters (physicalPEId coordinate pe) =
          commitParsedMaskedWrites
            (currentState.peRegisters (physicalPEId coordinate pe)) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

/-- **`WelcomePEBlockFloatMabShapeOfBusCopy`.** -/
theorem welcomePEBlockFloatMabShape_of_busCopy_hyp :
    WelcomePEBlockFloatMabShapeOfBusCopy :=
  fun readState currentState expression coordinate noForward hasSingleLineMask next accesses w
    lowered staticWidth countBound busCopy executed pe =>
    welcomePEBlockFloatMabShape_of_busCopy readState currentState expression coordinate
      noForward hasSingleLineMask next accesses w lowered staticWidth countBound busCopy
      executed pe

/-- **The block-float coordinate shape for the precisions whose low half is
zero.**  Same shape as the original, with `.d`/`.f`/`.g` as the only allowed
precisions.  This is the unconditional form the observed rows need. -/
def WelcomePEBlockFloatMabShapeLowPrecision : Prop :=
  ∀ (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width),
    lowerParsedBlockFloat? expression = some accesses →
    (accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g) →
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

/-- **`WelcomePEBlockFloatMabShapeLowPrecision`.** -/
theorem welcomePEBlockFloatMabShape_lowPrecision :
    WelcomePEBlockFloatMabShapeLowPrecision :=
  fun readState currentState expression coordinate noForward hasSingleLineMask next accesses w
    lowered lowPrecision staticWidth countBound executed pe =>
    welcomePEBlockFloatMabShape_of_precision_low_zero readState currentState expression
      coordinate noForward hasSingleLineMask next accesses w lowered staticWidth countBound
      lowPrecision executed pe

/-! ## 3. The `.lm1` frames

The frames are "the `.lm1` bank of PE 0 is unchanged".  Each stage executor is a
chain of loops; at every write the shared single-destination writer
`writeParsedMslMsrDestination?` is applied, and
`writeParsedMslMsrDestination?_lm1_of_ne` (`WelcomeAssembly.lean` §9) says that a
destination whose static bank is not `.lm1` leaves the bank alone.  The lemmas
below are the loop inductions that carry that fact through the folds. -/

/-- A commit of `.lm1`-free prepared writes preserves the `.lm1` bank. -/
theorem commitParsedMaskedWrites_lm1_frame (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite)
    (noLm1 : ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false) :
    (commitParsedMaskedWrites files writes).lm1 = files.lm1 :=
  commitParsedMaskedWrites_lm1_of_no_lm1 writes files
    (fun write member access haccess =>
      isLm1Write_false_bank write (noLm1 write member) access haccess)

/-! ### 3.1 The float-MAU write lists are `.lm1`-free -/

theorem writeParsedMAUDestinations?_writeAll_lm1_free
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (next : ParsedMAUDestinationWrites),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      writeParsedMAUDestinations?.writeAll context output flags cycle directive hasSingleLineMask
        destinations files bar0 bar1 = some next →
      next.files.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 next noLm1 executed
      rw [writeParsedMAUDestinations?.writeAll.eq_1] at executed
      obtain rfl := Option.some.inj executed
      rfl
  | cons destination rest ih =>
      intro files bar0 bar1 next noLm1 executed
      rw [writeParsedMAUDestinations?.writeAll.eq_2] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have headFrame := writeParsedMslMsrDestination?_lm1_of_ne files destination
            { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
            hasSingleLineMask
            (fun bank width pair bankEq =>
              noLm1 destination (by simp) bank width pair bankEq) write lowered
          have tailFrame := ih write.files
            (match write.barUpdate with
              | some (false, value) => value
              | _ => bar0)
            (match write.barUpdate with
              | some (true, value) => value
              | _ => bar1)
            next (fun item member bank width pair bankEq =>
              noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq) executed
          rw [tailFrame, headFrame]

theorem writeParsedMAUDestinations?_lm1_free
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (next : ParsedMAUDestinationWrites),
      writeParsedMAUDestinations? files destinations context output flags cycle directive
        hasSingleLineMask = some next →
      next.files.lm1 = files.lm1 := by
  intro next executed
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_lm1_free context output flags cycle directive
    hasSingleLineMask destinations files context.bar0 context.bar1 next noLm1 executed

theorem executeParsedFloatMAUCyclesAtPE_lm1_free
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
          .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      nextFiles.lm1 = files.lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_2] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i ignored output flags ranCycle
        split at executed
        · simp at executed
        · rename_i flushSelection
          split at executed
          · simp at executed
          · rename_i writes wrote
            have writesFrame := writeParsedMAUDestinations?_lm1_free files
              expression.destinations
              { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } _ flags cycle
              directive hasSingleLineMask noLm1 writes wrote
            rw [ih writes.files writes.bar0 writes.bar1 _ nextFiles nextBar0 nextBar1
              nextOutputs executed]
            exact writesFrame

theorem executeParsedFloatMAUsAtPE_run_lm1_free
    (readState : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (remaining : List ParsedExpr),
      (∀ expression ∈ remaining, ∀ destination ∈ expression.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
        (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
        (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
        executeParsedFloatMAUsAtPE.run readState oldSlots context directive hasSingleLineMask
          remaining files bar0 bar1 outputs = .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
        nextFiles.lm1 = files.lm1 := by
  intro remaining
  induction remaining with
  | nil =>
      intro noLm1 files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons expression rest ih =>
      intro noLm1 files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run.eq_2] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middleFiles middleBar0 middleBar1 middleOutputs ran
        have cycleFrame := executeParsedFloatMAUCyclesAtPE_lm1_free readState oldSlots expression
          context directive hasSingleLineMask
          (fun destination member bank width pair bankEq =>
            noLm1 expression (by simp) destination member bank width pair bankEq)
          [0, 1, 2, 3] files bar0 bar1 _ middleFiles middleBar0 middleBar1 middleOutputs ran
        rw [ih (fun other member destination destMem bank width pair bankEq =>
          noLm1 other (List.mem_cons_of_mem _ member) destination destMem bank width pair bankEq)
          middleFiles middleBar0 middleBar1 middleOutputs nextFiles nextBar0 nextBar1
          nextOutputs executed]
        exact cycleFrame

theorem executeParsedFloatMAUsAtPE_lm1_free
    (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      ∀ destination ∈ expression.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) :
    ∀ (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
      (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool),
      executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions directive
        hasSingleLineMask = .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer) →
      nextFiles.lm1 = currentFiles.lm1 := by
  intro nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  cases ran : executeParsedFloatMAUsAtPE.run readState oldSlots context directive
      hasSingleLineMask (List.filter parsedExprIsSupportedFloatMAUProducer expressions)
      currentFiles context.bar0 context.bar1 (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok result =>
      obtain ⟨files, bar0, bar1, outputs⟩ := result
      rw [ran] at executed
      simp only [StepResult.ok.injEq] at executed
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := executed
      exact executeParsedFloatMAUsAtPE_run_lm1_free readState oldSlots context directive
        hasSingleLineMask _ noLm1 currentFiles context.bar0 context.bar1 _ nextFiles
        nextBar0 nextBar1 nextOutputs ran

/-! ### 3.2 The integer-stage `.lm1` frame, with the float-MAU hypothesis -/

/-- The four-cycle integer preparation is a commit of `.lm1`-free writes when its
rows avoid bank `.lm1`. -/
theorem parsedIntegerMatrixReadLineFourCycleStep_lm1_free
    (files : IntegerRegisterFiles) (slots : Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) (reduced : Bool)
    (registers : IntegerRegisterFiles) (nextSlots : Forwarding.Slots)
    (barUpdates : List (Bool × BitVec 12))
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : parsedIntegerMatrixReadLineFourCycleStep files slots store expressions control
      reduced = .ok (registers, nextSlots, barUpdates)) :
    ∃ writes, registers = commitParsedMaskedWrites files writes ∧
      ∀ write ∈ writes, ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = false := by
  rw [parsedIntegerMatrixReadLineFourCycleStep.eq_1] at executed
  cases prepared : prepareParsedIntegerMatrixReadLineCycles files slots store expressions
      control reduced with
  | failure =>
      rw [prepared] at executed
      simp at executed
  | unknown =>
      rw [prepared] at executed
      simp at executed
  | ok result =>
      obtain ⟨writes, preparedSlots, preparedBars⟩ := result
      rw [prepared] at executed
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      exact ⟨writes, rfl,
        prepareParsedIntegerMatrixReadLineCycles_lm1_free files slots store expressions control
          reduced noLm1 writes preparedSlots preparedBars prepared⟩

/-- The per-PE integer core preserves the visited PE's `.lm1` bank when both its
integer rows and its float-MAU rows avoid bank `.lm1`. -/
theorem executeIntegerProducerLineAtPECore_lm1_free
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (intNoLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression)
    (floatNoLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    (next.peRegisters pe).lm1 = (state.peRegisters pe).lm1 := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    split at executed
    · simp at executed
    · simp at executed
    · rename_i registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
      simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        have integerFrame : registers.lm1 = (state.peRegisters pe).lm1 := by
          obtain ⟨intWrites, intCommit, intFree⟩ :=
            parsedIntegerMatrixReadLineFourCycleStep_lm1_free (state.peRegisters pe)
              (stateForwardingSlots state pe) _ _ (parsedPEHazardControl state pe) false
              registers integerSlots barUpdates intNoLm1 fourCycle
          rw [intCommit]
          exact commitParsedMaskedWrites_lm1_frame _ _ intFree
        have floatFrame : registersWithFloat.lm1 = registers.lm1 := by
          exact executeParsedFloatMAUsAtPE_lm1_free (state.peRegisters pe) registers
            (stateForwardingSlots state pe) _ expressions state.maskDirective
            (expressions.any parsedExprHasSingleLineWriteMask) floatNoLm1 _ _ _ _
            hasMAUProducer floatMAU
        dsimp only
        rw [ite_eq_left rfl, floatFrame, integerFrame]

/-- The per-PE integer step (`executeIntegerProducerLineAtPE`) preserves the
visited PE's `.lm1` bank under the two no-`.lm1` hypotheses. -/
theorem executeIntegerProducerLineAtPE_lm1_free
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (intNoLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression)
    (floatNoLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    (next.peRegisters pe).lm1 = (state.peRegisters pe).lm1 := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_lm1_free expressions state next pe intNoLm1
      floatNoLm1 executed

/-- The walk of the integer stage preserves PE 0's `.lm1` bank under the two
no-`.lm1` hypotheses.  No `Nodup` condition is needed: every step either visits
another PE (and frames PE 0) or is the visited PE (and preserves the bank). -/
theorem executeIntegerProducerLineAtPEs_lm1_frame
    (expressions : List ParsedExpr) :
    ∀ (pes : List PEId) (state next : State),
      (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
        WelcomeRowHasNoLm1Destination expression) →
      (∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeIntegerProducerLineAtPEs expressions pes state = .ok next →
      (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro state next intNoLm1 floatNoLm1 executed
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next intNoLm1 floatNoLm1 executed
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : pe = welcomePE
        · have headFrame : (middle.peRegisters welcomePE).lm1 =
              (state.peRegisters welcomePE).lm1 := by
            rw [← same]
            exact executeIntegerProducerLineAtPE_lm1_free expressions state middle pe
              intNoLm1 floatNoLm1 headExecuted
          rw [ih middle next intNoLm1 floatNoLm1 executed, headFrame]
        · have headFrame : middle.peRegisters welcomePE = state.peRegisters welcomePE :=
            executeIntegerProducerLineAtPE_peRegisters_other expressions state middle pe
              welcomePE (Ne.symm same) headExecuted
          rw [ih middle next intNoLm1 floatNoLm1 executed, headFrame]

/-- **The corrected integer-stage `.lm1` frame.**  This is
`WelcomePEIntegerStageLm1Frame` with the extra hypothesis the previous round
identified: the rows that `executeParsedFloatMAUsAtPE` executes *inside* this
stage must avoid bank `.lm1` as well.  With only the integer-stage-row
hypothesis the statement is not derivable, because the float-MAU writes are part
of the same stage. -/
def WelcomePEIntegerStageLm1FrameCorrected : Prop :=
  ∀ (expressions : List ParsedExpr) (pes : List PEId) (state next : State),
    pes.Nodup → welcomePE ∈ pes →
    (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) →
    (∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression) →
    executeIntegerProducerLineAtPEs expressions pes state = .ok next →
    (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1

/-- **`WelcomePEIntegerStageLm1FrameCorrected`.** -/
theorem welcomePEIntegerStageLm1Frame_corrected :
    WelcomePEIntegerStageLm1FrameCorrected :=
  fun expressions pes state next _nodup _mem intNoLm1 floatNoLm1 executed =>
    executeIntegerProducerLineAtPEs_lm1_frame expressions pes state next intNoLm1
      floatNoLm1 executed

/-! ### 3.3 The MSL/MSR stage -/

/-- The destination list of an MSL/MSR lowering is the row's destination list. -/
theorem lowerParsedMslMsr?_destinations (expression : ParsedExpr) (isMsl : Bool)
    (destinations : List ParsedOperand)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations)) :
    destinations = expression.destinations := by
  obtain ⟨op, sources, ds, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none =>
          simp only [lowerParsedMslMsr?, Bind.bind, Option.bind, guard] at lowered
          repeat' (first | split at lowered | simp_all)
      | some parsedPrecision => simp [lowerParsedMslMsr?] at lowered
  | zero => simp [lowerParsedMslMsr?] at lowered
  | immediate payload sparse => simp [lowerParsedMslMsr?] at lowered
  | mau precision matrix kind half round => simp [lowerParsedMslMsr?] at lowered
  | matrixWrite precision => simp [lowerParsedMslMsr?] at lowered
  | matrixRead precision => simp [lowerParsedMslMsr?] at lowered
  | wait tag => simp [lowerParsedMslMsr?] at lowered
  | noforward => simp [lowerParsedMslMsr?] at lowered
  | l1bm operation => simp [lowerParsedMslMsr?] at lowered
  | l2bm operation => simp [lowerParsedMslMsr?] at lowered

theorem executeParsedMslMsrAtPE_writeDestinations_lm1_free
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        context cycle output destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      rfl
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have headFrame := writeParsedMslMsrDestination?_lm1_of_ne files destination
            { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
            currentState.maskDirective hasSingleLineMask
            (fun bank width pair bankEq =>
              noLm1 destination (by simp) bank width pair bankEq) write lowered
          have tailFrame := ih write.files
            (match write.barUpdate with
              | some (false, value) => value
              | _ => bar0)
            (match write.barUpdate with
              | some (true, value) => value
              | _ => bar1)
            nextFiles nextBar0 nextBar1
            (fun item member bank width pair bankEq =>
              noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq)
            executed
          rw [tailFrame, headFrame]

theorem executeParsedMslMsrAtPE_runCycles_lm1_free
    (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (sourcePE : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput)
    (noLm1 : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (registers : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations sourcePE sourceAt cycles files bar0 bar1 outputs =
          .ok (registers, nextBar0, nextBar1, nextOutputs) →
      registers.lm1 = files.lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs registers nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs registers nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      dsimp only at executed
      cases source : sourceAt cycle with
      | none =>
          rw [source] at executed
          dsimp only at executed
          simp at executed
      | some item =>
          rw [source] at executed
          dsimp only at executed
          cases read : ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
              (stateForwardingSlots readState sourcePE) cycle item with
          | failure =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | ok sourceBus =>
              rw [read] at executed
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
                    have headFrame := executeParsedMslMsrAtPE_writeDestinations_lm1_free
                      currentState hasSingleLineMask context cycle _ destinations files bar0 bar1
                      middleFiles middleBar0 middleBar1 noLm1 wrote
                    rw [ih middleFiles middleBar0 middleBar1 _ registers nextBar0 nextBar1
                      nextOutputs executed]
                    exact headFrame

theorem executeParsedMslMsrAtPE_lm1_frame
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters pe).lm1 = (currentState.peRegisters pe).lm1 := by
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  cases lowered : lowerParsedMslMsr? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      obtain ⟨isMsl, destinations⟩ := accesses
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i registers bar0 bar1 outputs ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        subst executed
        have destinationsEq : destinations = expression.destinations :=
          lowerParsedMslMsr?_destinations expression isMsl destinations lowered
        have destinationsNoLm1 : ∀ destination ∈ destinations,
            ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
              ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
                bank ≠ PEMemory.Bank.lm1 := by
          intro destination member bank width pair bankEq
          exact noLm1 destination (destinationsEq ▸ member) bank width pair bankEq
        have frame := executeParsedMslMsrAtPE_runCycles_lm1_free readState currentState
          expression hasSingleLineMask _ destinations _ _ destinationsNoLm1
          [0, 1, 2, 3] (currentState.peRegisters pe) _ _ _ registers bar0 bar1 outputs ran
        simpa using frame

theorem executeParsedMslMsrAtPEs_lm1_frame
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (pes : List PEId) (state next : State),
      executeParsedMslMsrAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro state next executed
      simp only [executeParsedMslMsrAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next executed
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : pe = welcomePE
        · have headFrame : (middle.peRegisters welcomePE).lm1 =
              (state.peRegisters welcomePE).lm1 := by
            rw [← same]
            exact executeParsedMslMsrAtPE_lm1_frame readState state middle expression pe
              noForward hasSingleLineMask noLm1 headExecuted
          rw [ih middle next executed, headFrame]
        · have headFrame : middle.peRegisters welcomePE = state.peRegisters welcomePE :=
            executeParsedMslMsrAtPE_peRegisters_other readState state middle expression pe
              welcomePE (Ne.symm same) noForward hasSingleLineMask headExecuted
          rw [ih middle next executed, headFrame]

theorem executeParsedMslMsrProducers_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedMslMsrProducers.eq_1] at executed
  cases filtered : List.filter parsedExprIsMslMsrProducer expressions with
  | nil =>
      rw [filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [filtered] at executed
          exact executeParsedMslMsrAtPEs_lm1_frame readState expression noForward
            hasSingleLineMask
            (noLm1 expression (List.mem_filter.mp (by rw [filtered]; simp)).1)
            (List.finRange 4096) currentState next executed
      | cons second remaining =>
          rw [filtered] at executed
          simp at executed

/-! ### 3.4 The float-relu stage -/

/-- The destination list of a float-relu lowering is the row's destination list. -/
theorem lowerParsedFloatRelu?_destinations (expression : ParsedExpr)
    (context : ParsedIntegerContext) (accesses : ParsedFloatReluAccesses)
    (lowered : lowerParsedFloatRelu? expression context = some accesses) :
    accesses.destinations = expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [lowerParsedFloatRelu?] at lowered
      | some parsedPrecision =>
          cases sources with
          | nil => simp [lowerParsedFloatRelu?] at lowered
          | cons first rest =>
              cases rest with
              | nil =>
                  cases destinations with
                  | nil => simp [lowerParsedFloatRelu?] at lowered
                  | cons destination tail =>
                      simp only [lowerParsedFloatRelu?, Bind.bind] at lowered
                      repeat' (
                        first
                        | rw [Option.bind_eq_some_iff] at lowered
                        | simp only [Option.some.injEq] at lowered
                        | simp_all
                        | rcases lowered with ⟨_, _, lowered⟩)
              | cons second tailSources =>
                  cases tailSources with
                  | nil =>
                      cases destinations with
                      | nil => simp [lowerParsedFloatRelu?] at lowered
                      | cons destination tail =>
                          simp only [lowerParsedFloatRelu?, Bind.bind] at lowered
                          repeat' (
                            first
                            | rw [Option.bind_eq_some_iff] at lowered
                            | simp only [Option.some.injEq] at lowered
                            | simp_all
                            | rcases lowered with ⟨_, _, lowered⟩)
                  | cons third more => simp [lowerParsedFloatRelu?] at lowered
  | zero => simp [lowerParsedFloatRelu?] at lowered
  | immediate payload sparse => simp [lowerParsedFloatRelu?] at lowered
  | mau precision matrix kind half round => simp [lowerParsedFloatRelu?] at lowered
  | matrixWrite precision => simp [lowerParsedFloatRelu?] at lowered
  | matrixRead precision => simp [lowerParsedFloatRelu?] at lowered
  | wait tag => simp [lowerParsedFloatRelu?] at lowered
  | noforward => simp [lowerParsedFloatRelu?] at lowered
  | l1bm operation => simp [lowerParsedFloatRelu?] at lowered
  | l2bm operation => simp [lowerParsedFloatRelu?] at lowered

theorem executeParsedFloatReluAtPE_writeDestinations_lm1_free
    (currentState : State) (hasSingleLineMask : Bool) (coordinates : ParsedIntegerContext)
    (cycle : Fin 4) (flags : BitVec 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedFloatReluAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        coordinates cycle flags output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      rfl
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have headFrame := writeParsedMslMsrDestination?_lm1_of_ne files destination
            { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
            currentState.maskDirective hasSingleLineMask
            (fun bank width pair bankEq =>
              noLm1 destination (by simp) bank width pair bankEq) write lowered
          have tailFrame := ih write.files
            (match write.barUpdate with
              | some (false, value) => value
              | _ => bar0)
            (match write.barUpdate with
              | some (true, value) => value
              | _ => bar1)
            nextFiles nextBar0 nextBar1
            (fun item member bank width pair bankEq =>
              noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq)
            executed
          rw [tailFrame, headFrame]

theorem executeParsedFloatReluAtPE_runCycles_lm1_free
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext)
    (noLm1 : ∀ destination ∈ expression.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask coordinates sourceContext cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      nextFiles.lm1 = files.lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
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
          obtain ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩ :=
            accesses
          have destinationsNoLm1 : ∀ destination ∈ destinations,
              ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
                ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
                  bank ≠ PEMemory.Bank.lm1 := by
            intro destination member bank width pair bankEq
            have eq := lowerParsedFloatRelu?_destinations expression
              { sourceContext with cycle := cycle }
              ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩ lower
            exact noLm1 destination (by rw [← eq]; exact member) bank width pair bankEq
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
                        have headFrame :=
                          executeParsedFloatReluAtPE_writeDestinations_lm1_free currentState
                            hasSingleLineMask coordinates cycle _ _ destinations files bar0 bar1
                            middleFiles middleBar0 middleBar1 destinationsNoLm1 wrote
                        rw [ih middleFiles middleBar0 middleBar1 _ nextFiles nextBar0 nextBar1
                          nextOutputs executed]
                        exact headFrame
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
                            have headFrame :=
                              executeParsedFloatReluAtPE_writeDestinations_lm1_free currentState
                                hasSingleLineMask coordinates cycle _ _ destinations files bar0 bar1
                                middleFiles middleBar0 middleBar1 destinationsNoLm1 wrote
                            rw [ih middleFiles middleBar0 middleBar1 _ nextFiles nextBar0 nextBar1
                              nextOutputs executed]
                            exact headFrame

theorem executeParsedFloatReluAtPE_lm1_frame
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters pe).lm1 = (currentState.peRegisters pe).lm1 := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    subst executed
    have frame := executeParsedFloatReluAtPE_runCycles_lm1_free readState currentState
      expression pe hasSingleLineMask _ _ noLm1 [0, 1, 2, 3] (currentState.peRegisters pe) _ _
      _ registers bar0 bar1 outputs ran
    simpa using frame

theorem executeParsedFloatReluAtPEs_lm1_frame
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (pes : List PEId) (state next : State),
      executeParsedFloatReluAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro state next executed
      simp only [executeParsedFloatReluAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next executed
      simp only [executeParsedFloatReluAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : pe = welcomePE
        · have headFrame : (middle.peRegisters welcomePE).lm1 =
              (state.peRegisters welcomePE).lm1 := by
            rw [← same]
            exact executeParsedFloatReluAtPE_lm1_frame readState state middle expression pe
              noForward hasSingleLineMask noLm1 headExecuted
          rw [ih middle next executed, headFrame]
        · have headFrame : middle.peRegisters welcomePE = state.peRegisters welcomePE :=
            executeParsedFloatReluAtPE_peRegisters_other readState state middle expression pe
              welcomePE (Ne.symm same) noForward hasSingleLineMask headExecuted
          rw [ih middle next executed, headFrame]

theorem executeParsedFloatReluProducers_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedFloatReluProducers.eq_1] at executed
  cases filtered : List.filter parsedExprIsFloatReluProducer expressions with
  | nil =>
      rw [filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [filtered] at executed
          exact executeParsedFloatReluAtPEs_lm1_frame readState expression noForward
            hasSingleLineMask
            (noLm1 expression (List.mem_filter.mp (by rw [filtered]; simp)).1)
            (List.finRange 4096) currentState next executed
      | cons second remaining =>
          rw [filtered] at executed
          simp at executed

/-! ### 3.5 The block-float stage

The block-float row writes through the same single-destination writer inside a
four-cycle, four-PE fold, and then installs the four register files with
`List.finRange 4` fold.  The frame lemmas below are the verbatim `.lm1`
analogues of the commit lemmas of `WelcomeStageCommit.lean` §6, with the fold
lemmas `blockFloatFoldl_peRegisters_target` / `..._frame` of
`WelcomeReluBlockShape.lean` extracting PE 0 from the installation fold. -/

theorem physicalPEId_zero_zero : physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) 0 = welcomePE := by
  decide

theorem lowerParsedBlockFloat?_destinations (expression : ParsedExpr)
    (accesses : ParsedBlockFloatAccesses)
    (lowered : lowerParsedBlockFloat? expression = some accesses) :
    accesses.destinations = expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [lowerParsedBlockFloat?] at lowered
  repeat' (first
    | split at lowered
    | simp_all
    | rw [Option.bind_eq_some_iff] at lowered
    | rcases lowered with ⟨_, _, lowered⟩)

theorem executeParsedBlockFloatAtMAB_apply_lm1_free
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (output : IntegerALU.Bus) (oldContext coords : ParsedIntegerContext) :
    ∀ (destinations : List ParsedOperand),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
        (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
        executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output oldContext
          coords destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
        nextFiles.lm1 = files.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro noLm1 files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons destination rest ih =>
      intro noLm1 files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
          have headFrame := writeParsedMslMsrDestination?_lm1_of_ne files destination
            { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
            output 0 cycle currentState.maskDirective hasSingleLineMask
            (fun bank width pair bankEq =>
              noLm1 destination (by simp) bank width pair bankEq) write lowered
          have tailFrame := ih
            (fun item member bank width pair bankEq =>
              noLm1 item (List.mem_cons_of_mem _ member) bank width pair bankEq)
            write.files
            (match write.barUpdate with
              | some (false, value) => value
              | _ => bar0)
            (match write.barUpdate with
              | some (true, value) => value
              | _ => bar1)
            nextFiles nextBar0 nextBar1 executed
          rw [tailFrame, headFrame]

theorem executeParsedBlockFloatAtMAB_writePEs_lm1_frame
    (expression : ParsedExpr)
    (writeDestinations : Fin 4 → Fin 4 → IntegerALU.Bus → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → StepResult (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (writeFrame : ∀ (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12),
      writeDestinations pe cycle output files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = files.lm1)
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus) (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses pes files
        bar0 bar1 outputs = .ok results →
      (results target).1.lm1 = (files target).lm1 := by
  intro pes
  induction pes with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      rfl
  | cons pe rest ih =>
      intro files bar0 bar1 outputs results executed
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
              have headFrame := writeFrame pe cycle
                (parsedOutputAfterFlush flushSelection (buses pe)) (files pe) (bar0 pe)
                (bar1 pe) nextPEFiles nextBar0 nextBar1 wrote
              have tailFrame := ih
                (fun other => if (other == pe) = true then nextPEFiles else files other)
                (fun other => if (other == pe) = true then nextBar0 else bar0 other)
                (fun other => if (other == pe) = true then nextBar1 else bar1 other)
                (fun other index =>
                  if (other == pe && index == cycle) = true
                  then parsedOutputAfterFlush flushSelection (buses pe)
                  else outputs other index)
                results executed
              rw [tailFrame]
              by_cases same : target = pe
              · subst same
                simp only [beq_self_eq_true, ite_true]
                exact headFrame
              · have different : (target == pe) = false := by
                  simp [same]
                simp [different]

theorem executeParsedBlockFloatAtMAB_runCycles_lm1_frame
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (writeFrame : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∀ target : Fin 4, (results target).1.lm1 = (files target).lm1)
    (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1
        outputs = .ok results →
      (results target).1.lm1 = (files target).lm1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      rfl
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
          have headFrame := writeFrame cycle
            (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
            files bar0 bar1 outputs results' ranWrite target
          have tailFrame := ih (fun pe => (results' pe).1) (fun pe => (results' pe).2.1)
            (fun pe => (results' pe).2.2.1) (fun pe index => (results' pe).2.2.2 index)
            results executed
          rw [tailFrame]
          exact headFrame

theorem executeParsedBlockFloat_writeCycle_lm1_frame
    (currentState : State) (hasSingleLineMask : Bool) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (accesses : ParsedBlockFloatAccesses)
    (noLm1 : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1)
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
    (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (executed : writeCycle cycle buses files bar0 bar1 outputs = .ok results)
    (target : Fin 4) :
    (results target).1.lm1 = (files target).lm1 := by
  rw [form cycle buses files bar0 bar1 outputs] at executed
  exact executeParsedBlockFloatAtMAB_writePEs_lm1_frame expression _ 
    (fun pe cyc out fl b0 b1 nf nb0 nb1 hh =>
      executeParsedBlockFloatAtMAB_apply_lm1_free currentState hasSingleLineMask cyc out
        (currentState.peContext (physicalPEId coordinate pe))
        (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
        accesses.destinations noLm1 fl b0 b1 nf nb0 nb1 hh)
    cycle buses target (List.finRange 4) files bar0 bar1 outputs results executed

theorem executeParsedBlockFloatAtMAB_lm1_frame
    (readState currentState next : State) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedBlockFloatAtMAB.eq_1] at executed
  dsimp only at executed
  cases lowered : lowerParsedBlockFloat? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i results ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        subst executed
        have accessesNoLm1 : ∀ destination ∈ accesses.destinations,
            ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
              ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
                bank ≠ PEMemory.Bank.lm1 := by
          intro destination member bank width pair bankEq
          have eq := lowerParsedBlockFloat?_destinations expression accesses lowered
          exact noLm1 destination (by rw [← eq]; exact member) bank width pair bankEq
        by_cases zero : coordinate = (⟨0, 0, 0, 0⟩ : MABCoordinate)
        · subst zero
          have foldEq := blockFloatFoldl_peRegisters_target noForward
            (⟨0, 0, 0, 0⟩ : MABCoordinate) results 0 (List.finRange 4) currentState
            (List.nodup_finRange 4) (List.mem_finRange 0)
          rw [physicalPEId_zero_zero] at foldEq
          rw [foldEq]
          have frame := executeParsedBlockFloatAtMAB_runCycles_lm1_frame accesses _ _
            (fun cycle buses files bar0 bar1 outputs results' hh target =>
              executeParsedBlockFloat_writeCycle_lm1_frame currentState hasSingleLineMask
                expression (⟨0, 0, 0, 0⟩ : MABCoordinate) accesses accessesNoLm1 _
                (fun _ _ _ _ _ _ => rfl) cycle buses files bar0 bar1 outputs results' hh target)
            0 [0, 1, 2, 3] (fun pe => currentState.peRegisters (physicalPEId
              (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)) _ _ _ results ran
          simpa [physicalPEId_zero_zero] using frame
        · have notTouched : ∀ pe ∈ List.finRange 4,
              welcomePE ≠ physicalPEId coordinate pe := by
            intro pe _ hpe
            exact zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)
          rw [blockFloatFoldl_peRegisters_frame noForward coordinate results welcomePE
            (List.finRange 4) currentState notTouched]

theorem executeParsedBlockFloatAtMABs_lm1_frame
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedBlockFloatAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed
      simp only [executeParsedBlockFloatAtMABs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons coordinate rest ih =>
      intro state next executed
      simp only [executeParsedBlockFloatAtMABs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        rw [ih middle next executed]
        exact executeParsedBlockFloatAtMAB_lm1_frame readState state middle expression
          coordinate noForward hasSingleLineMask noLm1 headExecuted

theorem executeParsedBlockFloatProducer_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedBlockFloatProducer.eq_1] at executed
  cases filtered : List.filter parsedExprIsBlockFloatProducer expressions with
  | nil =>
      rw [filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [filtered] at executed
          exact executeParsedBlockFloatAtMABs_lm1_frame readState expression noForward
            hasSingleLineMask
            (noLm1 expression (List.mem_filter.mp (by rw [filtered]; simp)).1)
            allMABCoordinates currentState next executed
      | cons second remaining =>
          rw [filtered] at executed
          simp at executed

/-! ### 3.6 The remaining two stage frames, exactly

These are the two stages not covered above.  The matrix-MAU/write stage is the
one whose *commit* form is still open (`WelcomePEMatrixMAUStageCommit`), and the
L1BM-to-PE stage writes through its own `writeParsedL1ToPEDestination?` rather
than through the shared single-destination writer, so its `.lm1` frame needs a
separate per-destination analysis.  Both frames are therefore stated as the
named residuals `WelcomePEMatrixMAUStageLm1Frame` and
`WelcomePEL1ToPEStageLm1Frame`, in exactly the shape of the corresponding
conjunct of `WelcomePEStageLm1Frame`.  `welcomePEStageLm1Frame_of_residuals`
then proves `WelcomePEStageLm1Frame` from those two facts, the other three
conjuncts being discharged unconditionally above. -/


def WelcomePEMatrixMAUStageLm1Frame : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool),
    (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
    executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok next →
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1

def WelcomePEL1ToPEStageLm1Frame : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool),
    (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
    executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next →
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1

def WelcomePEStageLm1FrameProvedPart : Prop :=
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedMslMsrProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedFloatReluProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedBlockFloatProducer readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1)

theorem welcomePEStageLm1Frame_provedPart : WelcomePEStageLm1FrameProvedPart :=
  ⟨fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedMslMsrProducers_lm1_frame readState currentState next expressions noForward
      hasSingleLineMask noLm1 executed,
   fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedFloatReluProducers_lm1_frame readState currentState next expressions noForward
      hasSingleLineMask noLm1 executed,
   fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedBlockFloatProducer_lm1_frame readState currentState next expressions noForward
      hasSingleLineMask noLm1 executed⟩

theorem welcomePEStageLm1Frame_of_residuals
    (matrixFrame : WelcomePEMatrixMAUStageLm1Frame)
    (l1Frame : WelcomePEL1ToPEStageLm1Frame) : WelcomePEStageLm1Frame :=
  ⟨welcomePEStageLm1Frame_provedPart.1,
   welcomePEStageLm1Frame_provedPart.2.1,
   welcomePEStageLm1Frame_provedPart.2.2,
   matrixFrame, l1Frame⟩

theorem welcomePEIntegerStageLm1Frame_of_noFloatMAU
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (nodup : pes.Nodup) (mem : welcomePE ∈ pes)
    (intNoLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  refine welcomePEIntegerStageLm1Frame_corrected expressions pes state next nodup mem
    intNoLm1 ?_ executed
  intro expression member
  rw [floatEmpty] at member
  simp at member

end ProofsLean.MNCore
