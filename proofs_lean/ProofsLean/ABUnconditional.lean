import ProofsLean.StageCommitWalk
import ProofsLean.ABLowerBound
import ProofsLean.WelcomeValueBound
import ProofsLean.ALURequestProvenance
import ProofsLean.PlusTwoLowerBound
import ProofsLean.WelcomePlainStep
import ProofsLean.PlainALUDestination
import ProofsLean.DoubleWindowValue

/-! # `1.a-b`: the plain-ALU narrow branch, unconditionally

`ProofsLean/ABLowerBound.lean` reduces `LowerBound abSealedMachine abSpec 2` to
refuting every unrefuted one-line `.pe` program (`AbPEUnrefuted`).
`ProofsLean/ABWidthBound.lean` closes the non-`.double` width case given a
write list, `ProofsLean/DoubleWindowValue.lean` closes the `.double` case given
the right-witness window data, and `ProofsLean/ALURequestProvenance.lean`
projects the four destinations of a plain ALU row out of the executor's
dependent request match.  What was missing was the *line level*: from a
successful sealed step at an initial state, obtain the executor's own prepared
write list, and transfer a zero-state write shape to the witness inputs.

This module supplies that layer for the **plain integer-ALU family**
(`.alu` / `.zero` / `.immediate`), which is the family whose state-general
destination congruence is already proved in
`ProofsLean/PlainALUDestination.lean`, and closes its **narrow branch**
unconditionally:

* `abPlainSingleton_prepared` — at *any* `1.a-b` initial state, a successful
  single-row plain `.pe` line commits the four-cycle
  `prepareParsedIntegerALUExprCycles` list (via
  `executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists`,
  `executeIntegerProducerLineAtPEs_zero_commit_list` and the singleton
  inversion `prepareParsedIntegerMatrixReadLineCycles_singleton_plain_inv`);
* `abPlainZero_prepared_shape` — at the all-zero input the prepared list is
  either all copied `.double` blocks or fits four two-word windows
  (`prepareParsedIntegerALUExprCycles_four`, the nine-branch per-cycle
  `prepareParsedIntegerALUExprCycle_lm1_facts` of `WelcomePlainStep`, and
  `lm1WritesShape_of_chunks`);
* `abPlain_destinations_eq` — the prepared destination list is the same at any
  two initial states (`prepareParsedIntegerALUCycles_destination_state_general`;
  only `maskRegisters` matters and those are zero everywhere);
* `abPE_plain_narrow_not_correct` — a plain row whose zero-state list is narrow
  is incorrect at `A = 1.0, B = 0`: the windows transfer along the destination
  equality, four two-word windows cover at most eight of the sixteen observed
  words, and an uncovered word keeps the initial `0` while the target is
  `0x3F800000` (`ab_not_correct_of_narrowAtOnes`);
* `abPE_plain_not_correct_or_doubleCase` — every single plain row is either
  refuted or its zero-state prepared list is the `.double` case;
* `abPE_not_correct_of_rightWindowData` — a line whose right witness is an
  aligned, covering, data-safe write list is refuted at `A = 0, B = 1.0`
  (`abZeroRight_doubleWindow_refutes`);
* `abLowerBound_two_of_residuals` — `LowerBound abSealedMachine abSpec 2`
  follows from the two residual statements below, and
  `abLowerBound_two_iff_residuals` shows the two residuals are *exactly* the
  remaining gap (they are equivalent to the bound, so nothing is weakened
  silently);
* `abLowerBound_two_of_rightWindowData` — the same bound from the *uniform*
  residual `ABRightWindowData`: every unrefuted line outside the class
  `ABPlainClosed` (which this module refutes) must have the right-witness
  window data.  This is the exact hypothesis of
  `ab_not_correct_of_lm1DoubleWindow`, per line and hence per family.

## The two residuals, precisely

* `ABPlainDoubleResidual` — a single plain row whose zero-state prepared list
  is the `.double` case (`ABPlainZeroDouble`), or whose destination is an
  `.immediate` `.double` block (`ABPlainImmediateDouble`), is still unrefuted.
  Closing it needs the right-witness data facts: at `A = 0, B = 1.0` the
  `.double` writes' data words `2, 3` are never `0xBF800000`
  (`Lm1WritesDataSafe`), which `DoubleWindowValue` proves per prepared write for
  memory and `.fixed` operands but not yet for a whole four-cycle row.
* `ABNonPlainResidual` — every unrefuted line that is not a single plain row
  (`.mau`, relu, block float, `.matrixRead`, `.l1bm`, `.l2bm`, msl/msr,
  multi-row lines) is still unrefuted.  Their state-general width/count lemmas
  exist in `WelcomeStageProvenance`/`WelcomeShapes`, but the line-level
  destination transfer at a non-zero input is only proved for the plain family
  (`PlainALUDestination.lean`); the other families need their own congruence
  lemma before the narrow/width kernels apply.

The uniform form of both residuals is `ABRightWindowData`: at
`A = 0, B = 1.0`, PE 0 commits an aligned write list covering all sixteen
observed words whose data words `2, 3` are `ABWitnessDataWord`s.  It is exactly
what `DoubleWindowValue`'s kernel consumes, and it implies the two residuals
above.

So `LowerBound abSealedMachine abSpec 2` is **not** unconditional in this
module; it is proved from exactly those two statements.  No `sorry`, no
`admit`, no `native_decide`, no new axioms, no existing module is edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Line-level extraction for a single plain row -/



/-- Inversion of the singleton line preparation for a plain row. -/
theorem prepareParsedIntegerMatrixReadLineCycles_singleton_plain_inv
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (e : ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool) (barUpdates : List (Bool × BitVec 12))
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (plain : (∃ name precision unsigned arg, e.op = .alu name precision unsigned arg) ∨
      e.op = .zero ∨ ∃ value unsigned, e.op = .immediate value unsigned)
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots store [e] control reduced
      = .ok (writes, slots, barUpdates)) :
    ∃ outSlots, prepareParsedIntegerALUExprCycles files oldSlots oldSlots e control
        ([e].any parsedExprHasSingleLineWriteMask)
        ([e].any (fun expression => match expression.op with | .noforward => true | _ => false))
        reduced = .ok (writes, outSlots) ∧
      barUpdates = parsedIntegerALUBarUpdates e writes := by
  obtain ⟨op, sources, destinations, flush, text⟩ := e
  rcases plain with ⟨name, precision, unsigned, arg, hop⟩ | hop | ⟨value, unsigned, hop⟩
  · subst hop
    unfold prepareParsedIntegerMatrixReadLineCycles at prepared
    simp only [prepareParsedIntegerMatrixReadLineExpressions,
      prepareParsedIntegerMatrixReadLineExpression_plain (files := files) (oldSlots := oldSlots)
      (nextSlots := oldSlots) (store := store)
      (expression := ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩)
      (control := control) (hasSingleLineMask := _) (noForward := _) (reduced := reduced)
      (Or.inl ⟨_, _, _, _, rfl⟩)] at prepared
    split at prepared
    · simp at prepared
    · simp at prepared
    · rename_i expressionWrites expressionSlots expressionBarUpdates hprep
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      split at hprep
      · simp at hprep
      · simp at hprep
      · rename_i w2 s2 hal
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at hprep
        obtain ⟨rfl, rfl, rfl⟩ := hprep
        exact ⟨s2, hal, rfl⟩
  · subst hop
    unfold prepareParsedIntegerMatrixReadLineCycles at prepared
    simp only [prepareParsedIntegerMatrixReadLineExpressions,
      prepareParsedIntegerMatrixReadLineExpression_plain (files := files) (oldSlots := oldSlots)
      (nextSlots := oldSlots) (store := store)
      (expression := ⟨.zero, sources, destinations, flush, text⟩)
      (control := control) (hasSingleLineMask := _) (noForward := _) (reduced := reduced)
      (Or.inr (Or.inl rfl))] at prepared
    split at prepared
    · simp at prepared
    · simp at prepared
    · rename_i expressionWrites expressionSlots expressionBarUpdates hprep
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      split at hprep
      · simp at hprep
      · simp at hprep
      · rename_i w2 s2 hal
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at hprep
        obtain ⟨rfl, rfl, rfl⟩ := hprep
        exact ⟨s2, hal, rfl⟩
  · subst hop
    unfold prepareParsedIntegerMatrixReadLineCycles at prepared
    simp only [prepareParsedIntegerMatrixReadLineExpressions,
      prepareParsedIntegerMatrixReadLineExpression_plain (files := files) (oldSlots := oldSlots)
      (nextSlots := oldSlots) (store := store)
      (expression := ⟨.immediate value unsigned, sources, destinations, flush, text⟩)
      (control := control) (hasSingleLineMask := _) (noForward := _) (reduced := reduced)
      (Or.inr (Or.inr ⟨_, _, rfl⟩))] at prepared
    split at prepared
    · simp at prepared
    · simp at prepared
    · rename_i expressionWrites expressionSlots expressionBarUpdates hprep
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      split at hprep
      · simp at hprep
      · simp at hprep
      · rename_i w2 s2 hal
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at hprep
        obtain ⟨rfl, rfl, rfl⟩ := hprep
        exact ⟨s2, hal, rfl⟩

theorem plain_list_filter
    (e : NormalizedExpr) (h : parsedExprIsPlainIntegerALU e.toParsed = true) :
    ([e].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [e.toParsed] := by
  obtain ⟨_, _, msl, relu, block, _, _, mMAU, mWrite, l1ToPE, l2bm, _, _⟩ :=
    parsedExprIsPlainIntegerALU_facts e.toParsed h
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  simp [l2bm, mMAU, mWrite, l1ToPE, msl, relu, block]

theorem plain_list_float_empty
    (e : NormalizedExpr) (h : parsedExprIsPlainIntegerALU e.toParsed = true) :
    ([e].map NormalizedExpr.toParsed).filter parsedExprIsSupportedFloatMAUProducer = [] := by
  obtain ⟨integer, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    parsedExprIsPlainIntegerALU_facts e.toParsed h
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  cases op : e.toParsed.op with
  | alu name precision unsigned arg => simp [op, parsedExprIsSupportedFloatMAUProducer]
  | zero => simp [op, parsedExprIsSupportedFloatMAUProducer]
  | immediate value unsigned => simp [op, parsedExprIsSupportedFloatMAUProducer]
  | matrixRead precision => simp [parsedExprIsIntegerProducer, op] at integer
  | mau precision matrix kind half round => simp [parsedExprIsIntegerProducer, op] at integer
  | matrixWrite precision => simp [parsedExprIsIntegerProducer, op] at integer
  | wait tag => simp [parsedExprIsIntegerProducer, op] at integer
  | noforward => simp [parsedExprIsIntegerProducer, op] at integer
  | l1bm operation => simp [parsedExprIsIntegerProducer, op] at integer
  | l2bm operation => simp [parsedExprIsIntegerProducer, op] at integer

/-- A plain integer-ALU row is one of the three plain op shapes. -/
theorem plain_op_cases (e : ParsedExpr) (h : parsedExprIsPlainIntegerALU e = true) :
    (∃ name precision unsigned arg, e.op = .alu name precision unsigned arg) ∨ e.op = .zero ∨
      ∃ value unsigned, e.op = .immediate value unsigned := by
  obtain ⟨integer, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    parsedExprIsPlainIntegerALU_facts e h
  cases op : e.op with
  | alu name precision unsigned arg => exact Or.inl ⟨name, precision, unsigned, arg, rfl⟩
  | zero => exact Or.inr (Or.inl rfl)
  | immediate value unsigned => exact Or.inr (Or.inr ⟨value, unsigned, rfl⟩)
  | matrixRead precision => simp [parsedExprIsIntegerProducer, op] at integer
  | mau precision matrix kind half round => simp [parsedExprIsIntegerProducer, op] at integer
  | matrixWrite precision => simp [parsedExprIsIntegerProducer, op] at integer
  | wait tag => simp [parsedExprIsIntegerProducer, op] at integer
  | noforward => simp [parsedExprIsIntegerProducer, op] at integer
  | l1bm operation => simp [parsedExprIsIntegerProducer, op] at integer
  | l2bm operation => simp [parsedExprIsIntegerProducer, op] at integer

/-- **Extraction for a single plain row.**  At any initial `1.a-b` state, the
PE-0 file after a successful line step is the commit of the four-cycle plain ALU
preparation list, with the executor's own arguments. -/
theorem abPlainSingleton_prepared
    (e : NormalizedExpr) (input : ABInput) (next : State)
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (accepted : checkParsedTopLine (InstructionLine.pe [e]).toParsed = true)
    (step : abSealedMachine.step (.pe [e]) (abInitialState input) = some next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycles ((abInitialState input).peRegisters abPE)
        (stateForwardingSlots (abInitialState input) abPE)
        (stateForwardingSlots (abInitialState input) abPE) e.toParsed
        (parsedPEHazardControl (abInitialState input) abPE)
        ([e.toParsed].any parsedExprHasSingleLineWriteMask)
        ([e.toParsed].any (fun expression => match expression.op with
          | .noforward => true | _ => false)) false
        = .ok (writes, slots) ∧
      next.peRegisters abPE =
        commitParsedMaskedWrites ((abInitialState input).peRegisters abPE) writes := by
  have plainList : ([e].map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true := by
    simpa using plain
  have executed : executeNormalizedLine (InstructionLine.pe [e]).toNormalizedLine
      (abInitialState input) = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe [e]).toNormalizedLine
        (abInitialState input) with
    | ok result => simpa [abSealedMachine, h] using step
    | failure => simp [abSealedMachine, h] at step
    | unknown => simp [abSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [e]) (abInitialState input)
      = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists [e] (abInitialState input)
      next accepted plainList lineExecuted
  have filterEq := plain_list_filter e plain
  have floatEmpty := plain_list_float_empty e plain
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split, filterEq] at walk
  obtain ⟨prepared, prepWelcome, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list [e.toParsed]
      ((List.finRange 4095).map Fin.succ) (abInitialState input) nextPEs absent floatEmpty walk
  obtain ⟨writes, slots, bars⟩ := prepared
  have stageInput : parsedExprIsIntegerMatrixReadStageInput e.toParsed = true :=
    plain_stageInput e.toParsed plain
  have stageFilter : [e.toParsed].filter parsedExprIsIntegerMatrixReadStageInput = [e.toParsed] := by
    simp [stageInput]
  rw [stageFilter] at prepWelcome
  have plainOp := plain_op_cases e.toParsed plain
  obtain ⟨outSlots, alu, barsEq⟩ :=
    prepareParsedIntegerMatrixReadLineCycles_singleton_plain_inv
      ((abInitialState input).peRegisters abPE)
      (stateForwardingSlots (abInitialState input) abPE)
      ((abInitialState input).matrixRegisters (ParsedIntegerContext.ofLinearIndex abPE).group
        (ParsedIntegerContext.ofLinearIndex abPE).l2b
        (ParsedIntegerContext.ofLinearIndex abPE).l1b)
      e.toParsed
      { directive := (abInitialState input).maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex abPE) with
            bar0 := ((abInitialState input).peContext abPE).bar0
            bar1 := ((abInitialState input).peContext abPE).bar1
            tWord := ((abInitialState input).peContext abPE).tWord }
        elapsedWords := (abInitialState input).hazardClock } false bars writes slots plainOp
      prepWelcome
  refine ⟨writes, outSlots, ?_, ?_⟩
  · show prepareParsedIntegerALUExprCycles ((abInitialState input).peRegisters abPE)
      (stateForwardingSlots (abInitialState input) abPE)
      (stateForwardingSlots (abInitialState input) abPE) e.toParsed
      (parsedPEHazardControl (abInitialState input) abPE)
      ([e.toParsed].any parsedExprHasSingleLineWriteMask)
      ([e.toParsed].any (fun expression => match expression.op with
        | .noforward => true | _ => false)) false = .ok (writes, outSlots)
    simpa [parsedPEHazardControl] using alu
  · rw [nextEq]
    simp only
    rw [committed]

/-! ## 2. The zero-state shape of a plain row's prepared list -/

/-- **The zero-state shape of a plain row's prepared list.**  All `.lm1` writes
are copied 4-aligned `.double` blocks, or all fit in four two-word windows. -/
theorem abPlainZero_prepared_shape (e : NormalizedExpr)
    (nodup : (e.toParsed.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : ∀ payload sparse, e.toParsed.op = .immediate payload sparse →
      ∀ d ∈ e.toParsed.destinations,
        ParsedOperand.directDestinationBankWidth? d ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
      e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
      (match e.toParsed.op with | .noforward => true | _ => false) false =
        .ok (writes, slots)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
    prepareParsedIntegerALUExprCycles_four welcomeZeroFiles welcomeZeroSlots
      e.toParsed welcomeZeroControl
      (parsedExprHasSingleLineWriteMask e.toParsed)
      (match e.toParsed.op with | .noforward => true | _ => false) false writes slots prep
  have f0 := prepareParsedIntegerALUExprCycle_lm1_facts e.toParsed.op e.toParsed.sources
    e.toParsed.destinations e.toParsed.flush e.toParsed.text _ 0 welcomeZeroSlots w0 s1
    notDouble nodup h0
  have f1 := prepareParsedIntegerALUExprCycle_lm1_facts e.toParsed.op e.toParsed.sources
    e.toParsed.destinations e.toParsed.flush e.toParsed.text _ 1 s1 w1 s2
    notDouble nodup h1
  have f2 := prepareParsedIntegerALUExprCycle_lm1_facts e.toParsed.op e.toParsed.sources
    e.toParsed.destinations e.toParsed.flush e.toParsed.text _ 2 s2 w2 s3
    notDouble nodup h2
  have f3 := prepareParsedIntegerALUExprCycle_lm1_facts e.toParsed.op e.toParsed.sources
    e.toParsed.destinations e.toParsed.flush e.toParsed.text _ 3 s3 w3 slots
    notDouble nodup h3
  have shape := lm1WritesShape_of_chunks e.toParsed nodup w0 w1 w2 w3 f0 f1 f2 f3
  rw [writesEq]
  exact shape

/-! ### Zero-state extraction in canonical form -/

theorem abPlainSingleton_prepared_zero (e : NormalizedExpr) (next : State)
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (accepted : checkParsedTopLine (InstructionLine.pe [e]).toParsed = true)
    (step : abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) = some next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
        e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
        (match e.toParsed.op with | .noforward => true | _ => false) false
        = .ok (writes, slots) ∧
      next.peRegisters abPE = commitParsedMaskedWrites welcomeZeroFiles writes := by
  obtain ⟨writes, slots, prep, commit⟩ :=
    abPlainSingleton_prepared e abZeroInput next plain accepted step
  refine ⟨writes, slots, ?_, ?_⟩
  · simpa [abZeroInput_initialState, welcomeZeroFiles, welcomeZeroSlots, welcomeZeroControl,
      welcomeInitialState, abInitialPERegisters, welcomeInitialPERegisters, abInitialLm0_zero]
      using prep
  · rw [abZeroInput_initialState] at commit
    simpa [welcomeZeroFiles, welcomeInitialState, abInitialPERegisters, welcomeInitialPERegisters,
      abInitialLm0_zero]
      using commit

/-! ## 3. Destination congruence between two initial states -/

theorem abPlain_destinations_eq
    (filesA filesB : IntegerRegisterFiles) (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (e : ParsedExpr) (controlA controlB : ParsedMaskExecutionControl)
    (controlEq : controlA = controlB)
    (hsm nf reduced : Bool)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (prepA : prepareParsedIntegerALUExprCycles filesA oldSlotsA oldSlotsA e controlA hsm nf reduced =
      .ok (writesA, slotsA))
    (prepB : prepareParsedIntegerALUExprCycles filesB oldSlotsB oldSlotsB e controlB hsm nf reduced =
      .ok (writesB, slotsB)) :
    writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  subst controlEq
  unfold prepareParsedIntegerALUExprCycles at *
  exact prepareParsedIntegerALUCycles_destination_state_general filesA filesB oldSlotsA oldSlotsB
    e controlA hsm nf reduced maskEq parsedIntegerALUCycles [] oldSlotsA [] oldSlotsB
    (writesA, slotsA) (writesB, slotsB) rfl prepA prepB

theorem lm1WritesNarrow_of_destination_map_eq
    (writesA writesB : List PreparedParsedMaskedWrite)
    (mapEq : writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination))
    (narrowB : Lm1WritesNarrow writesB) :
    Lm1WritesNarrow writesA := by
  obtain ⟨windows, covers, bound, sizes⟩ := narrowB
  refine ⟨windows, ?_, bound, sizes⟩
  intro write member width address destination
  have memMap : write.destination ∈ writesA.map (fun w => w.destination) :=
    List.mem_map_of_mem member
  rw [mapEq] at memMap
  obtain ⟨other, otherMem, otherDest⟩ := List.mem_map.mp memMap
  have otherDestination : other.destination = some ⟨.lm1, width, address⟩ := by
    rw [otherDest]
    exact destination
  exact covers other otherMem width address otherDestination

/-! ## 4. The plain-ALU narrow branch, unconditionally -/

/-- **The plain-ALU narrow branch is closed.**  If the line is a single plain
row accepted by the issue checker and its zero-state prepared list is narrow,
then the line is incorrect at `A = 1.0, B = 0`: the windows transfer to that
input along the destination congruence, four two-word windows cover at most
eight of the sixteen observed words, and an uncovered word keeps the initial
`0` while the target is `0x3F800000`. -/
theorem abPE_plain_narrow_not_correct
    (e : NormalizedExpr) (nextZero : State)
    (accepted : AbPEAccepted [e])
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (stepZero : abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) = some nextZero)
    (narrowZero : ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
        e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
        (match e.toParsed.op with | .noforward => true | _ => false) false =
          .ok (writes, slots) →
        Lm1WritesNarrow writes) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [e]] : List InstructionLine) := by
  obtain ⟨writes0, slots0, prep0, _commit0⟩ :=
    abPlainSingleton_prepared_zero e nextZero plain accepted.1 stepZero
  have narrow0 := narrowZero writes0 slots0 prep0
  refine ab_not_correct_of_narrowAtOnes [e] ?_
  intro next stepLeft
  obtain ⟨writesL, slotsL, prepL, commitL⟩ :=
    abPlainSingleton_prepared e abOneLeftInput next plain accepted.1 stepLeft
  have controlEq : parsedPEHazardControl (abInitialState abZeroInput) abPE =
      parsedPEHazardControl (abInitialState abOneLeftInput) abPE := by
    unfold parsedPEHazardControl abInitialState
    rfl
  have prep0' : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
      e.toParsed (parsedPEHazardControl (abInitialState abOneLeftInput) abPE)
      ([e.toParsed].any parsedExprHasSingleLineWriteMask)
      ([e.toParsed].any (fun expression => match expression.op with
        | .noforward => true | _ => false)) false = .ok (writes0, slots0) := by
    have zeroControl : welcomeZeroControl =
        parsedPEHazardControl (abInitialState abOneLeftInput) abPE := by
      unfold welcomeZeroControl parsedPEHazardControl abInitialState welcomeInitialState
      rfl
    rw [zeroControl] at prep0
    simpa using prep0
  have prepL' : prepareParsedIntegerALUExprCycles
      ((abInitialState abOneLeftInput).peRegisters abPE)
      (stateForwardingSlots (abInitialState abOneLeftInput) abPE)
      (stateForwardingSlots (abInitialState abOneLeftInput) abPE)
      e.toParsed (parsedPEHazardControl (abInitialState abOneLeftInput) abPE)
      ([e.toParsed].any parsedExprHasSingleLineWriteMask)
      ([e.toParsed].any (fun expression => match expression.op with
        | .noforward => true | _ => false)) false = .ok (writesL, slotsL) := prepL
  have mapEq := abPlain_destinations_eq welcomeZeroFiles
    ((abInitialState abOneLeftInput).peRegisters abPE) rfl welcomeZeroSlots
    (stateForwardingSlots (abInitialState abOneLeftInput) abPE) e.toParsed
    welcomeZeroControl (parsedPEHazardControl (abInitialState abOneLeftInput) abPE)
    (by
      unfold welcomeZeroControl parsedPEHazardControl abInitialState welcomeInitialState
      rfl)
    ([e.toParsed].any parsedExprHasSingleLineWriteMask)
    ([e.toParsed].any (fun expression => match expression.op with
      | .noforward => true | _ => false)) false writes0 slots0 writesL slotsL prep0' prepL'
  have narrowL : Lm1WritesNarrow writesL :=
    lm1WritesNarrow_of_destination_map_eq writesL writes0 mapEq.symm narrow0
  obtain ⟨windows, covers, bound, sizes⟩ := narrowL
  exact ⟨writesL, windows, commitL, covers, bound, sizes⟩

/-! ## 5. Residuals and the conditional lower bound -/

/-- The zero-state `.double` shape of a single plain row. -/
def ABPlainZeroDouble (e : NormalizedExpr) : Prop :=
  ∃ (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots),
    prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
      e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
      (match e.toParsed.op with | .noforward => true | _ => false) false =
        .ok (writes, slots) ∧
    Lm1WritesDoubleCopy writes

/-- The immediate-`.double` destination shape of a single plain row. -/
def ABPlainImmediateDouble (e : NormalizedExpr) : Prop :=
  (∃ payload sparse, e.toParsed.op = .immediate payload sparse) ∧
    ∃ destination ∈ e.toParsed.destinations,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, PEMemory.Width.double)

/-- **A single plain row is refuted, or its zero state is the `.double` case.** -/
theorem abPE_plain_not_correct_or_doubleCase
    (e : NormalizedExpr) (nextZero : State)
    (unrefuted : AbPEUnrefuted [e])
    (plain : parsedExprIsPlainIntegerALU e.toParsed = true)
    (notDouble : ∀ payload sparse, e.toParsed.op = .immediate payload sparse →
      ∀ d ∈ e.toParsed.destinations,
        ParsedOperand.directDestinationBankWidth? d ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (stepZero : abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) = some nextZero) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
        ([InstructionLine.pe [e]] : List InstructionLine) ∨ ABPlainZeroDouble e := by
  obtain ⟨writes0, slots0, prep0, _commit0⟩ :=
    abPlainSingleton_prepared_zero e nextZero plain unrefuted.1.1 stepZero
  have accepted' : checkParsedTopLine (.pe [e.toParsed]) = true := by
    have h := unrefuted.1.1
    simpa [InstructionLine.toParsed, NormalizedExpr.toParsed] using h
  have legal : LegalParsedLine [e.toParsed] := parsed_topline_check_sound (.pe [e.toParsed]) accepted'
  have memProject : e.toParsed.toIssueExpr 0 ∈ projectLine [e.toParsed] := by
    simp [projectLine, projectFrom]
  have nodup : (e.toParsed.toIssueExpr 0).writeBanks.Nodup :=
    welcomeLm1WritesNodup [e] legal _ memProject
  rcases abPlainZero_prepared_shape e nodup notDouble writes0 slots0 prep0 with double0 | narrow0
  · exact Or.inr ⟨writes0, slots0, prep0, double0⟩
  · refine Or.inl (abPE_plain_narrow_not_correct e nextZero unrefuted.1 plain stepZero ?_)
    intro writes slots prep
    have h1 := prep
    rw [prep0] at h1
    obtain ⟨rfl, rfl⟩ := (StepResult.ok.inj h1).symm
    exact narrow0

/-! ### The uniform right-witness residual -/

/-- **The right-witness window data** of a line: at `A = 0, B = 1.0` the PE-0
file is the commit of an aligned write list covering all sixteen observed words
whose data words `2, 3` are witness data words.  This is exactly the hypothesis
of `ab_not_correct_of_lm1DoubleWindow`; supplying it for every unrefuted family
is the remaining executor link. -/
def ABRightWindowData (expressions : List NormalizedExpr) : Prop :=
  ∀ next, abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) = some next →
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters abPE =
        commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) writes ∧
      Lm1WritesAligned writes ∧ Lm1WritesCover writes ∧ Lm1WritesDataSafe writes

/-- **The right-witness window data refutes the line**, at `A = 0, B = 1.0`,
through `ab_not_correct_of_lm1DoubleWindow`. -/
theorem abPE_not_correct_of_rightWindowData (expressions : List NormalizedExpr)
    (data : ABRightWindowData expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) with
  | none => exact ab_not_correct_of_step_none _ _ step
  | some next =>
      obtain ⟨writes, committed, aligned, covers, safe⟩ := data next step
      exact ProofsLean.refutes_not_correct
        (abZeroRight_doubleWindow_refutes expressions next step writes committed aligned
          covers safe)

/-- **The lines this module refutes**: a single plain row whose zero-state
prepared list is narrow, or a single plain row stuck at the zero input. -/
def ABPlainClosed (expressions : List NormalizedExpr) : Prop :=
  (∃ e : NormalizedExpr, expressions = [e] ∧
      parsedExprIsPlainIntegerALU e.toParsed = true ∧
      (∀ (writes : List PreparedParsedMaskedWrite)
        (slots : ProofsLean.MNCore.Forwarding.Slots),
        prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
          e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
          (match e.toParsed.op with | .noforward => true | _ => false) false =
            .ok (writes, slots) →
          Lm1WritesNarrow writes)) ∨
    (∃ e : NormalizedExpr, expressions = [e] ∧
      abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) = none)

/-- **Every closed line is refuted.** -/
theorem abPE_not_correct_of_plainClosed (expressions : List NormalizedExpr)
    (unrefuted : AbPEUnrefuted expressions) (closed : ABPlainClosed expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  rcases closed with ⟨e, same, plain, narrow⟩ | ⟨e, same, stuck⟩
  · subst same
    cases stepZero : abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) with
    | none => exact ab_not_correct_of_step_none _ _ stepZero
    | some nextZero =>
        exact abPE_plain_narrow_not_correct e nextZero unrefuted.1 plain stepZero narrow
  · subst same
    exact ab_not_correct_of_step_none _ _ stuck

/-- **The plain-row `.double` residual**: the constant-destination case and the
zero-state `.double`-window case of a single plain row. -/
def ABPlainDoubleResidual : Prop :=
  ∀ (e : NormalizedExpr), AbPEUnrefuted [e] →
    parsedExprIsPlainIntegerALU e.toParsed = true →
    (ABPlainImmediateDouble e ∨ ABPlainZeroDouble e) →
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [e]] : List InstructionLine)

/-- A line whose only expression is a plain integer-ALU row. -/
def ABPlainLine (expressions : List NormalizedExpr) : Prop :=
  ∃ e : NormalizedExpr, expressions = [e] ∧ parsedExprIsPlainIntegerALU e.toParsed = true

/-- **The residual for every family other than a single plain row.** -/
def ABNonPlainResidual : Prop :=
  ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions → ¬ ABPlainLine expressions →
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **The lower bound from the two residuals.**  The plain narrow branch is
proved; a plain line is either stuck at the zero input (refuted), narrow
(refuted by `abPE_plain_narrow_not_correct`), or one of the two `.double`
shapes handed to `ABPlainDoubleResidual`.  Every other line is handed to
`ABNonPlainResidual`. -/
theorem abLowerBound_two_of_residuals
    (plainDouble : ABPlainDoubleResidual) (nonPlain : ABNonPlainResidual) :
    ProofsLean.LowerBound abSealedMachine abSpec 2 := by
  apply abLowerBound_two_of_residual
  intro expressions unrefuted
  by_cases plainLine : ABPlainLine expressions
  · obtain ⟨e, same, plain⟩ := plainLine
    subst same
    cases stepZero : abSealedMachine.step (.pe [e]) (abInitialState abZeroInput) with
    | none => exact ab_not_correct_of_step_none _ _ stepZero
    | some nextZero =>
        by_cases immediateDouble : ABPlainImmediateDouble e
        · exact plainDouble e unrefuted plain (Or.inl immediateDouble)
        · have notDouble : ∀ payload sparse, e.toParsed.op = .immediate payload sparse →
              ∀ d ∈ e.toParsed.destinations,
                ParsedOperand.directDestinationBankWidth? d ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double) := by
            intro payload sparse hop d member pair
            exact immediateDouble ⟨⟨payload, sparse, hop⟩, d, member, pair⟩
          rcases abPE_plain_not_correct_or_doubleCase e nextZero unrefuted plain notDouble
            stepZero with refuted | doubleCase
          · exact refuted
          · exact plainDouble e unrefuted plain (Or.inr doubleCase)
  · exact nonPlain expressions unrefuted plainLine

/-- **The lower bound from the uniform right-witness data.**  Every unrefuted
line outside the class this module refutes must supply the aligned, covering,
data-safe right-witness write list.  This is the most informative residual: it
is exactly the hypothesis of `ab_not_correct_of_lm1DoubleWindow`, per line and
therefore per family, and it implies both residuals above. -/
theorem abLowerBound_two_of_rightWindowData
    (rightData : ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
      ¬ ABPlainClosed expressions → ABRightWindowData expressions) :
    ProofsLean.LowerBound abSealedMachine abSpec 2 := by
  apply abLowerBound_two_of_residual
  intro expressions unrefuted
  by_cases closed : ABPlainClosed expressions
  · exact abPE_not_correct_of_plainClosed expressions unrefuted closed
  · exact abPE_not_correct_of_rightWindowData expressions
      (rightData expressions unrefuted closed)

/-- **The residuals are exactly the gap**: the lower bound is equivalent to the
two residual statements, so nothing weaker is being assumed. -/
theorem abLowerBound_two_iff_residuals :
    ProofsLean.LowerBound abSealedMachine abSpec 2 ↔
      ABPlainDoubleResidual ∧ ABNonPlainResidual := by
  constructor
  · intro lower
    refine ⟨?_, ?_⟩
    · intro e unrefuted _plain _shape
      exact (abLowerBound_two_iff_residual.mp lower) [e] unrefuted
    · intro expressions unrefuted _plainLine
      exact (abLowerBound_two_iff_residual.mp lower) expressions unrefuted
  · rintro ⟨plainDouble, nonPlain⟩
    exact abLowerBound_two_of_residuals plainDouble nonPlain


/-- **The uniform residual implies the two named residuals**, so it is a
strictly sharper statement of the same gap. -/
theorem abResiduals_of_rightWindowData
    (rightData : ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
      ¬ ABPlainClosed expressions → ABRightWindowData expressions) :
    ABPlainDoubleResidual ∧ ABNonPlainResidual :=
  (abLowerBound_two_iff_residuals).mp (abLowerBound_two_of_rightWindowData rightData)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
