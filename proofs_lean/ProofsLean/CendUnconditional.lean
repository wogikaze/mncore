import ProofsLean.ConvertEndianLowerBound
import ProofsLean.FamilyDestinationCongruence

/-! # `12.convert-endian`: unconditional refutations at the observed state

`ProofsLean/ConvertEndianLowerBound.lean` reduces `LowerBound cendSealedMachine
cendSpec 2` to the single residual `CendPELinesRefuted`: no one-line `.pe`
program is correct.  This module closes one whole family of that residual
**unconditionally** and states the exact remaining gap.

## What makes `12.convert-endian` different from `1.a-b`

`1.a-b` observes sixteen LM1 words, so a width/count argument ("one line writes
at most eight words, so one observed word is untouched and keeps its initial
`0` against a non-zero target") refutes every non-`.double` line
(`ABWidthBound.ab_not_correct_of_lm1WidthNotDouble`).  `12.convert-endian`
observes only the **two** words of LM1 long address `0`, so no counting argument
applies: both observed words fit in one `.long` (or `.double`) window, and a
`.word` store at LM1 address `0` already writes one of them.

What *does* single out `12.convert-endian` is the **data** of the two words.  At
the initial state the only non-zero register words in the whole machine are LM0
words `0` and `1` of every PE (the two halves of the input word); LM1, GRF, `T`,
the mask registers, the matrix store, L1BM/L2BM, DAR and the forwarding
payloads are all zero, and the forwarding validity bits are `false` (so every
`.forward` source is `poison`).  The two observed words therefore start at `0`,
and a line that prepares only **zero data** for LM1 leaves them at `0` — which
is wrong whenever the target pair is non-zero.  That is the shape of every
family this module closes.

## Results proved here

* §1 — the initial state field by field (`lm0` words `0`/`1`/others, `lm1`,
  GRF, `T`, mask registers, matrix store, block memory, forwarding poison,
  clock, context, directive) and the two observed words at the initial state.
* §2 — the observed-word kernel: a `.pe` line whose PE-0 LM1 bank is
  identically zero after the step is incorrect at the witness
  `cendWitness = 0x0102030405060708`, whose target is
  `byteSwap64 cendWitness = 0x0807060504030201` (`cend_not_correct_of_lm1_zero`),
  plus the commit form `cend_not_correct_of_commit_lm1_zero`.
* §3 — the zero-data commit algebra on the executor's own
  `commitParsedMaskedWrites`: a prepared write whose four data words are `0`
  writes `0` into every word of its window, so a zero-data commit list
  preserves an identically-zero LM1 bank
  (`commitParsedMaskedWrites_lm1_zero_of_data_zero`).
* §4 — **the `.matrixRead` family is closed unconditionally**:
  * the matrix store is identically zero at the initial state, hence every
    matrix-read operand bus is `⟨0, 0⟩` (`parsedMatrixReadBus_zero`), every
    flush keeps it at zero, and every prepared write of the row carries zero
    data (`prepareParsedMatrixReadExprCycles_data_zero`);
  * the line-level extraction at the `cendSpec` initial state
    (`cendMatrixReadSingleton_prepared`, the state-general
    `matrixReadSingleton_prepared` instantiated at `cendInitialState`) and its
    multi-row form (`cendAllMatrixReadLines_prepared`) show that the PE-0 file
    after the step is *exactly* the commit of that zero-data list;
  * so **any** line built only from `.matrixRead` rows leaves both observed
    words at `0` and is refuted (`cendPE_allMatrixReadLines_not_correct`).
* §5 — two more unconditional closures and the residual:
  * **inert lines**: a line whose every row is a `.noforward`, a `.wait` or one
    of the five shared-block `.l1bm` operations (`mwrite`/`m4write`/`gather`/
    `reduce`/`reduce4`, i.e. `parsedExprIsPEInertProducer`) never writes a PE
    register file at all
    (`WelcomeGapShape.executeIntegerProducerInstructionLine_pe_peRegisters_of_inert`),
    so both observed words keep the initial `0`
    (`cendPE_inertLines_not_correct`);
  * `CendClosedLines` bundles the two closed classes (`.matrixRead`-only lines
    and PE-frame lines) and `cendPE_closedLines_not_correct` refutes every line
    in it;
  * the residual is `CendPENonClosedRefuted`, and
    `cendPELinesRefuted_iff_nonClosed` proves it is *equivalent* to
    `CendPELinesRefuted` (nothing weaker is assumed);
    `cendLowerBound_two_of_nonClosed` composes it with the
    `ConvertEndianLowerBound` reduction to give `LowerBound ... 2`, and
    `cendLowerBound_two_iff_residual` states the same reduction in the
    `CendPEUnrefuted` style of `ABUnconditional`.

## What is *not* closed, and why the `1.a-b` template does not apply

The remaining families are the ones whose LM1 writes carry non-zero data at the
initial state: plain integer ALU (`.alu`/`.zero`/`.immediate`), `msl`/`msr`,
float MAU, float relu, block float, matrix MAU, L1BM broadcast and
`.matrixWrite` (the last two are PE-frame or zero-data *at the observed words*
only for their own destinations, which are not yet extracted at the line level
here).  Their value argument **cannot be witness-independent**, unlike `1.a-b`:
the `$msb1` fixed source and the `.immediate` payload are line constants, and a
`.word` store of the `$msb1` pattern into LM1 word `0` is *correct* at the input
`0x0000000000000080` (its target pair is `(0x80000000, 0)`, and that store
writes exactly `0x80000000` into word `0`, leaving word `1` at its initial `0`;
checked informally against the executor, not a theorem of this module), so the
witness has to depend on the line.  Closing the residual therefore needs, per family, an
explicit construction of a witness input from the line's constants, plus the
state-general destination/count transfer (§4's machinery is the first half of
that for `.matrixRead`).  There is no `12.convert-endian` analogue of
`ab_not_correct_of_lm1WidthNotDouble`: both observed words fit in one window.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 1. The initial state of `cendSpec` -/

theorem cendInitialPERegisters_lm0_zero (input : BitVec 64) :
    (cendInitialPERegisters input).lm0 ⟨0, by decide⟩ = input.extractLsb' 32 32 := by
  simp [cendInitialPERegisters]

theorem cendInitialPERegisters_lm0_one (input : BitVec 64) :
    (cendInitialPERegisters input).lm0 ⟨1, by decide⟩ = input.extractLsb' 0 32 := by
  simp [cendInitialPERegisters]

theorem cendInitialPERegisters_lm0_other (input : BitVec 64)
    (address : Fin Bank.lm0.capacity) (zero : address.val ≠ 0) (one : address.val ≠ 1) :
    (cendInitialPERegisters input).lm0 address = 0 := by
  simp [cendInitialPERegisters, zero, one]

theorem cendInitialPERegisters_lm0_eq (input : BitVec 64)
    (address : Fin Bank.lm0.capacity) :
    (cendInitialPERegisters input).lm0 address =
      if address.val = 0 then input.extractLsb' 32 32
      else if address.val = 1 then input.extractLsb' 0 32
      else 0 := rfl

theorem cendInitialPERegisters_lm1 (input : BitVec 64)
    (address : Fin Bank.lm1.capacity) :
    (cendInitialPERegisters input).lm1 address = 0 := rfl

theorem cendInitialPERegisters_grf0 (input : BitVec 64)
    (address : Fin Bank.grf0.capacity) :
    (cendInitialPERegisters input).grf0 address = 0 := rfl

theorem cendInitialPERegisters_grf1 (input : BitVec 64)
    (address : Fin Bank.grf1.capacity) :
    (cendInitialPERegisters input).grf1 address = 0 := rfl

theorem cendInitialPERegisters_t (input : BitVec 64)
    (address : Fin Bank.t.capacity) :
    (cendInitialPERegisters input).t address = 0 := rfl

theorem cendInitialPERegisters_maskRegisters (input : BitVec 64) (entry : Fin 15)
    (cycle : Fin 4) :
    (cendInitialPERegisters input).maskRegisters entry cycle = 0 := rfl

/-- The observed LM1 word `0` of a state. -/
def cendOutputWord0 (state : State) : BitVec 32 :=
  (state.peRegisters cendPE).lm1 ⟨0, by decide⟩

/-- The observed LM1 word `1` of a state. -/
def cendOutputWord1 (state : State) : BitVec 32 :=
  (state.peRegisters cendPE).lm1 ⟨1, by decide⟩

theorem readPair_zero_of_memory_zero (bank : PEMemory.Bank)
    (memory : PEMemory.Memory bank) (start : Fin bank.capacity)
    (zero : ∀ address, memory address = 0) :
    FloatPEMemory.readPair bank memory start = 0 := by
  unfold FloatPEMemory.readPair
  simp only [PEMemory.readWords]
  simp [zero]

theorem cendOutputPair_zero_of_lm1_zero (state : State)
    (zero : ∀ address, (state.peRegisters cendPE).lm1 address = 0) :
    cendOutputPair state = 0 :=
  readPair_zero_of_memory_zero .lm1 _ _ zero

theorem cendOutputPair_eq_append (state : State) :
    cendOutputPair state = cendOutputWord0 state ++ cendOutputWord1 state := by
  rfl

theorem cendInitialState_outputWord0 (input : BitVec 64) :
    cendOutputWord0 (cendInitialState input) = 0 := by
  unfold cendOutputWord0 cendInitialState
  exact cendInitialPERegisters_lm1 input _

theorem cendInitialState_outputWord1 (input : BitVec 64) :
    cendOutputWord1 (cendInitialState input) = 0 := by
  unfold cendOutputWord1 cendInitialState
  exact cendInitialPERegisters_lm1 input _

theorem cendInitialState_outputPair_zero (input : BitVec 64) :
    cendOutputPair (cendInitialState input) = 0 := by
  rw [cendOutputPair_eq_append, cendInitialState_outputWord0,
    cendInitialState_outputWord1]
  rfl

theorem cendInitialState_matrixRegisters_zero (input : BitVec 64) :
    (cendInitialState input).matrixRegisters = fun _ _ _ _ _ _ => 0 := rfl

theorem cendInitialState_blockMemory_zero (input : BitVec 64) :
    (cendInitialState input).blockMemory = fun _ => 0 := rfl

theorem cendInitialState_l1bm_zero (input : BitVec 64) :
    (cendInitialState input).l1bm = fun _ _ => 0 := rfl

theorem cendInitialState_forwarding_poison (input : BitVec 64) (pe : PEId)
    (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4) :
    stateForwardingSlots (cendInitialState input) pe unit cycle = .poison := by
  unfold stateForwardingSlots cendInitialState
  simp [rustSimulatorInitialState_forwarding_invalid]

theorem cendInitialState_hazardClock_zero (input : BitVec 64) :
    (cendInitialState input).hazardClock = 0 := rfl

theorem cendInitialState_maskDirective_entry_zero (input : BitVec 64) :
    (cendInitialState input).maskDirective.entry = ⟨0, by decide⟩ := rfl

theorem cendInitialState_maskDirective_targets (input : BitVec 64) :
    (cendInitialState input).maskDirective.targets = {} := rfl

theorem cendInitialState_bar0 (input : BitVec 64) :
    ((cendInitialState input).peContext cendPE).bar0 = 0 := rfl

theorem cendInitialState_bar1 (input : BitVec 64) :
    ((cendInitialState input).peContext cendPE).bar1 = 0 := rfl

theorem cendInitialState_tWord (input : BitVec 64) :
    ((cendInitialState input).peContext cendPE).tWord = 0 := rfl

/-! ## 2. The witness and the observed-word kernel -/

theorem cendWitness_target : byteSwap64 cendWitness = 0x0807060504030201 := by decide

theorem cendWitness_target_ne_zero : byteSwap64 cendWitness ≠ 0 := by decide

/-- **The observed-word kernel.**  A `.pe` line whose PE-0 LM1 bank is identically
zero after the step at the witness input is incorrect: the target pair is
non-zero while the observed pair is `0`. -/
theorem cend_not_correct_of_lm1_zero (expressions : List NormalizedExpr) (next : State)
    (step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) = some next)
    (zero : ∀ address, (next.peRegisters cendPE).lm1 address = 0) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 cendWitness (cendSpec_admissible _)
  rw [cendSpec_initial] at executed
  have stepResult : cendSealedMachine.step (InstructionLine.pe expressions)
      (cendInitialState cendWitness) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  have postPair : cendOutputPair result = byteSwap64 cendWitness := post
  rw [resultEq] at postPair
  have zeroPair : cendOutputPair next = 0 := cendOutputPair_zero_of_lm1_zero next zero
  rw [zeroPair, cendWitness_target] at postPair
  exact absurd postPair (by decide)

/-! ## 3. The zero-data commit algebra

A prepared write whose four data words are all `0` writes `0` into every word of
its window (a masked merge of a zero old word with a zero new word is zero), so
a commit of such writes preserves an identically-zero LM1 bank. -/

theorem welcomeCommitStep_lm1_zero_of_data_zero (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (dataZero : ∀ i : Fin 4, write.data i = 0)
    (target : Fin Bank.lm1.capacity) (oldZero : files.lm1 target = 0) :
    (welcomeCommitStep files write).lm1 target = 0 := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
        exact oldZero
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
            exact oldZero
        | some access =>
            cases access with
            | mk bank width address =>
                cases bank with
                | lm1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    by_cases within : distance .lm1 address target < count .lm1 width
                    · rw [writeWordsMasked_at .lm1 width files.lm1 address target data
                        selection.flags selection.longLong within]
                      have dataAll : data = fun _ => 0 := funext dataZero
                      rw [oldZero, dataAll]
                      simp [mergeSelectedWord]
                    · rw [writeWordsMasked_preserves_outside .lm1 width files.lm1 address
                        target data selection.flags selection.longLong
                        (Nat.le_of_not_lt within)]
                      exact oldZero
                | lm0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | grf0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | grf1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | t =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero

/-- **A zero-data commit list preserves an identically-zero LM1 bank.** -/
theorem commitParsedMaskedWrites_lm1_zero_of_data_zero
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (dataZero : ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0)
    (oldZero : ∀ target, files.lm1 target = 0) :
    ∀ target, (commitParsedMaskedWrites files writes).lm1 target = 0 := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using oldZero
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member
        exact dataZero item (List.mem_cons_of_mem _ member)
      · intro target
        exact welcomeCommitStep_lm1_zero_of_data_zero files write
          (dataZero write (by simp)) target (oldZero target)

/-- **The commit-form observed-word kernel.** -/
theorem cend_not_correct_of_commit_lm1_zero (expressions : List NormalizedExpr)
    (next : State)
    (step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) =
      some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters cendPE =
      commitParsedMaskedWrites ((cendInitialState cendWitness).peRegisters cendPE) writes)
    (dataZero : ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  refine cend_not_correct_of_lm1_zero expressions next step ?_
  intro address
  rw [committed]
  exact commitParsedMaskedWrites_lm1_zero_of_data_zero _ writes dataZero
    (fun target => cendInitialPERegisters_lm1 cendWitness target) address

/-! ## 4. The `.matrixRead` family: zero data at the initial state

At the initial state the matrix store is identically zero, so every matrix-read
operand bus is `⟨0, 0⟩`: the store is read, never computed from constants.  A
flush only ANDs with a word mask, and `prepareParsedMatrixReadTargets` copies
`unpackALUBus output` into the prepared writes' data.  Hence every write of a
`.matrixRead` line carries the zero bus, and §3 keeps the observed words at
zero. -/

/-- A target list prepared from the zero bus produces zero-data writes. -/
theorem prepareParsedMatrixReadTargets_data_zero (targets : List ParsedMatrixReadTarget) :
    ∀ (output : IntegerALU.Bus) (writes : List PreparedParsedMaskedWrite)
      (bars : List (Bool × BitVec 12)),
      output = ⟨0, 0⟩ →
      prepareParsedMatrixReadTargets targets output = .ok (writes, bars) →
      ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 := by
  induction targets with
  | nil =>
      intro output writes bars _ prepared write member
      simp [prepareParsedMatrixReadTargets] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      simp at member
  | cons target rest ih =>
      intro output writes bars outputZero prepared write member
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              simp only [List.mem_cons] at member
              rcases member with same | later
              · subst same
                intro i
                have busZero : unpackALUBus output = fun _ => 0 := by
                  rw [outputZero]; exact unpackALUBus_zero
                exact congrFun busZero i
              · exact ih output tailWrites tailBars outputZero tail write later
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              simp only [List.mem_cons] at member
              rcases member with same | later
              · subst same
                intro i
                have busZero : unpackALUBus output = fun _ => 0 := by
                  rw [outputZero]; exact unpackALUBus_zero
                exact congrFun busZero i
              · exact ih output tailWrites tailBars outputZero tail write later
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              exact ih output tailWrites tailBars outputZero tail write (by simpa using member)

/-- One matrix-read cycle on the zero store prepares zero-data writes. -/
theorem prepareParsedMatrixReadCycle_data_zero (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadCycle files slots welcomeZeroMatrixStore expression
      directive hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 := by
  unfold prepareParsedMatrixReadCycle at prepared
  cases lowered : ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters
      directive hasSingleLineMask context with
  | none => simp [lowered] at prepared
  | some accesses =>
      simp only [lowered] at prepared
      cases flush : resolveFlushSelection? expression.flush files.maskRegisters context.cycle with
      | none => simp [flush] at prepared
      | some flushSelection =>
          simp only [flush] at prepared
          have outputZero : parsedOutputAfterFlush flushSelection
              (parsedMatrixReadBus welcomeZeroMatrixStore accesses context) = ⟨0, 0⟩ := by
            rw [parsedMatrixReadBus_zero, parsedOutputAfterFlush_zero]
          cases targets : prepareParsedMatrixReadTargets accesses.targets
              (parsedOutputAfterFlush flushSelection
                (parsedMatrixReadBus welcomeZeroMatrixStore accesses context)) with
          | failure => simp [targets] at prepared
          | unknown => simp [targets] at prepared
          | ok result =>
              obtain ⟨doneWrites, doneBars⟩ := result
              simp only [targets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, _, rfl⟩ := prepared
              exact prepareParsedMatrixReadTargets_data_zero accesses.targets _ doneWrites
                doneBars outputZero targets

/-- The four-cycle accumulation on the zero store prepares zero-data writes. -/
theorem prepareParsedMatrixReadCycles_data_zero (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext) :
    ∀ (cycles : List (Fin 4)) (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12))
      (result : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12)),
      (∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0) →
      prepareParsedMatrixReadCycles files welcomeZeroMatrixStore expression directive
        hasSingleLineMask noForward context cycles writes nextSlots bars = .ok result →
      ∀ write ∈ result.1, ∀ i : Fin 4, write.data i = 0 := by
  intro cycles
  induction cycles with
  | nil =>
      intro writes nextSlots bars result prior prepared
      simp only [prepareParsedMatrixReadCycles, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      exact prior
  | cons cycle rest ih =>
      intro writes nextSlots bars result prior prepared
      simp only [prepareParsedMatrixReadCycles] at prepared
      cases head : prepareParsedMatrixReadCycle files nextSlots welcomeZeroMatrixStore expression
          directive hasSingleLineMask noForward { context with cycle := cycle } with
      | failure => simp [head] at prepared
      | unknown => simp [head] at prepared
      | ok cycleResult =>
          obtain ⟨cycleWrites, cycleSlots, cycleBars⟩ := cycleResult
          simp only [head] at prepared
          have cycleZero : ∀ write ∈ cycleWrites, ∀ i : Fin 4, write.data i = 0 :=
            prepareParsedMatrixReadCycle_data_zero files nextSlots expression directive
              hasSingleLineMask noForward { context with cycle := cycle } cycleWrites
              cycleSlots cycleBars head
          have combined : ∀ write ∈ writes ++ cycleWrites, ∀ i : Fin 4, write.data i = 0 := by
            intro write member
            rcases List.mem_append.mp member with earlier | later
            · exact prior write earlier
            · exact cycleZero write later
          exact ih (writes ++ cycleWrites) cycleSlots (bars ++ cycleBars) result combined prepared

/-- The whole `.matrixRead` row on the zero store prepares zero-data writes. -/
theorem prepareParsedMatrixReadExprCycles_data_zero (files : IntegerRegisterFiles)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadExprCycles files initialSlots welcomeZeroMatrixStore
      expression directive hasSingleLineMask noForward context = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 := by
  unfold prepareParsedMatrixReadExprCycles at prepared
  exact prepareParsedMatrixReadCycles_data_zero files expression directive hasSingleLineMask
    noForward context parsedMatrixReadCycles [] initialSlots []
    (writes, slots, bars) (by intro write member; simp at member) prepared

/-- **The line-level extraction for a single `.matrixRead` row at the
`12.convert-endian` initial state.**  A successful sealed step commits the
executor's own `prepareParsedMatrixReadExprCycles` list at that input's PE-0
register file (the state-general form of
`FamilyDestinationCongruence.matrixReadSingleton_prepared`). -/
theorem cendMatrixReadSingleton_prepared
    (expression : NormalizedExpr) (input : BitVec 64) (next : State)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision)
    (step : cendSealedMachine.step (.pe [expression]) (cendInitialState input) = some next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      prepareParsedMatrixReadExprCycles ((cendInitialState input).peRegisters cendPE)
        (stateForwardingSlots (cendInitialState input) cendPE)
        ((cendInitialState input).matrixRegisters
          (ParsedIntegerContext.ofLinearIndex cendPE).group
          (ParsedIntegerContext.ofLinearIndex cendPE).l2b
          (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
        expression.toParsed (cendInitialState input).maskDirective
        (parsedExprHasSingleLineWriteMask expression.toParsed) false
        (parsedPEHazardControl (cendInitialState input) cendPE).context =
        .ok (writes, slots, bars) ∧
      next.peRegisters cendPE =
        commitParsedMaskedWrites ((cendInitialState input).peRegisters cendPE) writes := by
  have executed : executeNormalizedLine (InstructionLine.pe [expression]).toNormalizedLine
      (cendInitialState input) = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe [expression]).toNormalizedLine
        (cendInitialState input) with
    | ok result => simpa [cendSealedMachine, h] using step
    | failure => simp [cendSealedMachine, h] at step
    | unknown => simp [cendSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [expression])
      (cendInitialState input) = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  obtain ⟨nextPEs, walk, registersEq⟩ :=
    executeIntegerProducerInstructionLine_pe_matrixRead_exists expression
      (cendInitialState input) next precision readOp lineExecuted
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walk
  have floatEmpty : ([expression.toParsed].filter
      parsedExprIsSupportedFloatMAUProducer) = [] := by
    simp [readOp, parsedExprIsSupportedFloatMAUProducer]
  obtain ⟨prepared, prepWelcome, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list [expression.toParsed]
      ((List.finRange 4095).map Fin.succ) (cendInitialState input) nextPEs absent floatEmpty walk
  obtain ⟨writes, slots, bars⟩ := prepared
  have stage : [expression.toParsed].filter parsedExprIsIntegerMatrixReadStageInput =
      [expression.toParsed] := by
    simp [matrixRead_stageInput expression.toParsed precision readOp]
  rw [stage] at prepWelcome
  have readPrep := prepareParsedIntegerMatrixReadLineCycles_singleton_matrixRead_inv
    ((cendInitialState input).peRegisters cendPE)
    (stateForwardingSlots (cendInitialState input) cendPE)
    ((cendInitialState input).matrixRegisters
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
    expression.toParsed
    { directive := (cendInitialState input).maskDirective
      context :=
        { (ParsedIntegerContext.ofLinearIndex cendPE) with
          bar0 := ((cendInitialState input).peContext cendPE).bar0
          bar1 := ((cendInitialState input).peContext cendPE).bar1
          tWord := ((cendInitialState input).peContext cendPE).tWord }
      elapsedWords := (cendInitialState input).hazardClock } false
    precision readOp writes slots bars prepWelcome
  refine ⟨writes, slots, bars, ?_, ?_⟩
  · simpa [parsedPEHazardControl, readOp] using readPrep
  · rw [registersEq]
    exact committed

/-- **The `.matrixRead` family is refuted.**  A single `.matrixRead` row leaves
both observed LM1 words at the initial `0` at the witness input: every prepared
write of the row carries the zero bus (the matrix store is zero), so the target
pair `0x0807060504030201` is unreachable. -/
theorem cendPE_matrixRead_not_correct (expression : NormalizedExpr) (next : State)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision)
    (step : cendSealedMachine.step (.pe [expression]) (cendInitialState cendWitness) =
      some next) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [expression]] : List InstructionLine) := by
  obtain ⟨writes, slots, bars, prepared, committed⟩ :=
    cendMatrixReadSingleton_prepared expression cendWitness next precision readOp step
  have storeZero :
      ((cendInitialState cendWitness).matrixRegisters
        (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b) = welcomeZeroMatrixStore := rfl
  rw [storeZero] at prepared
  have dataZero : ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 :=
    prepareParsedMatrixReadExprCycles_data_zero
      ((cendInitialState cendWitness).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState cendWitness) cendPE) expression.toParsed
      (cendInitialState cendWitness).maskDirective
      (parsedExprHasSingleLineWriteMask expression.toParsed) false
      (parsedPEHazardControl (cendInitialState cendWitness) cendPE).context writes slots bars prepared
  exact cend_not_correct_of_commit_lm1_zero [expression] next step writes committed dataZero


/-- The line preparation of a `.matrixRead` row is its own four-cycle
preparation, re-wrapped. -/
theorem prepareParsedIntegerMatrixReadLineExpression_matrixRead
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (precision : ParsedPrecision) (hop : expression.op = .matrixRead precision) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store expression
        control hasSingleLineMask noForward reduced =
      (match prepareParsedMatrixReadExprCycles files nextSlots store expression
          control.directive hasSingleLineMask noForward control.context with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (writes, outputSlots, barUpdates) => .ok (writes, outputSlots, barUpdates)) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst hop
  rfl

/-- **The whole line preparation of a list of `.matrixRead` rows prepares zero
data.**  Each row is prepared by its own `prepareParsedMatrixReadExprCycles` on
the zero store (§4), and the expression list fold only concatenates the rows'
write lists. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_data_zero
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool) :
    ∀ (expressions : List ParsedExpr),
      (∀ expression ∈ expressions, ∃ precision, expression.op = .matrixRead precision) →
      ∀ (writes : List PreparedParsedMaskedWrite)
        (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
        (bars : List (Bool × BitVec 12))
        (result : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
          List (Bool × BitVec 12)),
        (∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0) →
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots welcomeZeroMatrixStore
          control hasSingleLineMask noForward reduced expressions writes nextSlots bars =
          .ok result →
        ∀ write ∈ result.1, ∀ i : Fin 4, write.data i = 0 := by
  intro expressions
  induction expressions with
  | nil =>
      intro _ writes nextSlots bars result prior prepared
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      exact prior
  | cons expression rest ih =>
      intro allRead writes nextSlots bars result prior prepared
      have headRead : ∃ precision, expression.op = .matrixRead precision :=
        allRead expression (by simp)
      have restRead : ∀ item ∈ rest, ∃ precision, item.op = .matrixRead precision :=
        fun item member => allRead item (List.mem_cons_of_mem _ member)
      obtain ⟨precision, hop⟩ := headRead
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at prepared
      rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead files oldSlots nextSlots
        welcomeZeroMatrixStore expression control hasSingleLineMask noForward reduced
        precision hop] at prepared
      cases head : prepareParsedMatrixReadExprCycles files nextSlots welcomeZeroMatrixStore
          expression control.directive hasSingleLineMask noForward control.context with
      | failure => simp [head] at prepared
      | unknown => simp [head] at prepared
      | ok expressionResult =>
          obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := expressionResult
          simp only [head] at prepared
          have expressionZero : ∀ write ∈ expressionWrites, ∀ i : Fin 4, write.data i = 0 :=
            prepareParsedMatrixReadExprCycles_data_zero files nextSlots expression
              control.directive hasSingleLineMask noForward control.context
              expressionWrites expressionSlots expressionBars head
          have combined : ∀ write ∈ writes ++ expressionWrites, ∀ i : Fin 4, write.data i = 0 := by
            intro write member
            rcases List.mem_append.mp member with earlier | later
            · exact prior write earlier
            · exact expressionZero write later
          exact ih restRead (writes ++ expressionWrites) expressionSlots
            (bars ++ expressionBars) result combined prepared

/-- **The line preparation of a list of `.matrixRead` rows prepares zero data.** -/
theorem prepareParsedIntegerMatrixReadLineCycles_data_zero
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (expressions : List ParsedExpr)
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.op = .matrixRead precision)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots welcomeZeroMatrixStore
      expressions control reduced = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 :=
  prepareParsedIntegerMatrixReadLineExpressions_data_zero files oldSlots control _
    (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) reduced
    expressions allRead [] oldSlots [] (writes, nextSlots, bars)
    (by intro write member; simp at member) prepared


/-! ### Filter equalities for lines built only from `.matrixRead` rows -/

theorem allMatrixRead_mem_toParsed {expressions : List NormalizedExpr}
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision)
    {item : ParsedExpr} (member : item ∈ expressions.map NormalizedExpr.toParsed) :
    ∃ precision, item.op = .matrixRead precision := by
  obtain ⟨expression, expressionMem, rfl⟩ := List.mem_map.mp member
  exact allRead expression expressionMem

theorem allMatrixRead_stageInput_filter {expressions : List NormalizedExpr}
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision) :
    (expressions.map NormalizedExpr.toParsed).filter parsedExprIsIntegerMatrixReadStageInput =
      expressions.map NormalizedExpr.toParsed := by
  apply List.filter_eq_self.mpr
  intro item member
  obtain ⟨precision, hop⟩ := allMatrixRead_mem_toParsed allRead member
  exact matrixRead_stageInput item precision hop

/-- A `.matrixRead` row satisfies the integer stage's outer producer filter. -/
theorem matrixRead_outerPredicate (item : ParsedExpr) (precision : ParsedPrecision)
    (hop : item.op = .matrixRead precision) :
    (!parsedExprIsL2BMProducer item && !parsedExprIsMslMsrProducer item &&
      !parsedExprIsMatrixMAUProducer item && !parsedExprIsBlockFloatProducer item &&
      !parsedExprIsFloatReluProducer item) = true := by
  obtain ⟨op, sources, destinations, flush, text⟩ := item
  subst hop
  simp [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
    parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
    parsedExprIsFloatReluProducer]

theorem allMatrixRead_outer_filter {expressions : List NormalizedExpr}
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision) :
    (expressions.map NormalizedExpr.toParsed).filter (fun item =>
      !parsedExprIsL2BMProducer item && !parsedExprIsMslMsrProducer item &&
        !parsedExprIsMatrixMAUProducer item && !parsedExprIsBlockFloatProducer item &&
        !parsedExprIsFloatReluProducer item) = expressions.map NormalizedExpr.toParsed := by
  apply List.filter_eq_self.mpr
  intro item member
  obtain ⟨precision, hop⟩ := allMatrixRead_mem_toParsed allRead member
  exact matrixRead_outerPredicate item precision hop

theorem allMatrixRead_noProducer {expressions : List NormalizedExpr}
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision)
    (producer : ParsedExpr → Bool)
    (rowFalse : ∀ (item : ParsedExpr) (precision : ParsedPrecision), item.op = .matrixRead precision →
      producer item = false) :
    (expressions.map NormalizedExpr.toParsed).filter producer = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro item member
  obtain ⟨precision, hop⟩ := allMatrixRead_mem_toParsed allRead member
  simp [rowFalse item precision hop]

theorem allMatrixRead_any_false {expressions : List NormalizedExpr}
    (allRead : ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision)
    (producer : ParsedExpr → Bool)
    (rowFalse : ∀ (item : ParsedExpr) (precision : ParsedPrecision), item.op = .matrixRead precision →
      producer item = false) :
    (expressions.map NormalizedExpr.toParsed).any producer = false := by
  apply List.any_eq_false.mpr
  intro item member
  obtain ⟨precision, hop⟩ := allMatrixRead_mem_toParsed allRead member
  simp [rowFalse item precision hop]

/-- **The line-level extraction for a line built only from `.matrixRead` rows.**
A successful sealed step commits the integer stage's own preparation of the
whole expression list at the initial PE-0 register file. -/
theorem cendAllMatrixReadLines_prepared (expressions : List NormalizedExpr)
    (input : BitVec 64) (next : State)
    (allRead : ∀ expression ∈ expressions,
      ∃ precision, expression.toParsed.op = .matrixRead precision)
    (step : cendSealedMachine.step (.pe expressions) (cendInitialState input) = some next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles ((cendInitialState input).peRegisters cendPE)
        (stateForwardingSlots (cendInitialState input) cendPE)
        ((cendInitialState input).matrixRegisters
          (ParsedIntegerContext.ofLinearIndex cendPE).group
          (ParsedIntegerContext.ofLinearIndex cendPE).l2b
          (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
        (expressions.map NormalizedExpr.toParsed)
        { directive := (cendInitialState input).maskDirective
          context :=
            { (ParsedIntegerContext.ofLinearIndex cendPE) with
              bar0 := ((cendInitialState input).peContext cendPE).bar0
              bar1 := ((cendInitialState input).peContext cendPE).bar1
              tWord := ((cendInitialState input).peContext cendPE).tWord }
          elapsedWords := (cendInitialState input).hazardClock } false =
        .ok (writes, slots, bars) ∧
      next.peRegisters cendPE =
        commitParsedMaskedWrites ((cendInitialState input).peRegisters cendPE) writes := by
  have executed : executeNormalizedLine (InstructionLine.pe expressions).toNormalizedLine
      (cendInitialState input) = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe expressions).toNormalizedLine
        (cendInitialState input) with
    | ok result => simpa [cendSealedMachine, h] using step
    | failure => simp [cendSealedMachine, h] at step
    | unknown => simp [cendSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions)
      (cendInitialState input) = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions (cendInitialState input) next
      lineExecuted
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions (cendInitialState input)
      next accepted waits unsupported supported lineExecuted
  have outer := allMatrixRead_outer_filter allRead
  rw [outer] at walkExecuted
  have floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsSupportedFloatMAUProducer])
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walkExecuted
  obtain ⟨prepared, preparedEq, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list
      (expressions.map NormalizedExpr.toParsed) ((List.finRange 4095).map Fin.succ)
      (cendInitialState input) nextPEs absent floatEmpty walkExecuted
  obtain ⟨writes, slots, bars⟩ := prepared
  have stage := allMatrixRead_stageInput_filter allRead
  rw [stage] at preparedEq
  have mslEmpty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsMslMsrProducer])
  have reluEmpty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsFloatReluProducer])
  have blockEmpty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsBlockFloatProducer])
  have mauEmpty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsMatrixMAUProducer])
  have writeAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsMatrixWriteProducer = false :=
    allMatrixRead_any_false allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsMatrixWriteProducer])
  have l1Empty : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [] :=
    allMatrixRead_noProducer allRead _ (fun item precision hop => by
      simp [hop, parsedExprIsL1ToPEProducer])
  have mslId : executeParsedMslMsrProducers (cendInitialState input) nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self (cendInitialState input) nextPEs _ _ _ mslEmpty
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers (cendInitialState input) nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok nextMsl :=
    executeParsedFloatReluProducers_eq_self (cendInitialState input) nextMsl _ _ _ reluEmpty
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer (cendInitialState input) nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok nextRelu :=
    executeParsedBlockFloatProducer_eq_self (cendInitialState input) nextRelu _ _ _ blockEmpty
  have nextBlockEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  have matrixId : executeParsedMatrixMAUAndWrites (cendInitialState input) nextBlockFloat
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextBlockFloat :=
    executeParsedMatrixMAUAndWrites_eq_self (cendInitialState input) nextBlockFloat _ _ _
      mauEmpty writeAny
  have afterMatrixEq : afterMatrix = nextBlockFloat := by
    rw [matrixId] at matrixExecuted
    exact (StepResult.ok.inj matrixExecuted).symm
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters (cendInitialState input) afterMatrix
      nextShared _ _ sharedExecuted
  have l1Id : executeParsedL1ToPEProducers (cendInitialState input) nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) = .ok nextShared :=
    executeParsedL1ToPEProducers_eq_self (cendInitialState input) nextShared _ _ _ _ l1Empty
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed
    exact (StepResult.ok.inj l1Executed).symm
  refine ⟨writes, slots, bars, preparedEq, ?_⟩
  have registersEq : next.peRegisters = nextBroadcast.peRegisters := by
    rw [nextEq]
  rw [registersEq, nextBroadcastEq, sharedFrame, afterMatrixEq, nextBlockEq, nextReluEq,
    nextMslEq]
  exact committed

/-- **Lines built only from `.matrixRead` rows are refuted.**  Every prepared
write carries the zero bus, so both observed words stay `0` against the
non-zero target pair. -/
theorem cendPE_allMatrixReadLines_not_correct (expressions : List NormalizedExpr)
    (allRead : ∀ expression ∈ expressions,
      ∃ precision, expression.toParsed.op = .matrixRead precision) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      obtain ⟨writes, slots, bars, prepared, committed⟩ :=
        cendAllMatrixReadLines_prepared expressions cendWitness next allRead step
      have storeZero :
          ((cendInitialState cendWitness).matrixRegisters
            (ParsedIntegerContext.ofLinearIndex cendPE).group
            (ParsedIntegerContext.ofLinearIndex cendPE).l2b
            (ParsedIntegerContext.ofLinearIndex cendPE).l1b) = welcomeZeroMatrixStore := rfl
      rw [storeZero] at prepared
      have allReadParsed : ∀ item ∈ expressions.map NormalizedExpr.toParsed,
          ∃ precision, item.op = .matrixRead precision :=
        fun item member => allMatrixRead_mem_toParsed allRead member
      have dataZero : ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 :=
        prepareParsedIntegerMatrixReadLineCycles_data_zero
          ((cendInitialState cendWitness).peRegisters cendPE)
          (stateForwardingSlots (cendInitialState cendWitness) cendPE)
          { directive := (cendInitialState cendWitness).maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex cendPE) with
                bar0 := ((cendInitialState cendWitness).peContext cendPE).bar0
                bar1 := ((cendInitialState cendWitness).peContext cendPE).bar1
                tWord := ((cendInitialState cendWitness).peContext cendPE).tWord }
            elapsedWords := (cendInitialState cendWitness).hazardClock } false
          (expressions.map NormalizedExpr.toParsed) allReadParsed writes slots bars prepared
      exact cend_not_correct_of_commit_lm1_zero expressions next step writes committed dataZero


/-! ## 5. The residual: exactly the lines this module does not refute -/

/-- The first class §4 refutes: every expression is a `.matrixRead` row. -/
def CendAllMatrixReadLines (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions, ∃ precision, expression.toParsed.op = .matrixRead precision

/-- **The `.matrixRead` family is refuted**, restated on the class name. -/
theorem cendPE_not_correct_of_allMatrixReadLines (expressions : List NormalizedExpr)
    (isRead : CendAllMatrixReadLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_allMatrixReadLines_not_correct expressions isRead

/-- A single `.matrixRead` row is an instance of the closed class. -/
theorem cendAllMatrixReadLines_singleton (expression : NormalizedExpr)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision) :
    CendAllMatrixReadLines [expression] := by
  intro item member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨precision, readOp⟩

/-! ### The inert-line family: no PE register write at all

Lines whose every row is a `.noforward`, a `.wait` or one of the five
shared-block `.l1bm` operations never write a PE register file at all
(`WelcomeGapShape.executeIntegerProducerInstructionLine_pe_peRegisters_of_inert`),
so both observed words keep the initial `0` and the line is refuted by §2. -/

/-- **Inert lines are refuted.** -/
theorem cendPE_inertLines_not_correct (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      have executed := cendSealed_step_ok step
      have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions)
          (cendInitialState cendWitness) = .ok next := by
        unfold executeNormalizedLine at executed
        simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
        exact executed
      have frame := executeIntegerProducerInstructionLine_pe_peRegisters_of_inert
        expressions (cendInitialState cendWitness) next all lineExecuted
      refine cend_not_correct_of_lm1_zero expressions next step ?_
      intro address
      rw [frame]
      exact cendInitialPERegisters_lm1 cendWitness address

/-- **The classes this module refutes**: lines built only from `.matrixRead` rows
and lines with no PE-register write at all. -/
def CendClosedLines (expressions : List NormalizedExpr) : Prop :=
  CendAllMatrixReadLines expressions ∨
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)

/-- **Every closed line is refuted.** -/
theorem cendPE_closedLines_not_correct (expressions : List NormalizedExpr)
    (closed : CendClosedLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  rcases closed with isRead | inert
  · exact cendPE_allMatrixReadLines_not_correct expressions isRead
  · exact cendPE_inertLines_not_correct expressions inert

/-- **The residual after this module.**  Every `.pe` line outside
`CendClosedLines`: it has at least one `.matrixRead`-free row and at least one
row that writes a PE register file. -/
def CendPENonClosedRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, ¬ CendClosedLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **`CendPELinesRefuted` from the residual.**  The two closed families are
refuted by §4 and §5; everything else is the residual. -/
theorem cendPELinesRefuted_of_nonClosed (rest : CendPENonClosedRefuted) :
    CendPELinesRefuted := by
  intro expressions correct
  by_cases closed : CendClosedLines expressions
  · exact cendPE_closedLines_not_correct expressions closed correct
  · exact rest expressions closed correct

/-- **The residual is exactly the gap.**  `CendPELinesRefuted` and the residual
are equivalent, so closing the residual closes the recorded one-line obligation
and nothing weaker is being assumed. -/
theorem cendPELinesRefuted_iff_nonClosed :
    CendPELinesRefuted ↔ CendPENonClosedRefuted := by
  constructor
  · intro refuted expressions _closed
    exact refuted expressions
  · exact cendPELinesRefuted_of_nonClosed

/-- **Bound two from the residual.**  The `ConvertEndianLowerBound` reduction
chain composed with §4–§5: a proof of the residual closes
`LowerBound cendSealedMachine cendSpec 2`. -/
theorem cendLowerBound_two_of_nonClosed (rest : CendPENonClosedRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_peLines (cendPELinesRefuted_of_nonClosed rest)

/-- **The residual in the `ABUnconditional` style.**  Every *unrefuted* `.pe`
line (accepted, wait-free, supported, not all-`.noforward`, i.e. the class
`CendPEUnrefuted` left open by `ConvertEndianLowerBound`) outside
`CendClosedLines`. -/
def CendValueResidual : Prop :=
  ∀ expressions : List NormalizedExpr, CendPEUnrefuted expressions →
    ¬ CendClosedLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **Bound two from the value residual.**  Every syntactic rejection, every
all-`.noforward` line, every `.matrixRead`-only line and every PE-frame line is
refuted unconditionally; the residual is the remaining per-family value
argument. -/
theorem cendLowerBound_two_of_residual (value : CendValueResidual) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_unrefuted (fun expressions unrefuted => by
    intro correct
    by_cases closed : CendClosedLines expressions
    · exact cendPE_closedLines_not_correct expressions closed correct
    · exact value expressions unrefuted closed correct)

/-- **The residual is exactly the gap at bound two.**  So §4–§5 removed a
genuine part of `CendPELinesRefuted` and the residual is not a weakening. -/
theorem cendLowerBound_two_iff_residual :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 ↔ CendValueResidual := by
  constructor
  · intro lower expressions _unrefuted _closed correct
    exact (cendLowerBound_two_iff_peLines.mp lower expressions) correct
  · exact cendLowerBound_two_of_residual

end ProofsLean.MNCore
