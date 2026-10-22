import ProofsLean.InputDependence
import ProofsLean.StageCommitWalk
import ProofsLean.WelcomeGapShape

/-! # Write determination for the input-dependence kernel

`ProofsLean/InputDependence.lean` reduces the input-parametric `2.plus-two` floor
argument to a single per-line contract,

```
PlusTwoWriteDetermination := ∀ line, LineDeterminedAt plusTwoLineFootprint plusTwoPE line
```

and leaves it open.  This module audits that residual.  Its finding is negative
and precise:

* the `nop` and `mv` constructors are **discharged** (§1);
* the `.pe` constructor is discharged for the *inert* rows — lines whose rows
  never write a PE register file (§2);
* for a general `.pe` line the contract is **not a theorem of the executor**:
  the committed write list depends on per-line state channels that are not
  bank words, and `WordRef`/`FilesAgreeOn` cannot see them (§3);
* the exact point of failure is machine-checked: two register files that agree
  on *every* `WordRef` value but differ in their OPE mask-register file make the
  executor prepare different write lists and commit different words (§3);
* a general bridge then shows that **any** two successful steps that agree on
  all bank words but end with different observed words refute
  `LineDeterminedAt` at *every* footprint (§4);
* combining the two gives `PlusTwoWriteDetermination`'s falsity from the two
  concrete masked-line steps — the only unproved premise, isolated as
  `WriteDeterminationCounterexampleSteps` (§5).

So the residual as stated cannot be discharged: it needs a *channel-aware*
contract (mask registers, forwarding slots, matrix store, mask directive,
BAR/T context, hazard clock), not the bank-word footprint.  The kernel's
payoff `plusTwo_output_forces_footprint_meets` remains valid **conditionally**
on such a contract; it cannot be re-derived unconditionally from
`plusTwoLineFootprint`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 0. Unwrapping the sealed step

`plusTwoSealedMachine.step` is `executeNormalizedLine` with the three-way
`StepResult` squashed to an `Option`.  Every per-line frame below starts from
the underlying `.ok` equation. -/

/-- A successful sealed step is a successful normalized value step. -/
theorem stepTo_executeNormalizedLine (line : InstructionLine) (state next : State)
    (step : StepTo line state next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  cases executed : executeNormalizedLine line.toNormalizedLine state with
  | ok result => simpa [StepTo, plusTwoSealedMachine, executed] using step
  | failure => simp [StepTo, plusTwoSealedMachine, executed] at step
  | unknown => simp [StepTo, plusTwoSealedMachine, executed] at step

theorem stepTo_nop (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (state next : State) (step : StepTo (.nop count wait) state next) :
    executeNormalizedLine (NormalizedLine.nop count.val wait) state = .ok next := by
  simpa [Issue.InstructionLine.toNormalizedLine] using
    stepTo_executeNormalizedLine (.nop count wait) state next step

theorem stepTo_mv (transfer : NormalizedMv) (state next : State)
    (step : StepTo (.mv transfer) state next) :
    executeIntegerProducerInstructionLine (.mv transfer) state = .ok next := by
  have executed := stepTo_executeNormalizedLine (.mv transfer) state next step
  simpa [executeNormalizedLine, Issue.InstructionLine.toNormalizedLine,
    NormalizedLine.toInstruction?] using executed

theorem stepTo_pe (expressions : List NormalizedExpr) (state next : State)
    (step : StepTo (.pe expressions) state next) :
    executeIntegerProducerInstructionLine (.pe expressions) state = .ok next := by
  have executed := stepTo_executeNormalizedLine (.pe expressions) state next step
  simpa [executeNormalizedLine, Issue.InstructionLine.toNormalizedLine,
    NormalizedLine.toInstruction?] using executed

/-! ## 1. `nop` and `mv`

Both constructors leave every PE register file untouched, so both satisfy the
per-line contract at *any* footprint — in particular at `plusTwoLineFootprint`. -/

/-- `nop` lines satisfy the contract (restated for the concrete payoff). -/
theorem nop_lineDeterminedAt (footprint : InstructionLine → State → Set WordRef)
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    LineDeterminedAt footprint plusTwoPE (.nop count wait) :=
  nop_lineDeterminedOn footprint count wait plusTwoPE

/-- `mv` lines satisfy the contract (restated for the concrete payoff). -/
theorem mv_lineDeterminedAt (footprint : InstructionLine → State → Set WordRef)
    (transfer : NormalizedMv) :
    LineDeterminedAt footprint plusTwoPE (.mv transfer) :=
  lineDeterminedAt_of_frame footprint (.mv transfer)
    (fun state next step => by
      have executed := stepTo_mv transfer state next step
      exact executeNormalizedLine_mv_peRegisters transfer state next
        (by simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using executed))
    plusTwoPE

/-! ## 2. The inert `.pe` lines

A `.pe` line whose rows are all *inert* — shared-block `.l1bm` rows, `.noforward`
rows and `.wait` rows — never writes a PE register file, so it is determined at
the empty footprint.  This is the part of the `.pe` constructor that the
bank-word contract does see. -/

/-- Inert `.pe` lines leave every PE register file untouched. -/
theorem pe_inert_step_peRegisters_frame (expressions : List NormalizedExpr)
    (state next : State)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)
    (step : StepTo (.pe expressions) state next) :
    next.peRegisters = state.peRegisters := by
  have executed := stepTo_pe expressions state next step
  exact executeIntegerProducerInstructionLine_pe_peRegisters_of_inert expressions state next
    all executed

/-- Inert `.pe` lines satisfy the contract at any footprint. -/
theorem pe_inert_lineDeterminedAt (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true) :
    LineDeterminedAt footprint plusTwoPE (.pe expressions) :=
  lineDeterminedAt_of_frame footprint (.pe expressions)
    (fun state next step => pe_inert_step_peRegisters_frame expressions state next all step)
    plusTwoPE

/-- The empty `.pe` line is inert, hence determined. -/
theorem pe_nil_lineDeterminedAt (footprint : InstructionLine → State → Set WordRef) :
    LineDeterminedAt footprint plusTwoPE (.pe []) :=
  pe_inert_lineDeterminedAt footprint []
    (by intro expression member; simp at member)

/-! ## 3. The obstruction: a non-bank channel the footprint cannot see

A prepared write is not a function of the PE-register words alone.  The
executor's per-cycle lowering resolves the write *selection* from the PE's OPE
mask-register file (`IntegerRegisterFiles.maskRegisters`), and `WordRef` has no
mask-register bank: `wordValue` projects only `lm0`, `lm1`, `grf0`, `grf1` and
`t`.  The two files below therefore agree on **every** `WordRef` value while the
executor prepares different lists and commits different words.

The witness row is an unmasked-source `.immediate` producer whose single `LM1`
destination carries the explicit mask selector `$imr1` (mask-register entry 1,
i.e. mask-register word `0` at each cycle).  With the all-zero mask-register
file the selector disables every write; with entry `0`/cycle `0` set to `0xF`
the first cycle writes. -/

/-- Forwarding slots used by the witness preparation: none are read by a
constant producer, so the poison-filled slots are harmless. -/
abbrev writeDetSlots : ProofsLean.MNCore.Forwarding.Slots := fun _ _ => .poison

/-- Matrix store used by the witness preparation: the constant producer reads no
matrix word. -/
abbrev writeDetStore : ParsedMatrixReadStore := fun _ _ _ _ => 0

/-- Preparation control of the observed PE at the all-zero state. -/
abbrev writeDetControl : ParsedMaskExecutionControl :=
  { directive := welcomeMaskDirective
    context := ParsedIntegerContext.ofLinearIndex plusTwoPE
    elapsedWords := 0 }

/-- The masked constant producer: `imm 7` into an `LM1` `.long` destination with
the explicit mask selector `$imr1`. -/
def writeDetMaskedExpr : ParsedExpr where
  op := .immediate 7 false
  sources := []
  destinations :=
    [.mem (Issue.plusOneAccess .lm1 0) false false false (some (.entry false 1))]
  flush := none
  text := ""

/-- The same expression as an `InstructionLine` row. -/
def writeDetMaskedNExpr : NormalizedExpr :=
  ⟨.immediate 7 false, [], writeDetMaskedExpr.destinations, none⟩

/-- The witness line: one masked constant producer. -/
def writeDetMaskedLine : InstructionLine :=
  InstructionLine.pe [writeDetMaskedNExpr]

/-- Register file with the all-zero mask-register file. -/
def writeDetFilesA : IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with maskRegisters := fun _ _ => 0 }

/-- Register file with mask-register word `0` at cycle `0` set to `0xF`; every
bank word is unchanged. -/
def writeDetFilesB : IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with maskRegisters := fun e c =>
      if e.val = 0 ∧ c.val = 0 then 0xF else 0 }

/-- The executor's prepared write list for the witness expression at a given
register file. -/
def writeDetWrites (files : IntegerRegisterFiles) : List PreparedParsedMaskedWrite :=
  match prepareParsedIntegerMatrixReadLineCycles files writeDetSlots writeDetStore
    [writeDetMaskedExpr] writeDetControl false with
  | .ok (writes, _, _) => writes
  | _ => []

/-- The executor's prepared write list at the all-zero mask registers. -/
abbrev writeDetWritesA : List PreparedParsedMaskedWrite := writeDetWrites writeDetFilesA

/-- The executor's prepared write list at the `0xF` mask register. -/
abbrev writeDetWritesB : List PreparedParsedMaskedWrite := writeDetWrites writeDetFilesB

/-- **The two files agree on every bank word.**  Changing the mask-register file
does not change any `WordRef` value. -/
theorem writeDetFiles_agree : FilesAgreeOn Set.univ writeDetFilesA writeDetFilesB := by
  intro w _
  obtain ⟨bank, address⟩ := w
  cases bank <;> rfl

theorem writeDetFiles_maskRegisters_ne :
    writeDetFilesA.maskRegisters ≠ writeDetFilesB.maskRegisters := by
  intro same
  have values := congrArg (fun registers => registers 0 0) same
  simp [writeDetFilesA, writeDetFilesB] at values

/-- **The prepared write selections differ.**  This is the channel the bank-word
footprint cannot see: the same expression at bank-word-identical files prepares
different selection masks. -/
theorem writeDetSelections_ne :
    writeDetWritesA.map PreparedParsedMaskedWrite.selection ≠
      writeDetWritesB.map PreparedParsedMaskedWrite.selection := by
  decide

/-- **The prepared write lists differ** — hence the executor commits different
list records at the two files. -/
theorem writeDetWrites_ne : writeDetWritesA ≠ writeDetWritesB := by
  intro same
  exact writeDetSelections_ne (by rw [same])

/-- With the all-zero mask-register file the first cycle's destination word is
left at `0`: every selection mask is zero. -/
theorem writeDetCommit_A :
    (commitParsedMaskedWrites writeDetFilesA writeDetWritesA).lm1 ⟨0, by decide⟩ = 0 := by
  decide

/-- With mask-register word `0` at cycle `0` set to `0xF` the same execution
writes the constant `7` into that word. -/
theorem writeDetCommit_B :
    (commitParsedMaskedWrites writeDetFilesB writeDetWritesB).lm1 ⟨0, by decide⟩ = 7 := by
  decide

/-- **The committed PE word differs.**  The first cycle's destination word is
left at `0` by the all-zero mask and written with the constant `7` by the `0xF`
mask, even though the two files agree on every bank word. -/
theorem writeDetCommit_ne :
    (commitParsedMaskedWrites writeDetFilesA writeDetWritesA).lm1 ⟨0, by decide⟩ ≠
      (commitParsedMaskedWrites writeDetFilesB writeDetWritesB).lm1 ⟨0, by decide⟩ := by
  rw [writeDetCommit_A, writeDetCommit_B]
  decide

/-- The same statement in `wordValue` form, the shape the commit bridge uses. -/
theorem writeDetCommit_wordValue_ne :
    wordValue (commitParsedMaskedWrites writeDetFilesA writeDetWritesA)
        ⟨.lm1, ⟨0, by decide⟩⟩ ≠
      wordValue (commitParsedMaskedWrites writeDetFilesB writeDetWritesB)
        ⟨.lm1, ⟨0, by decide⟩⟩ := by
  simpa [wordValue] using writeDetCommit_ne

/-! ### No bank-word-determined preparation

The obstruction restated in the form every `.pe` determination proof would have
to establish: the executor's own prepared list is not a function of the
bank-word content of a register file. -/

/-- **The prepared write list is not determined by the bank words.**  There are
two register files that agree on every `WordRef` and on which the executor's
`prepareParsedIntegerMatrixReadLineCycles` returns different write lists. -/
theorem preparedWrites_not_determined_by_bank_words :
    ∃ files files' : IntegerRegisterFiles,
      (∀ w : WordRef, wordValue files w = wordValue files' w) ∧
        prepareParsedIntegerMatrixReadLineCycles files writeDetSlots writeDetStore
            [writeDetMaskedExpr] writeDetControl false ≠
          prepareParsedIntegerMatrixReadLineCycles files' writeDetSlots writeDetStore
            [writeDetMaskedExpr] writeDetControl false := by
  refine ⟨writeDetFilesA, writeDetFilesB, fun w => writeDetFiles_agree w (Set.mem_univ w), ?_⟩
  intro same
  have lists : writeDetWrites writeDetFilesA = writeDetWrites writeDetFilesB := by
    unfold writeDetWrites
    rw [same]
  exact writeDetWrites_ne lists

/-! ## 4. The bridge: agreement on all bank words refutes determination

Any two successful steps whose input files agree on *every* bank word but whose
observed output words differ refute `LineDeterminedAt` at **every** footprint:
a smaller footprint only weakens the agreement hypothesis, so the same state
pair applies.

The key arithmetic is that committing the *same* list to two files that agree
on every word yields the same word (`commitParsedMaskedWrites_congr_on`), so no
list can explain two different results. -/

/-- Committing the same write list to two files that agree on every bank word
gives the same value at every word. -/
theorem commitParsedMaskedWrites_wordValue_congr_of_all
    (files files' : IntegerRegisterFiles)
    (agree : ∀ w : WordRef, wordValue files w = wordValue files' w)
    (writes : List PreparedParsedMaskedWrite) (w : WordRef) :
    wordValue (commitParsedMaskedWrites files writes) w =
      wordValue (commitParsedMaskedWrites files' writes) w :=
  commitParsedMaskedWrites_congr_on files files' writes Set.univ
    (fun v _ => agree v) w (Set.mem_univ w)

/-- **Determination bridge.**  If two states agree on every bank word, both take
the line successfully, and the observed PE's word `w` differs afterwards, then
the line is *not* write-determined — at any footprint whatsoever. -/
theorem not_lineDeterminedAt_of_stepResults_ne
    (footprint : InstructionLine → State → Set WordRef) (line : InstructionLine)
    (pe : PEId) (s s' next next' : State) (w : WordRef)
    (agree : ∀ v : WordRef, wordValue (s.peRegisters pe) v = wordValue (s'.peRegisters pe) v)
    (step : StepTo line s next) (step' : StepTo line s' next')
    (different : wordValue (next.peRegisters pe) w ≠ wordValue (next'.peRegisters pe) w) :
    ¬ LineDeterminedAt footprint pe line := by
  intro determined
  have hAgree : FilesAgreeOn (footprint line s ∪ footprint line s')
      (s.peRegisters pe) (s'.peRegisters pe) :=
    fun v _ => agree v
  obtain ⟨writes, writes', commit, commit', same⟩ :=
    determined s s' next next' hAgree step step'
  subst same
  have left : wordValue (next.peRegisters pe) w =
      wordValue (commitParsedMaskedWrites (s.peRegisters pe) writes) w := by
    rw [commit]
  have right : wordValue (next'.peRegisters pe) w =
      wordValue (commitParsedMaskedWrites (s'.peRegisters pe) writes) w := by
    rw [commit']
  rw [left, right] at different
  exact different (commitParsedMaskedWrites_wordValue_congr_of_all
    (s.peRegisters pe) (s'.peRegisters pe) agree writes w)

/-! ## 5. The concrete masked line refutes the residual

The two states below are the all-zero simulator state with the two witness
register files pushed to every PE.  They agree on every bank word (§3).  The
only remaining premise is that the witness line steps successfully in both
states; that premise is isolated as
`WriteDeterminationCounterexampleSteps`.

Given the two steps, the executor's PE-0 commit list is pinned by
`executeIntegerProducerLineAtPEs_zero_commit_list` to the witness preparation of
§3, the two committed words differ (`writeDetCommit_wordValue_ne`), and the
bridge of §4 concludes. -/

/-- The all-zero simulator state with one register file on every PE. -/
def writeDetState (files : IntegerRegisterFiles) : State :=
  { rustSimulatorInitialState with peRegisters := fun _ => files }

theorem writeDetState_peRegisters (files : IntegerRegisterFiles) (pe : PEId) :
    (writeDetState files).peRegisters pe = files := rfl

theorem writeDetState_maskDirective (files : IntegerRegisterFiles) :
    (writeDetState files).maskDirective = welcomeMaskDirective := rfl

theorem writeDetState_matrixStore (files : IntegerRegisterFiles) :
    (writeDetState files).matrixRegisters
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b = writeDetStore := rfl

theorem writeDetState_context (files : IntegerRegisterFiles) (pe : PEId) :
    (writeDetState files).peContext pe = ParsedIntegerContext.ofLinearIndex pe := rfl

theorem writeDetState_clock (files : IntegerRegisterFiles) :
    (writeDetState files).hazardClock = 0 := rfl

theorem writeDetState_forwardingSlots (files : IntegerRegisterFiles) :
    stateForwardingSlots (writeDetState files) plusTwoPE = writeDetSlots := by
  funext unit cycle
  simp [stateForwardingSlots, writeDetState, rustSimulatorInitialState, writeDetSlots]

/-- The witness line is a plain integer producer row. -/
theorem writeDetMaskedLine_plain :
    ([writeDetMaskedNExpr].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
  decide

theorem writeDetMaskedLine_filter :
    ([writeDetMaskedNExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [writeDetMaskedExpr] := by
  decide

theorem writeDetMaskedLine_floatEmpty :
    [writeDetMaskedExpr].filter parsedExprIsSupportedFloatMAUProducer = [] := by
  decide

/-- The witness line's stage input is the witness expression itself. -/
theorem writeDetMaskedLine_stageInput :
    [writeDetMaskedExpr].filter parsedExprIsIntegerMatrixReadStageInput =
      [writeDetMaskedExpr] := by
  decide

theorem writeDetState_control (files : IntegerRegisterFiles) :
    ({ directive := (writeDetState files).maskDirective
       context :=
         { ParsedIntegerContext.ofLinearIndex welcomePE with
           bar0 := ((writeDetState files).peContext welcomePE).bar0
           bar1 := ((writeDetState files).peContext welcomePE).bar1
           tWord := ((writeDetState files).peContext welcomePE).tWord }
       elapsedWords := (writeDetState files).hazardClock } : ParsedMaskExecutionControl) =
      writeDetControl := rfl

/-- **The pinned PE-0 commit of the witness line.**  From a successful sealed
step of the witness line at `writeDetState files`, the observed PE's register
file is the commit of the executor's own witness preparation list on `files`. -/
theorem writeDetMasked_step_commit (files : IntegerRegisterFiles) (next : State)
    (step : StepTo writeDetMaskedLine (writeDetState files) next) :
    next.peRegisters plusTwoPE =
      commitParsedMaskedWrites files (writeDetWrites files) := by
  have executed := stepTo_pe [writeDetMaskedNExpr] (writeDetState files) next step
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    writeDetMaskedLine (writeDetState files) next executed
  have plain := writeDetMaskedLine_plain
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
      [writeDetMaskedNExpr] (writeDetState files) next accepted plain executed
  rw [writeDetMaskedLine_filter] at walk
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walk
  obtain ⟨prepared, prepEq, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list [writeDetMaskedExpr]
      ((List.finRange 4095).map Fin.succ) (writeDetState files) nextPEs absent
      writeDetMaskedLine_floatEmpty walk
  rw [writeDetMaskedLine_stageInput,
    show (writeDetState files).peRegisters welcomePE = files from rfl,
    writeDetState_forwardingSlots, writeDetState_matrixStore, writeDetState_control] at prepEq
  have preparedEq : prepared.1 = writeDetWrites files := by
    unfold writeDetWrites
    rw [prepEq]
  rw [nextEq]
  change nextPEs.peRegisters welcomePE = commitParsedMaskedWrites files (writeDetWrites files)
  rw [committed, preparedEq]
  rfl

/-- **The only unproved premise.**  The witness masked line steps successfully
in both bank-word-identical states.  This is an executor-existence fact: the
producer has no sources, the mask selectors resolve totally
(`resolveParsedMaskSelection?_always_resolves`), and the destination is a direct
`LM1` `.long` window, so both walks are expected to `.ok`.  It is stated, not
assumed inside a theorem that claims to be unconditional. -/
def WriteDeterminationCounterexampleSteps : Prop :=
  ∃ next next' : State,
    StepTo writeDetMaskedLine (writeDetState writeDetFilesA) next ∧
      StepTo writeDetMaskedLine (writeDetState writeDetFilesB) next'

/-- **No bank-word footprint whatsoever determines the witness line.**  The two
states agree on every `WordRef` (`writeDetFiles_agree`), so they satisfy the
agreement hypothesis of `LineDeterminedAt` for *any* footprint; the pinned
commits of §5 differ at `LM1` word `0` (`writeDetCommit_wordValue_ne`), so no
common write list exists.  In particular, no extension of `plusTwoLineFootprint`
inside `Set WordRef` can repair the contract. -/
theorem no_footprint_determines_witness_line
    (steps : WriteDeterminationCounterexampleSteps) :
    ∀ footprint : InstructionLine → State → Set WordRef,
      ¬ LineDeterminedAt footprint plusTwoPE writeDetMaskedLine := by
  obtain ⟨next, next', step, step'⟩ := steps
  intro footprint
  have agree : ∀ v : WordRef,
      wordValue ((writeDetState writeDetFilesA).peRegisters plusTwoPE) v =
        wordValue ((writeDetState writeDetFilesB).peRegisters plusTwoPE) v :=
    fun v => writeDetFiles_agree v (Set.mem_univ v)
  have different : wordValue (next.peRegisters plusTwoPE)
        ⟨.lm1, ⟨0, by decide⟩⟩ ≠
      wordValue (next'.peRegisters plusTwoPE) ⟨.lm1, ⟨0, by decide⟩⟩ := by
    rw [writeDetMasked_step_commit writeDetFilesA next step,
      writeDetMasked_step_commit writeDetFilesB next' step']
    exact writeDetCommit_wordValue_ne
  exact not_lineDeterminedAt_of_stepResults_ne footprint writeDetMaskedLine
    plusTwoPE (writeDetState writeDetFilesA) (writeDetState writeDetFilesB) next next'
    ⟨.lm1, ⟨0, by decide⟩⟩ agree step step' different

/-- **`PlusTwoWriteDetermination` fails once the witness line steps twice.** -/
theorem not_plusTwoWriteDetermination_of_counterexampleSteps
    (steps : WriteDeterminationCounterexampleSteps) :
    ¬ PlusTwoWriteDetermination :=
  fun determination =>
    no_footprint_determines_witness_line steps plusTwoLineFootprint
      (determination writeDetMaskedLine)


/-! ## 6. What is discharged, and the exact residual

**Discharged here, without hypotheses.**

* Every `nop` line (`nop_lineDeterminedAt`) and every `mv` line
  (`mv_lineDeterminedAt`) satisfies `LineDeterminedAt` at *any* footprint; both
  leave the PE register files untouched.
* Every `.pe` line whose rows are all inert (`pe_inert_lineDeterminedAt`), and
  in particular the empty `.pe` line (`pe_nil_lineDeterminedAt`), satisfies
  `LineDeterminedAt` at any footprint.

**Refuted.**

* `PlusTwoWriteDetermination` is not a theorem for general `.pe` lines.  The
  blocked channel is the OPE **mask-register file**
  (`IntegerRegisterFiles.maskRegisters`): §3 exhibits two register files that
  agree on every `WordRef` yet prepare different write lists and commit
  different words.  `WordRef` has no mask-register bank, so **no** extension of
  `plusTwoLineFootprint` inside `Set WordRef` can cover this channel.
  The same gap arises for the other non-bank channels of the `.pe` step:
  * the forwarding slots (`stateForwardingSlots`, read by `.forward` sources),
  * the matrix store (`state.matrixRegisters`, read by `.matrixRead` rows),
  * the mask directive (`state.maskDirective`, the multiline selection of
    unmasked destinations),
  * the BAR/T context (`state.peContext`, used in address lowering), and
  * the hazard clock (`state.hazardClock`, used for mask-cycle selection),
  each of which is a `State` field outside `peRegisters` and outside `WordRef`,
  so none of them can be named by a richer `Set WordRef`-valued footprint.

**The exact remaining premise for a full refutation.**

`WriteDeterminationCounterexampleSteps`: the witness masked line must take one
successful step at each of the two witness states.  This is not a semantic gap
— the executor's mask resolvers are total and the producer has no source
operands — but it is an executor-existence fact of the same weight as the
`4096`-PE walk obligations the rest of the project states as `Prop`s.  Given it,
`not_plusTwoWriteDetermination_of_counterexampleSteps` proves
`¬ PlusTwoWriteDetermination` in full.

**Consequence for the kernel.**  A channel-aware contract is required, e.g. one
that additionally assumes equality of `maskRegisters`, `stateForwardingSlots`,
the matrix store, `maskDirective`, `peContext` and `hazardClock` between the two
states.  `plusTwo_output_forces_footprint_meets` remains valid for such a
contract but cannot be re-derived from `plusTwoLineFootprint` alone. -/

end ProofsLean.MNCore
