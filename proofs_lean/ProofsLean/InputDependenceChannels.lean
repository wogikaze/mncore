import ProofsLean.WriteDetermination

/-! # Channel-aware input dependence for the PE-memory floor arguments

`ProofsLean/WriteDetermination.lean` machine-checks that the bank-word contract of
`ProofsLean/InputDependence.lean`,

```
PlusTwoWriteDetermination := ∀ line, LineDeterminedAt plusTwoLineFootprint plusTwoPE line
```

is **false** as stated: the committed write list of a `.pe` line depends on state
channels that are not `WordRef`s (the OPE mask-register file, the forwarding
slots, the matrix register store, the mask directive, the BAR/T context and the
hazard clock), and `wordValue` projects only the five bank words.

This module builds the **channel-aware** replacement and re-derives the whole
program chain for it.

## 1. The channels

`stateChannels pe s` collects the six non-bank channels a `.pe` step at PE `pe`
reads:

* `stateForwardingSlots s pe` — the per-PE forwarding slots (payloads masked by
  their validity bits, exactly what every source read consults);
* `(s.peRegisters pe).maskRegisters` — the PE's OPE/OMR mask-register file;
* the matrix register bank at the three coordinates
  `(ParsedIntegerContext.ofLinearIndex pe).group/l2b/l1b` that the PE's
  `matrixRead` rows address;
* `s.maskDirective` — the current multiline mask selection;
* `s.peContext pe` — the BAR/T address-lowering context;
* `s.hazardClock` — the scored issue clock.

`ChanAgree pe s s'` is equality of that whole tuple.  It implies equality of the
bank-word-free data every executor read at `pe` consults, so the mask-register
witness of `WriteDetermination.lean` §3 (`writeDetFilesA` vs `writeDetFilesB`) is
**rejected** by the new hypothesis (`writeDetChan_disagree`), which is exactly
what a repaired contract has to do.

## 2. The contract

```
LineDeterminedAtChan footprint pe line :=
  ∀ s s' next next',
    FilesAgreeOn (footprint line s ∪ footprint line s') (s.peRegisters pe) (s'.peRegisters pe) →
    ChanAgree pe s s' →
    StepTo line s next → StepTo line s' next' →
    ∃ writes, CommitsWrites pe s next writes ∧ CommitsWrites pe s' next' writes ∧
      ChanAgree pe next next'
```

The bank-word part is the old hypothesis; the `ChanAgree` part is the channel
the footprint cannot name.  The **conclusion** additionally records that the two
runs still agree on the channels: without that the contract could not be used
for the *next* line of the program, whose own step reads the channels the
current line has just updated.

## 3. The chain (§3)

`execute_agreeOutside_of_determined_chan` re-proves the lock-step induction for
the new contract (agreement on `Dᶜ` **and** on the channels is preserved by every
line), and `exists_footprint_meets_of_output_ne_chan` is the contrapositive: a
different output word forces some line's footprint to meet `D`.

## 4. The `2.plus-two` application (§4)

`plusTwo_output_forces_footprint_meets_chan` and
`plusTwo_not_correct_of_footprint_avoids_chan` re-derive the input-parametric
reduction at the new contract.  The plus-two initial states agree on every
channel (`plusTwoInitialState_chanAgree`) because they differ only in `LM0`.

## 5. Per-line obligations (§5-§9)

* `.nop` — **discharged** (`nop_lineDeterminedAtChan`): the only channel it moves
  is the hazard clock, by the line's own cost (`nop_step_channels`).
* `.mv` — **discharged** (`mv_lineDeterminedAtChan`): it stages block-memory
  writes and advances the clock; no channel at the observed PE changes except the
  clock (`mv_step_channels`, `executeParsedMvMemory_channels`).
* inert `.pe` (`.noforward`, non-pending `.wait`, shared-block `.l1bm`) — the
  **write-list half is discharged** (`inert_pe_commitsWrites_nil`: the commit is
  `[]` at every PE), leaving only the channel frame
  (`inert_pe_lineDeterminedAtChan_of_frame`).
* plain-ALU `.pe` — **reduced** (`plain_pe_lineDeterminedAtChan_of_prepared`) to
  the executor's own prepared write list.  The proof performs the whole executor
  bridge (`executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists` for
  the `4096`-PE walk and the `next`-state shape,
  `executeIntegerProducerLineAtPEs_prepared` to pin the observed PE's file to the
  commit of its own `welcomeIntegerPrep` list).  The two residuals it names are
  exactly the executor obligations left:

  * `PEPreparedListCongruent footprint expressions` — the prepared write list is
    a function of the channels plus the footprint words.  This is
    `prepareParsedMaskedWriteWithForwarding_congr_of_agree` lifted over four
    cycles, the expression list and the family dispatch of
    `prepareParsedIntegerMatrixReadLineCycles`;
  * `PEChannelFrame pe line` — the two successor states still agree on the
    channels.  It is discharged for `nop`, `mv` (`nop_channelFrame`,
    `mv_channelFrame`); for `.pe` it is the walk's frame obligation.

  Neither residual is an axiom: both are hypotheses of a conditional theorem, and
  both are true for any footprint that covers the preparation's read regions.

## 6. The old counterexample is excluded (§7, §9, §6)

`writeDetCounterexample_not_chanAgree` proves the two witness states of
`WriteDetermination.lean` §3 — which agree on *every* `WordRef` — **disagree**
on the mask-register channel, so the new hypothesis rejects them
(`writeDetCounterexample_excluded`).  `writeDetMaskedLine_lineDeterminedAtChan_of_prepared`
applies the plain-ALU reduction to that very line.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

open Issue
open PEMemory

/-! ## 1. The non-bank channels of one PE -/

/-- The six state channels a `.pe` step at one PE reads that are **not** bank
words, and which `WordRef`/`wordValue` therefore cannot name.

The forwarding component is `stateForwardingSlots` (payload masked by validity),
the matrix component is the single matrix bank the PE's own coordinates address,
and the context component is the PE's full BAR/T/coordinate record. -/
structure NonBankChannels where
  /-- Per-PE forwarding slots, with invalid payloads masked to poison. -/
  forwardingSlots : Forwarding.Slots
  /-- The PE's OPE/OMR mask-register file. -/
  maskRegisters : Masks.RegisterFile
  /-- The matrix register bank at the PE's group/L2B/L1B coordinates. -/
  matrix : ParsedMatrixReadStore
  /-- The current multiline mask directive. -/
  maskDirective : ParsedMaskDirective
  /-- The PE's BAR/T address-lowering context. -/
  context : ParsedIntegerContext
  /-- The scored issue-word clock. -/
  clock : Nat

/-- **The non-bank channel tuple of one PE of a state.** -/
def stateChannels (pe : PEId) (s : State) : NonBankChannels where
  forwardingSlots := stateForwardingSlots s pe
  maskRegisters := (s.peRegisters pe).maskRegisters
  matrix := s.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
    (ParsedIntegerContext.ofLinearIndex pe).l2b
    (ParsedIntegerContext.ofLinearIndex pe).l1b
  maskDirective := s.maskDirective
  context := s.peContext pe
  clock := s.hazardClock

/-- **Channel agreement at one PE.**  Two states agree on every non-bank channel
the PE's step consults.  This is the hypothesis the bank-word footprint cannot
supply. -/
def ChanAgree (pe : PEId) (s s' : State) : Prop := stateChannels pe s = stateChannels pe s'

/-! ### Projections -/

theorem chanAgree_forwardingSlots {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    stateForwardingSlots s pe = stateForwardingSlots s' pe :=
  congrArg NonBankChannels.forwardingSlots h

theorem chanAgree_maskRegisters {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    (s.peRegisters pe).maskRegisters = (s'.peRegisters pe).maskRegisters :=
  congrArg NonBankChannels.maskRegisters h

theorem chanAgree_matrix {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    s.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b =
      s'.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b :=
  congrArg NonBankChannels.matrix h

theorem chanAgree_maskDirective {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    s.maskDirective = s'.maskDirective :=
  congrArg NonBankChannels.maskDirective h

theorem chanAgree_context {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    s.peContext pe = s'.peContext pe :=
  congrArg NonBankChannels.context h

theorem chanAgree_clock {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    s.hazardClock = s'.hazardClock :=
  congrArg NonBankChannels.clock h

@[refl] theorem chanAgree_refl (pe : PEId) (s : State) : ChanAgree pe s s := rfl

theorem chanAgree_symm {pe : PEId} {s s' : State} (h : ChanAgree pe s s') :
    ChanAgree pe s' s := h.symm

theorem chanAgree_trans {pe : PEId} {s s' s'' : State}
    (h : ChanAgree pe s s') (h' : ChanAgree pe s' s'') : ChanAgree pe s s'' := h.trans h'


/-! ### Simp lemmas for channel-preserving state updates -/

theorem stateChannels_clock (pe : PEId) (s : State) (clock : Nat) :
    stateChannels pe { s with hazardClock := clock } =
      { stateChannels pe s with clock := clock } := rfl

theorem stateChannels_maskDirective (pe : PEId) (s : State)
    (directive : ParsedMaskDirective) :
    stateChannels pe { s with maskDirective := directive } =
      { stateChannels pe s with maskDirective := directive } := rfl

theorem stateChannels_peRegisters (pe : PEId) (s : State)
    (registers : PEId → IntegerRegisterFiles) :
    stateChannels pe { s with peRegisters := registers } =
      { stateChannels pe s with
        maskRegisters := (registers pe).maskRegisters } := rfl

theorem stateChannels_peContext (pe : PEId) (s : State)
    (context : PEId → ParsedIntegerContext) :
    stateChannels pe { s with peContext := context } =
      { stateChannels pe s with context := context pe } := rfl

theorem stateChannels_matrixRegisters (pe : PEId) (s : State)
    (matrix : Fin 4 → Fin 2 → Fin 8 → ParsedMatrixReadStore) :
    stateChannels pe { s with matrixRegisters := matrix } =
      { stateChannels pe s with
        matrix := matrix (ParsedIntegerContext.ofLinearIndex pe).group
          (ParsedIntegerContext.ofLinearIndex pe).l2b
          (ParsedIntegerContext.ofLinearIndex pe).l1b } := rfl

theorem stateChannels_forwardingValid (pe : PEId) (s : State)
    (valid : PEId → Forwarding.Unit → Fin 4 → Bool) :
    stateChannels pe { s with forwardingValid := valid } =
      { stateChannels pe s with
        forwardingSlots := fun unit cycle =>
          if valid pe unit cycle then s.forwarding pe unit cycle else .poison } := by
  unfold stateChannels stateForwardingSlots
  simp only [show ({ s with forwardingValid := valid } : State).forwarding =
      s.forwarding from rfl]

theorem stateChannels_forwarding (pe : PEId) (s : State)
    (payload : PEId → Forwarding.Slots) :
    stateChannels pe { s with forwarding := payload } =
      { stateChannels pe s with
        forwardingSlots := fun unit cycle =>
          if s.forwardingValid pe unit cycle then payload pe unit cycle else .poison } := rfl

/-- Agreement survives a common clock update. -/
theorem chanAgree_clock_update {pe : PEId} {s s' : State} (h : ChanAgree pe s s')
    {a b : Nat} (hab : a = b) :
    ChanAgree pe { s with hazardClock := a } { s' with hazardClock := b } := by
  subst hab
  show ({ stateChannels pe s with clock := a } : NonBankChannels) =
    { stateChannels pe s' with clock := a }
  rw [h]

/-! ## 2. The channel-aware contract -/

/-- **Per-line write determination at one PE, channel-aware.**  Two states that
agree on the line's read footprint **and** on every non-bank channel the PE's
step consults both commit the *same* write list to `pe`, and still agree on the
channels afterwards.

The first hypothesis is the old bank-word hypothesis of
`ProofsLean/InputDependence.lean`; `ChanAgree` is the channel the footprint
cannot name (mask registers, forwarding slots, matrix store, mask directive,
BAR/T context, hazard clock); the conclusion's `ChanAgree` is what makes the
contract composable over a program. -/
def LineDeterminedAtChan (footprint : InstructionLine → State → Set WordRef)
    (pe : PEId) (line : InstructionLine) : Prop :=
  ∀ (s s' next next' : State),
    FilesAgreeOn (footprint line s ∪ footprint line s')
      (s.peRegisters pe) (s'.peRegisters pe) →
    ChanAgree pe s s' →
    StepTo line s next → StepTo line s' next' →
    ∃ writes : List PreparedParsedMaskedWrite,
      CommitsWrites pe s next writes ∧ CommitsWrites pe s' next' writes ∧
        ChanAgree pe next next'

/-- Channel-aware determination at a fixed observed PE, uniformly in the line. -/
def LineDeterminedChan (footprint : InstructionLine → State → Set WordRef)
    (pe : PEId) : Prop := ∀ line, LineDeterminedAtChan footprint pe line

/-! ## 3. The program chain for the channel-aware contract -/

/-- **The program chain.**  If every line of a program is channel-aware
write-determined and no line's footprint meets the difference set `D`, then two
executions from states that agree outside `D` *and* agree on the channels end
agreeing outside `D` and on the channels.

The channel part of the invariant is preserved line by line because the contract
concludes `ChanAgree` for the two successor states. -/
theorem execute_agreeOutside_of_determined_chan
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (pe : PEId) (D : Set WordRef)
    (determined : ∀ line ∈ program, LineDeterminedAtChan footprint pe line)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ Dᶜ)
    (s0 s0' : State) (hInit : FilesAgreeOn Dᶜ (s0.peRegisters pe) (s0'.peRegisters pe))
    (hChan : ChanAgree pe s0 s0')
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program s0 = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program s0' = some final') :
    FilesAgreeOn Dᶜ (final.peRegisters pe) (final'.peRegisters pe) ∧
      ChanAgree pe final final' := by
  induction program generalizing s0 s0' with
  | nil =>
      simp only [ProofsLean.execute] at run run'
      have same : final = s0 := (Option.some.inj run).symm
      have same' : final' = s0' := (Option.some.inj run').symm
      rw [same, same']
      exact ⟨hInit, hChan⟩
  | cons line rest ih =>
      rw [ProofsLean.execute.eq_2] at run run'
      cases hstep : plusTwoSealedMachine.step line s0 with
      | none => rw [hstep] at run; simp at run
      | some middle =>
          rw [hstep] at run
          simp only [Option.bind_some] at run
          cases hstep' : plusTwoSealedMachine.step line s0' with
          | none => rw [hstep'] at run'; simp at run'
          | some middle' =>
              rw [hstep'] at run'
              simp only [Option.bind_some] at run'
              have agrees : FilesAgreeOn (footprint line s0 ∪ footprint line s0')
                  (s0.peRegisters pe) (s0'.peRegisters pe) :=
                hInit.mono (avoids line (by simp) s0 s0')
              obtain ⟨writes, commit, commit', chan⟩ :=
                determined line (by simp) s0 s0' middle middle' agrees hChan hstep hstep'
              have hBank : FilesAgreeOn Dᶜ (middle.peRegisters pe)
                  (middle'.peRegisters pe) := by
                rw [commit, commit']
                exact commitParsedMaskedWrites_congr_on _ _ writes Dᶜ hInit
              exact ih (fun item mem => determined item (List.mem_cons_of_mem _ mem))
                (fun item mem s s' => avoids item (List.mem_cons_of_mem _ mem) s s')
                middle middle' hBank chan run run'

/-- **The usable contrapositive.**  If two executions of the same program end
with different values at an observed word `w` outside the difference set `D`,
the initial states agreed outside `D` **and on every channel**, then some line of
the program has a read footprint that meets `D`.  A differing output can only
come from a line that read a differing input word; the channels cannot explain
it away any more. -/
theorem exists_footprint_meets_of_output_ne_chan
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (pe : PEId) (D : Set WordRef)
    (determined : ∀ line ∈ program, LineDeterminedAtChan footprint pe line)
    (s0 s0' : State) (hInit : FilesAgreeOn Dᶜ (s0.peRegisters pe) (s0'.peRegisters pe))
    (hChan : ChanAgree pe s0 s0')
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program s0 = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program s0' = some final')
    (w : WordRef) (hw : w ∉ D)
    (different : wordValue (final.peRegisters pe) w ≠
      wordValue (final'.peRegisters pe) w) :
    ∃ line ∈ program, ∃ s s' : State, ∃ v : WordRef,
      v ∈ D ∧ (v ∈ footprint line s ∨ v ∈ footprint line s') := by
  by_contra none
  have avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ Dᶜ := by
    intro line mem s s' v hv
    by_contra outside
    exact none ⟨line, mem, s, s', v, by simpa using outside, hv⟩
  obtain ⟨bank, chan⟩ := execute_agreeOutside_of_determined_chan footprint program pe D
    determined avoids s0 s0' hInit hChan final final' run run'
  exact different (bank w hw)


/-! ## 4. The `2.plus-two` application at the channel-aware contract

The two initial states of `2.plus-two` differ only in `LM0`, so they agree on
every non-bank channel.  The whole input-parametric reduction therefore carries
over unchanged: a correct program must contain, for every `j`, a line whose read
footprint (bank words) meets the LM0 word of input `j`. -/

/-- **The plus-two initial states agree on every channel.**  They differ only in
the `LM0` bank of `peRegisters`, which no channel projects. -/
theorem plusTwoInitialState_chanAgree (input input' : PlusTwoWords) (pe : PEId) :
    ChanAgree pe (plusTwoInitialState input) (plusTwoInitialState input') := by
  show stateChannels pe (plusTwoInitialState input) =
    stateChannels pe (plusTwoInitialState input')
  unfold stateChannels plusTwoInitialState plusTwoInitialPERegisters
    rustSimulatorInitialState stateForwardingSlots
  rfl

/-- **The chain instantiated at `2.plus-two`.**  If every line of a program is
channel-aware write-determined on a footprint that avoids the input word of `j`,
then two inputs differing only at `j` produce the same PE-0 register words (and
still agree on the channels). -/
theorem plusTwo_execute_agreeOutside_chan
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (j : Fin 20)
    (determined : ∀ line ∈ program, LineDeterminedAtChan footprint plusTwoPE line)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ ({plusTwoInputWord j} : Set WordRef)ᶜ)
    (input input' : PlusTwoWords) (agree : ∀ k, k ≠ j → input k = input' k)
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program
      (plusTwoSpec.initial input) = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program
      (plusTwoSpec.initial input') = some final') :
    FilesAgreeOn ({plusTwoInputWord j} : Set WordRef)ᶜ
      (final.peRegisters plusTwoPE) (final'.peRegisters plusTwoPE) ∧
      ChanAgree plusTwoPE final final' :=
  execute_agreeOutside_of_determined_chan footprint program plusTwoPE
    ({plusTwoInputWord j} : Set WordRef) determined avoids
    (plusTwoSpec.initial input) (plusTwoSpec.initial input')
    (plusTwoInitialPERegisters_agree_outside input input' j agree)
    (by
      rw [plusTwoSpec_initial, plusTwoSpec_initial]
      exact plusTwoInitialState_chanAgree input input' plusTwoPE)
    final final' run run'

/-- **The headline reduction at the channel-aware contract.**  A correct
`2.plus-two` program needs, for every input index `j`, a line whose read
footprint contains the LM0 word of input `j`.  The channel hypothesis is
discharged at the two initial states, so the reduction is unconditional in the
channels. -/
theorem plusTwo_output_forces_footprint_meets_chan
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAtChan footprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ footprint line s ∨ plusTwoInputWord j ∈ footprint line s' := by
  let zeroInput : PlusTwoWords := fun _ => 0
  let oneInput : PlusTwoWords := fun k => if k = j then 1 else 0
  have zeroAdmissible : plusTwoSpec.admissible zeroInput := by
    intro k
    simp [zeroInput]
  have oneAdmissible : plusTwoSpec.admissible oneInput := by
    intro k
    by_cases isJ : k = j
    · simp [oneInput, isJ]
    · simp [oneInput, isJ]
  have agree : ∀ k, k ≠ j → zeroInput k = oneInput k := by
    intro k other
    simp [zeroInput, oneInput, other]
  obtain ⟨final, run, post⟩ := correct.2 zeroInput zeroAdmissible
  obtain ⟨final', run', post'⟩ := correct.2 oneInput oneAdmissible
  have initialAgree : FilesAgreeOn ({plusTwoInputWord j} : Set WordRef)ᶜ
      ((plusTwoSpec.initial zeroInput).peRegisters plusTwoPE)
      ((plusTwoSpec.initial oneInput).peRegisters plusTwoPE) :=
    plusTwoInitialPERegisters_agree_outside zeroInput oneInput j agree
  have initialChan : ChanAgree plusTwoPE (plusTwoSpec.initial zeroInput)
      (plusTwoSpec.initial oneInput) := by
    rw [plusTwoSpec_initial, plusTwoSpec_initial]
    exact plusTwoInitialState_chanAgree zeroInput oneInput plusTwoPE
  have different : wordValue (final.peRegisters plusTwoPE) (plusTwoOutputWord j) ≠
      wordValue (final'.peRegisters plusTwoPE) (plusTwoOutputWord j) := by
    have low := (post j).2
    have low' := (post' j).2
    simp only [plusTwoOutputWord, wordValue_lm1]
    rw [low, low']
    simp [zeroInput, oneInput]
  have outside : plusTwoOutputWord j ∉ ({plusTwoInputWord j} : Set WordRef) := by
    intro mem
    have same := Set.mem_singleton_iff.mp mem
    exact plusTwoOutputWord_not_inputWord j same
  obtain ⟨line, mem, s, s', v, inD, inFootprint⟩ :=
    exists_footprint_meets_of_output_ne_chan footprint program plusTwoPE
      ({plusTwoInputWord j} : Set WordRef) determined
      (plusTwoSpec.initial zeroInput) (plusTwoSpec.initial oneInput)
      initialAgree initialChan final final' run run' (plusTwoOutputWord j) outside different
  have vSame : v = plusTwoInputWord j := Set.mem_singleton_iff.mp inD
  subst vSame
  exact ⟨line, mem, s, s', inFootprint⟩

/-- **A program that never reads input `j` is incorrect**, at the channel-aware
contract: every correct `2.plus-two` program must contain, for every index `j`, a
line whose read footprint contains the LM0 word of input `j`. -/
theorem plusTwo_not_correct_of_footprint_avoids_chan
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAtChan footprint plusTwoPE line)
    (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ footprint line s ∧
        plusTwoInputWord j ∉ footprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program := by
  intro correct
  obtain ⟨line, mem, s, s', meets⟩ :=
    plusTwo_output_forces_footprint_meets_chan footprint program determined correct j
  rcases meets with inside | inside
  · exact (avoids line mem s s').1 inside
  · exact (avoids line mem s s').2 inside


/-! ## 5. Per-line obligations

### 5.1 `.nop`

A `nop` line only advances the hazard clock, by its own cost, and touches no
channel. -/

/-- **The `nop` step is a clock update.** -/
theorem nop_step_channels (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (pe : PEId) (state next : State) (step : StepTo (.nop count wait) state next) :
    stateChannels pe next =
      { stateChannels pe state with clock := state.hazardClock + count.val } := by
  have executed := stepTo_nop count wait state next step
  obtain ⟨c, hval⟩ : ∃ c, count.val = c + 1 := ⟨count.val - 1, by have := count.property; omega⟩
  rw [hval] at executed ⊢
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  cases wait with
  | none =>
      have accepted : checkParsedTopLine (.nop (c + 1) none) = true :=
        executeIntegerProducerInstructionLine_accepted_of_ok
          (.nop ⟨c + 1, by omega⟩ none) state next executed
      rw [executeIntegerProducerInstructionLine_nop ⟨c + 1, by omega⟩ none state accepted rfl]
        at executed
      simp only [StepResult.ok.injEq] at executed
      rw [← executed, stateChannels_clock]
  | some tag =>
      cases hcomp : state.mvCompletedTags tag with
      | false =>
          rw [show executeIntegerProducerInstructionLine
              (.nop ⟨c + 1, by omega⟩ (some tag)) state = .unknown from
            executeIntegerProducerInstructionLine_wait_pending_unknown
              ⟨c + 1, by omega⟩ tag state
              (executeIntegerProducerInstructionLine_accepted_of_ok
                (.nop ⟨c + 1, by omega⟩ (some tag)) state next executed) hcomp]
            at executed
          simp at executed
      | true =>
          rw [executeIntegerProducerInstructionLine_wait_completed
            ⟨c + 1, by omega⟩ tag state
            (executeIntegerProducerInstructionLine_accepted_of_ok
              (.nop ⟨c + 1, by omega⟩ (some tag)) state next executed) hcomp] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [← executed, stateChannels_clock]

/-- **`nop` lines satisfy the channel-aware contract** at any footprint. -/
theorem nop_lineDeterminedAtChan (footprint : InstructionLine → State → Set WordRef)
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    LineDeterminedAtChan footprint plusTwoPE (.nop count wait) := by
  intro s s' next next' agree chan step step'
  refine ⟨[], ?_, ?_, ?_⟩
  · show next.peRegisters plusTwoPE = commitParsedMaskedWrites (s.peRegisters plusTwoPE) []
    rw [nop_step_peRegisters_frame count wait s next step, commitParsedMaskedWrites_nil]
  · show next'.peRegisters plusTwoPE = commitParsedMaskedWrites (s'.peRegisters plusTwoPE) []
    rw [nop_step_peRegisters_frame count wait s' next' step', commitParsedMaskedWrites_nil]
  · show stateChannels plusTwoPE next = stateChannels plusTwoPE next'
    rw [nop_step_channels count wait plusTwoPE s next step,
      nop_step_channels count wait plusTwoPE s' next' step', chan, chanAgree_clock chan]

/-! ### 5.2 `.mv`

An `mv` line stages block-memory writes and advances the clock by one; every
channel at the observed PE is untouched. -/

/-- `executeParsedMvMemory` leaves every channel untouched. -/
theorem executeParsedMvMemory_channels (pe : PEId) (state next : State)
    (transfer : ParsedMv) (executed : executeParsedMvMemory state transfer = .ok next) :
    stateChannels pe next = stateChannels pe state := by
  unfold executeParsedMvMemory at executed
  cases h : MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar transfer with
  | none => rw [h] at executed; simp at executed
  | some writes =>
      rw [h] at executed
      dsimp only at executed
      by_cases isNop : transfer.kind == .nop
      · rw [ite_eq_left isNop] at executed
        cases executed
        rfl
      · rw [ite_eq_right isNop] at executed
        cases executed
        rfl

/-- **The `mv` step is a unit clock update** (with the block-memory staging
invisible to every channel). -/
theorem mv_step_channels (transfer : NormalizedMv) (pe : PEId) (state next : State)
    (step : StepTo (.mv transfer) state next) :
    stateChannels pe next =
      { stateChannels pe state with clock := state.hazardClock + 1 } := by
  have executed := stepTo_mv transfer state next step
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.mv transfer) state next executed
  by_cases isNop : transfer.kind == .nop
  · have isNopProp : transfer.kind = .nop := by simpa using isNop
    rw [executeIntegerProducerInstructionLine_mvnop transfer state isNopProp accepted] at executed
    simp only [StepResult.ok.injEq] at executed
    rw [← executed, stateChannels_clock]
  · have notNop : transfer.kind ≠ .nop := by simpa using isNop
    cases memory : executeParsedMvMemory state transfer.toParsed with
    | failure =>
        simp [executeIntegerProducerInstructionLine, accepted, isNop, memory] at executed
    | unknown =>
        simp [executeIntegerProducerInstructionLine, accepted, isNop, memory] at executed
    | ok middle =>
        rw [executeIntegerProducerInstructionLine_mv_transfer_success transfer state middle
          accepted notNop memory] at executed
        simp only [StepResult.ok.injEq] at executed
        rw [← executed, stateChannels_clock]
        have channels := executeParsedMvMemory_channels pe state middle transfer.toParsed memory
        rw [channels]
        have hclock : middle.hazardClock = state.hazardClock :=
          congrArg NonBankChannels.clock channels
        rw [hclock]

/-- **`mv` lines satisfy the channel-aware contract** at any footprint. -/
theorem mv_lineDeterminedAtChan (footprint : InstructionLine → State → Set WordRef)
    (transfer : NormalizedMv) :
    LineDeterminedAtChan footprint plusTwoPE (.mv transfer) := by
  intro s s' next next' agree chan step step'
  refine ⟨[], ?_, ?_, ?_⟩
  · show next.peRegisters plusTwoPE = commitParsedMaskedWrites (s.peRegisters plusTwoPE) []
    rw [executeNormalizedLine_mv_peRegisters transfer s next
        (by simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using
          stepTo_mv transfer s next step),
      commitParsedMaskedWrites_nil]
  · show next'.peRegisters plusTwoPE = commitParsedMaskedWrites (s'.peRegisters plusTwoPE) []
    rw [executeNormalizedLine_mv_peRegisters transfer s' next'
        (by simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using
          stepTo_mv transfer s' next' step'),
      commitParsedMaskedWrites_nil]
  · show stateChannels plusTwoPE next = stateChannels plusTwoPE next'
    rw [mv_step_channels transfer plusTwoPE s next step,
      mv_step_channels transfer plusTwoPE s' next' step', chan, chanAgree_clock chan]


/-! ## 6. The `.pe` constructor: reduction to the executor's prepared write list

A `.pe` line's committed write list at the observed PE is the executor's own
preparation list (`executeIntegerProducerLineAtPEs_prepared`), so determination
of the line reduces to determination of that *prepared list* — the state-general
executor obligation `PEPreparedListCongruent` — plus the channel frame
`PEChannelFrame`.  The reduction below performs the whole executor bridge (the
`4096`-PE walk, the plain-ALU stage identities, and the `next`-state shape); no
part of the `.pe` executor is assumed away. -/

/-- The expression list the per-PE walk is handed for a `.pe` line. -/
def peWalkExpressions (expressions : List NormalizedExpr) : List ParsedExpr :=
  expressions.map NormalizedExpr.toParsed

/-- **The prepared-list congruence residual.**  For a fixed line, two states that
agree on the non-bank channels *and* on the line's bank-word footprint prepare
the **same** write list at the observed PE.

This is exactly the executor read-locality fact that
`ProofsLean/InputDependence.lean` §3 proves for a *single* prepared write
(`prepareParsedMaskedWriteWithForwarding_congr_of_agree`): it has to be lifted
over the line's four cycles, its expression list and the family dispatch of
`prepareParsedIntegerMatrixReadLineCycles`.  The footprint is part of the
hypothesis because the prepared writes read their source operands through it. -/
def PEPreparedListCongruent (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr) : Prop :=
  ∀ (s s' : State) (w w' : List PreparedParsedMaskedWrite)
      (slots slots' : Forwarding.Slots) (bars bars' : List (Bool × BitVec 12)),
    ChanAgree plusTwoPE s s' →
    FilesAgreeOn (footprint (.pe expressions) s ∪ footprint (.pe expressions) s')
      (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE) →
    welcomeIntegerPrep s plusTwoPE (peWalkExpressions expressions) = .ok (w, slots, bars) →
    welcomeIntegerPrep s' plusTwoPE (peWalkExpressions expressions) = .ok (w', slots', bars') →
    w = w'

/-- **The channel frame residual.**  A line's two successful steps keep the
channels agreed.  `nop` and `mv` discharge it unconditionally
(`nop_lineDeterminedAtChan`, `mv_lineDeterminedAtChan`); for a `.pe` line it is
the executor frame obligation for the walk, the special-ALU stages and the
per-PE forwarding/context updates. -/
def PEChannelFrame (pe : PEId) (line : InstructionLine) : Prop :=
  ∀ (s s' next next' : State), ChanAgree pe s s' →
    StepTo line s next → StepTo line s' next' → ChanAgree pe next next'

/-- **The `.pe` reduction for plain-ALU lines.**  Given the prepared-list
congruence and the channel frame, a `.pe` line all of whose rows are plain
integer ALU rows satisfies the channel-aware contract at *any* footprint.

The proof is the executor bridge: `executeIntegerProducerInstructionLine_pe_
plainIntegerALU_exists` exposes the walk and the `next`-state shape (only the
hazard clock and the turnaround validity flag change after the walk), and
`executeIntegerProducerLineAtPEs_prepared` pins the observed PE's file to the
commit of its own `welcomeIntegerPrep` list. -/
theorem plain_pe_lineDeterminedAtChan_of_prepared
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (prepared : PEPreparedListCongruent footprint expressions)
    (frame : PEChannelFrame plusTwoPE (.pe expressions)) :
    LineDeterminedAtChan footprint plusTwoPE (.pe expressions) := by
  intro s s' next next' agree chan step step'
  have executed := stepTo_pe expressions s next step
  have executed' := stepTo_pe expressions s' next' step'
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s next executed
  have accepted' := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s' next' executed'
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s next
      accepted plain executed
  obtain ⟨nextPEs', walk', nextEq'⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s' next'
      accepted' plain executed'
  rw [plain_peFilter_eq_self (expressions.map NormalizedExpr.toParsed) plain] at walk walk'
  have floatEmpty := plain_floatFilter_eq_nil (expressions.map NormalizedExpr.toParsed) plain
  obtain ⟨w, slots, bars, prep, commit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (peWalkExpressions expressions)
      (List.finRange 4096) s nextPEs floatEmpty walk (List.nodup_finRange 4096)
      plusTwoPE (by simp [plusTwoPE, welcomePE])
  obtain ⟨w', slots', bars', prep', commit'⟩ :=
    executeIntegerProducerLineAtPEs_prepared (peWalkExpressions expressions)
      (List.finRange 4096) s' nextPEs' floatEmpty walk' (List.nodup_finRange 4096)
      plusTwoPE (by simp [plusTwoPE, welcomePE])
  have same : w = w' := prepared s s' w w' slots slots' bars bars' chan agree prep prep'
  refine ⟨w, ?_, ?_, frame s s' next next' chan step step'⟩
  · show next.peRegisters plusTwoPE = commitParsedMaskedWrites (s.peRegisters plusTwoPE) w
    rw [nextEq]
    exact commit
  · show next'.peRegisters plusTwoPE = commitParsedMaskedWrites (s'.peRegisters plusTwoPE) w
    rw [nextEq', same]
    exact commit'

/-! ## 7. The new contract excludes the old counterexample

`WriteDetermination.lean` §3 refutes the old contract with two register files
that agree on every bank word but differ in their **mask-register file**.  The
new contract's `ChanAgree` hypothesis is *false* for that pair, which is exactly
why the refutation does not apply any more. -/

theorem writeDetState_peRegisters_files (files : IntegerRegisterFiles) :
    (writeDetState files).peRegisters plusTwoPE = files := rfl

/-- **The old counterexample pair violates the channel hypothesis.** -/
theorem writeDetCounterexample_not_chanAgree :
    ¬ ChanAgree plusTwoPE (writeDetState writeDetFilesA) (writeDetState writeDetFilesB) := by
  intro agree
  exact writeDetFiles_maskRegisters_ne (chanAgree_maskRegisters agree)

/-- The same exclusion in the shape the old refutation used: the two witness
states agree on *every* bank word (`writeDetFiles_agree`), so the old contract's
hypothesis holds at every footprint, while the new contract's channel hypothesis
fails.  A channel-aware contract is therefore not refuted by the witness, and no
`Set WordRef`-valued footprint can substitute for the channels. -/
theorem writeDetCounterexample_excluded :
    (∀ (footprint : InstructionLine → State → Set WordRef),
      FilesAgreeOn (footprint writeDetMaskedLine (writeDetState writeDetFilesA) ∪
          footprint writeDetMaskedLine (writeDetState writeDetFilesB))
        ((writeDetState writeDetFilesA).peRegisters plusTwoPE)
        ((writeDetState writeDetFilesB).peRegisters plusTwoPE)) ∧
      ¬ ChanAgree plusTwoPE (writeDetState writeDetFilesA) (writeDetState writeDetFilesB) := by
  refine ⟨?_, writeDetCounterexample_not_chanAgree⟩
  intro footprint
  exact fun w _ => writeDetFiles_agree w (Set.mem_univ w)


/-! ## 8. Channel frames for the discharged line classes

`PEChannelFrame` is stated as a separate obligation so that the `.pe` reduction
of §6 can name it; for `nop`, `mv` and inert `.pe` lines it is an immediate
corollary of the step shapes proved in §5 and §9. -/

theorem nop_channelFrame (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    PEChannelFrame plusTwoPE (.nop count wait) := by
  intro s s' next next' chan step step'
  show stateChannels plusTwoPE next = stateChannels plusTwoPE next'
  rw [nop_step_channels count wait plusTwoPE s next step,
    nop_step_channels count wait plusTwoPE s' next' step', chan, chanAgree_clock chan]

theorem mv_channelFrame (transfer : NormalizedMv) :
    PEChannelFrame plusTwoPE (.mv transfer) := by
  intro s s' next next' chan step step'
  show stateChannels plusTwoPE next = stateChannels plusTwoPE next'
  rw [mv_step_channels transfer plusTwoPE s next step,
    mv_step_channels transfer plusTwoPE s' next' step', chan, chanAgree_clock chan]

/-! ## 9. Inert `.pe` lines: the write-list half is discharged

For a `.pe` line all of whose rows are PE-inert (`.noforward`, non-pending
`.wait`, and the five shared-block `.l1bm` forms), the committed write list is
literally `[]` at every PE, so the write-list half of the contract holds
unconditionally.  Only the channel frame remains, and it is the single named
obligation of §6. -/

/-- An inert `.pe` line commits the empty write list to every PE. -/
theorem inert_pe_commitsWrites_nil (expressions : List NormalizedExpr) (state next : State)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)
    (step : StepTo (.pe expressions) state next) :
    CommitsWrites plusTwoPE state next [] := by
  show next.peRegisters plusTwoPE =
    commitParsedMaskedWrites (state.peRegisters plusTwoPE) []
  rw [pe_inert_step_peRegisters_frame expressions state next all step,
    commitParsedMaskedWrites_nil]

/-- **Inert `.pe` lines satisfy the channel-aware contract as soon as the channel
frame holds.**  The write-list obligation is discharged here, unconditionally. -/
theorem inert_pe_lineDeterminedAtChan_of_frame
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)
    (frame : PEChannelFrame plusTwoPE (.pe expressions)) :
    LineDeterminedAtChan footprint plusTwoPE (.pe expressions) := by
  intro s s' next next' _agree _chan step step'
  exact ⟨[], inert_pe_commitsWrites_nil expressions s next all step,
    inert_pe_commitsWrites_nil expressions s' next' all step',
    frame s s' next next' _chan step step'⟩

/-- The empty `.pe` line is inert. -/
theorem pe_nil_lineDeterminedAtChan_of_frame
    (footprint : InstructionLine → State → Set WordRef)
    (frame : PEChannelFrame plusTwoPE (.pe [])) :
    LineDeterminedAtChan footprint plusTwoPE (.pe []) :=
  inert_pe_lineDeterminedAtChan_of_frame footprint []
    (by intro expression member; simp at member) frame

/-! ## 10. Concrete-footprint corollaries

The concrete hazard-event footprint of `ProofsLean/InputDependence.lean` is
still a valid instance of the channel-aware contract; what changed is that the
per-line obligation now also asks for the channels. -/

/-- **The headline reduction at the concrete footprint and the new contract.**
A correct `2.plus-two` program has, for every input index `j`, a line whose
concrete read footprint (the hazard-event lowering of its sources) contains the
LM0 word of input `j`. -/
theorem plusTwo_output_forces_concrete_read_chan
    (program : List InstructionLine)
    (determined : ∀ line ∈ program,
      LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ plusTwoLineFootprint line s ∨
        plusTwoInputWord j ∈ plusTwoLineFootprint line s' :=
  plusTwo_output_forces_footprint_meets_chan plusTwoLineFootprint program determined correct j

/-- **A program that never reads input `j` is incorrect**, at the concrete
footprint and the channel-aware contract. -/
theorem plusTwo_not_correct_of_concrete_footprint_avoids_chan
    (program : List InstructionLine)
    (determined : ∀ line ∈ program,
      LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line)
    (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ plusTwoLineFootprint line s ∧
        plusTwoInputWord j ∉ plusTwoLineFootprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program :=
  plusTwo_not_correct_of_footprint_avoids_chan plusTwoLineFootprint program determined j avoids


/-- **The witness line of `WriteDetermination.lean` is not a counterexample any
more.**  The masked constant producer that refutes the old contract is a plain
integer-ALU row, so the `.pe` reduction applies to it verbatim: its contract
obligation is exactly the two named executor residuals, and the mask-register
channel that refuted the old contract is part of `ChanAgree`. -/
theorem writeDetMaskedLine_lineDeterminedAtChan_of_prepared
    (footprint : InstructionLine → State → Set WordRef)
    (prepared : PEPreparedListCongruent footprint [writeDetMaskedNExpr])
    (frame : PEChannelFrame plusTwoPE writeDetMaskedLine) :
    LineDeterminedAtChan footprint plusTwoPE writeDetMaskedLine :=
  plain_pe_lineDeterminedAtChan_of_prepared footprint [writeDetMaskedNExpr]
    writeDetMaskedLine_plain prepared frame

end ProofsLean.MNCore
