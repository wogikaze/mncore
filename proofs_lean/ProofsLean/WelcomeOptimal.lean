import ProofsLean.WelcomeValue

/-! # Welcome optimality on a sealed whole-machine value model

`ProofsLean.MNCore.PlusOne.lean` proves correctness and two-line optimality in
a *source-level* two-line model that has only the two `iinc` line kinds. This
module replaces that model by the **whole-machine value semantics**:

* lines are `InstructionLine`s (the executable rows of the whole-machine
  semantics), and
* a step is exactly `executeNormalizedLine line.toNormalizedLine`, the value
  transition that `wholeMachine.step` invokes after its issue, address-mode and
  hazard-history checks.

The hazard-history layer, the `.unknown` sites and the issue/address-mode
checks of `wholeMachine.step` are **sealed away**. They are analysed
separately in `WelcomeValue.lean` (`welcomeExprEvents`, `welcome_no_peHazard`,
`welcome_blockEvents`), but this module does not claim
`ProofsLean.Optimal wholeMachine ...`. The machine below is therefore a
restricted (sealed) version of the whole-machine model; every theorem in this
file is stated about that machine and carries this restriction.

The restricted machine still has the full 4096-PE state, the real four-cycle
`.long` load/increment/store path, the issue checker, the mask directive, the
BAR context and the hazard clock. What is dropped is only the history-based
hazard rejection (and the `.failure`/`.unknown` distinction: a non-`.ok` value
transition is `none`).

## Results

* `welcomeAnswer_correct` — the two accepted `iinc` lines compute
  `n_i = m_i + 1` on all 16 LM1 words from the zero-initialised machine, for
  every admissible input (all 16 LM0 words in `0..50`).
* NOT PROVED HERE (and not implied by the theorem above): no lower bound and
  no `Optimal` theorem exists in this module. `welcomeAnswer_correct` is an
  upper bound only. The restricted one-line refutations live in
  `ProofsLean/WelcomeLowerBound.lean`; the unrestricted statement
  `LowerBound welcomeSealedMachine welcomeSpec 2` is still open, so
  `Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` is not claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- The single observed PE of the Welcome testcase (`n0c0b0m0p0`). -/
def welcomePE : PEId := ⟨0, by decide⟩

/-- Zero-initialised PE register file carrying the 16 input words in LM0. All
other PE memories (LM1, GRF, T and mask registers) are zero, matching
`Machine::new`. -/
def welcomeInitialPERegisters (input : ProofsLean.MNCore.PlusOne.Words) :
    IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with
    lm0 := fun address =>
      if h : address.val < 16 then input ⟨address.val, h⟩ else 0 }

/-- The initial whole-machine state of the Welcome problem: every PE carries
the same input words (the semantics is PE-uniform), the mask directive and BAR
contexts are the simulator defaults, and forwarding validity is false. -/
def welcomeInitialState (input : ProofsLean.MNCore.PlusOne.Words) : State :=
  { rustSimulatorInitialState with
    peRegisters := fun _ => welcomeInitialPERegisters input }

theorem welcomeInitialState_maskDirective (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialState input).maskDirective = welcomeMaskDirective := rfl

theorem welcomeInitialState_context (input : ProofsLean.MNCore.PlusOne.Words)
    (_pe : PEId) :
    (welcomeInitialState input).peContext _pe = ParsedIntegerContext.ofLinearIndex _pe := rfl

theorem welcomeInitialState_context_bar0 (input : ProofsLean.MNCore.PlusOne.Words)
    (pe : PEId) : ((welcomeInitialState input).peContext pe).bar0 = 0 := rfl

theorem welcomeInitialState_context_bar1 (input : ProofsLean.MNCore.PlusOne.Words)
    (pe : PEId) : ((welcomeInitialState input).peContext pe).bar1 = 0 := rfl

theorem welcomeInitialState_invariant (input : ProofsLean.MNCore.PlusOne.Words) :
    WelcomeStateInvariant (welcomeInitialState input) :=
  ⟨rfl, fun pe => ⟨rfl, rfl⟩⟩

theorem welcomeInitialPERegisters_lm0 (input : ProofsLean.MNCore.PlusOne.Words)
    (word : Fin 16) :
    (welcomeInitialPERegisters input).lm0
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      input word := by
  simp [welcomeInitialPERegisters, word.isLt]

theorem welcomeInitialState_lm0 (input : ProofsLean.MNCore.PlusOne.Words)
    (word : Fin 16) :
    ((welcomeInitialState input).peRegisters welcomePE).lm0
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      input word := by
  simpa [welcomeInitialState] using welcomeInitialPERegisters_lm0 input word

theorem welcomeInitialPERegisters_lm0_other (input : ProofsLean.MNCore.PlusOne.Words)
    (address : Fin Bank.lm0.capacity) (large : 16 ≤ address.val) :
    (welcomeInitialPERegisters input).lm0 address = 0 := by
  simp [welcomeInitialPERegisters, Nat.not_lt.mpr large]

/-- The sealed whole-machine value model: `Line` and `lineCost` are the
whole-machine ones, the state is the real `State`, and `step` is the value
transition `executeNormalizedLine` that `wholeMachine.step` invokes after its
checks. A non-`.ok` value transition becomes `none`. -/
noncomputable def welcomeSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := ProofsLean.MNCore.PlusOne.Words
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The Welcome problem: LM0 holds 16 words in `0..50`, LM1 starts zero, and
the observed PE's LM1 output word `i` must be the wrapping 32-bit successor of
input word `i`. -/
noncomputable def welcomeSpec : ProofsLean.Problem welcomeSealedMachine where
  admissible := fun input => ∀ i, (input i).toNat ≤ 50
  initial := welcomeInitialState
  post := fun input state => ∀ i : Fin 16,
    (state.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      input i + 1

/-- The two accepted Welcome lines of `problems/challenge/1.plus-one/answer.vsm`. -/
def welcomeAnswer : ProofsLean.Program welcomeSealedMachine :=
  [InstructionLine.pe [welcomeExpr 0], InstructionLine.pe [welcomeExpr 8]]

/-- One sealed step on a Welcome line: it succeeds, preserves the mask/BAR
invariant, and installs the committed increment writes at every PE. -/
theorem welcomeSealed_step (base : Nat) (state : State)
    (invariant : WelcomeStateInvariant state) :
    ∃ next,
      welcomeSealedMachine.step (InstructionLine.pe [welcomeExpr base]) state = some next ∧
      executeIntegerProducerInstructionLine (InstructionLine.pe [welcomeExpr base]) state =
        .ok next ∧
      WelcomeStateInvariant next ∧
      (∀ p : PEId,
        next.peRegisters p =
          commitParsedMaskedWrites (state.peRegisters p)
            [welcomePreparedWrite (state.peRegisters p) base 0,
             welcomePreparedWrite (state.peRegisters p) base 1,
             welcomePreparedWrite (state.peRegisters p) base 2,
             welcomePreparedWrite (state.peRegisters p) base 3]) := by
  obtain ⟨next, executed, nextInvariant⟩ :=
    welcome_executeIntegerProducerInstructionLine_success base state invariant
  have execEq : executeNormalizedLine
      (NormalizedLine.pe [welcomeExpr base]) state =
      executeIntegerProducerInstructionLine (InstructionLine.pe [welcomeExpr base]) state := rfl
  have stepEq : welcomeSealedMachine.step (InstructionLine.pe [welcomeExpr base]) state =
      some next := by
    show (match executeNormalizedLine (NormalizedLine.pe [welcomeExpr base]) state with
      | StepResult.ok next => some next
      | _ => none) = some next
    rw [execEq, executed]
  refine ⟨next, stepEq, executed, nextInvariant, ?_⟩
  intro p
  exact welcome_executeIntegerProducerInstructionLine_peRegisters base state next invariant
    executed p


/-- Start (even) word of the `.long` window containing `word`. -/
def welcomeWordLongStart (word : Fin 16) : Nat := 2 * (word.val / 2)

def welcomeWordLongAddress (word : Fin 16) : Fin Bank.lm1.capacity :=
  ⟨welcomeWordLongStart word, by
    have := word.isLt
    simp [welcomeWordLongStart]
    change 2 * (word.val / 2) < 4096
    omega⟩

def welcomeWordIndex (word : Fin 16) : Fin 4 :=
  ⟨word.val % 2, by have := word.isLt; omega⟩

theorem welcomeWordIndex_lt_two (word : Fin 16) : (welcomeWordIndex word).val < 2 := by
  simp [welcomeWordIndex]
  omega

theorem readDirectAccess_welcomeWord (files : IntegerRegisterFiles) (word : Fin 16) :
    readDirectAccess files ⟨.lm1, .long, welcomeWordLongAddress word⟩
      (welcomeWordIndex word) =
      files.lm1 ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ := by
  rw [readDirectAccess_lm1_long_word files (welcomeWordLongAddress word)
      (welcomeWordIndex word) (welcomeWordIndex_lt_two word)]
  congr 1
  apply Fin.ext
  simp [advance, welcomeWordLongAddress, welcomeWordLongStart, welcomeWordIndex,
    Bank.capacity]
  have := word.isLt
  omega

/-- Reading a word back from the four committed Welcome writes of line `base`
returns the increment of the corresponding LM0 input word. -/
theorem welcomeCommit_readback_word (files writeFiles : IntegerRegisterFiles)
    (base : Nat) (bounded : base = 0 ∨ base = 8) (word : Fin 16)
    (cycle : Fin 4) (index : Fin 4)
    (startEq : (welcomeDestinationAddress base cycle).val = welcomeWordLongStart word)
    (indexEq : index.val = word.val % 2) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
       welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3])
      ⟨.lm1, .long, welcomeWordLongAddress word⟩ (welcomeWordIndex word) =
      ProofsLean.MNCore.PlusOne.increment
        (writeFiles.lm0 ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩) := by
  have commit := welcome_commit_readback files writeFiles base bounded cycle index
    (by have := word.isLt; omega)
  have accessEq : (⟨.lm1, .long, welcomeWordLongAddress word⟩ : DirectMemoryAccess) =
      welcomeDestinationAccess base cycle := by
    unfold welcomeDestinationAccess
    congr 1
    apply Fin.ext
    simpa [welcomeWordLongAddress] using startEq.symm
  have indexEq' : welcomeWordIndex word = index := by
    apply Fin.ext
    simp [welcomeWordIndex, indexEq]
  rw [accessEq, indexEq', commit]
  by_cases even : word.val % 2 = 0
  · have indexZero : index = 0 := Fin.ext (by omega)
    rw [indexZero, welcomePreparedWrite_data_zero]
    apply congrArg ProofsLean.MNCore.PlusOne.increment
    apply congrArg writeFiles.lm0
    apply Fin.ext
    rw [welcomeSourceAddress_val base bounded cycle]
    have destVal := welcomeDestinationAddress_val base bounded cycle
    have wordEq : welcomeWordLongStart word = word.val := by
      simp [welcomeWordLongStart]
      omega
    change base + 2 * cycle.val = word.val
    omega
  · have indexOne : index = 1 := Fin.ext (by omega)
    rw [indexOne, welcomePreparedWrite_data_one]
    apply congrArg ProofsLean.MNCore.PlusOne.increment
    apply congrArg writeFiles.lm0
    apply Fin.ext
    simp [advance, Bank.capacity, welcomeSourceAddress, welcomeRawAddress]
    have destVal := welcomeDestinationAddress_val base bounded cycle
    have wordEq : welcomeWordLongStart word = word.val - 1 := by
      simp [welcomeWordLongStart]
      omega
    have := word.isLt
    omega


/-- A low LM1 address (below 8) lies outside the four `.long` windows written
by the base-8 Welcome line. -/
theorem welcomeBase8Distance (read : Fin Bank.lm1.capacity) (cycle : Fin 4)
    (index : Fin 4) (low : read.val + index.val < 8) :
    count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress 8 cycle)
      (advance .lm1 read index.val) := by
  have htarget : (advance .lm1 read index.val).val = read.val + index.val := by
    simp [advance, Bank.capacity]
    have := read.isLt
    have := index.isLt
    omega
  rw [show (advance .lm1 read index.val) =
      ⟨read.val + index.val, by have := read.isLt; have := index.isLt; change read.val + index.val < 4096; omega⟩
    from Fin.ext htarget]
  have hstart := welcomeDestinationAddress_val 8 (Or.inr rfl) cycle
  simp only [count, Width.words, distance, Bank.capacity, hstart]
  rw [Nat.mod_eq_of_lt]
  · change 2 ≤ read.val + index.val + 4096 - (8 + 2 * cycle.val)
    omega
  · have := read.isLt
    have := index.isLt
    have := cycle.isLt
    omega

/-- Committing base-8 Welcome writes preserves a low LM1 read. -/
theorem welcomeBase8Writes_preserves_read (files writeFiles : IntegerRegisterFiles)
    (cycles : List (Fin 4)) (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (indexBound : index.val < 2) (low : read.val + index.val < 8) :
    readDirectAccess (commitParsedMaskedWrites files
      (cycles.map (welcomePreparedWrite writeFiles 8))) ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  induction cycles generalizing files with
  | nil => rfl
  | cons cycle rest ih =>
      rw [List.map_cons]
      rw [show commitParsedMaskedWrites files
          (welcomePreparedWrite writeFiles 8 cycle ::
            rest.map (welcomePreparedWrite writeFiles 8)) =
        commitParsedMaskedWrites
          (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles 8 cycle])
          (rest.map (welcomePreparedWrite writeFiles 8)) from rfl]
      rw [ih (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles 8 cycle])]
      unfold welcomePreparedWrite welcomeDestinationAccess
      rw [commitParsedMaskedWrites_singleton_lm1Long]
      exact readDirectAccess_lm1Long_after_write_outside files
        (welcomeDestinationAddress 8 cycle) read _ _ index
        (welcomeBase8Distance read cycle index low)



/-- Reading back a word written by a Welcome line: the LM1 word is the
increment of the LM0 source word. `inBase` says `word` lies in the eight-word
half written by `base` (`0..7` for base 0, `8..15` for base 8). -/
theorem welcomeLineReadback (base : Nat) (bounded : base = 0 ∨ base = 8)
    (state next : State) (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerInstructionLine (.pe [(welcomeExpr base)])
      state = .ok next)
    (word : Fin 16) (cycle : Fin 4) (index : Fin 4)
    (startEq : (welcomeDestinationAddress base cycle).val = welcomeWordLongStart word)
    (indexEq : index.val = word.val % 2)
    (inBase : base ≤ word.val ∧ word.val < base + 8) :
    (next.peRegisters welcomePE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
    ProofsLean.MNCore.PlusOne.increment
      ((state.peRegisters welcomePE).lm0
        ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩) := by
  have value := welcome_executeIntegerProducerInstructionLine_peRegisters base state next
    invariant executed welcomePE
  have read := welcomeCommit_readback_word (state.peRegisters welcomePE)
    (state.peRegisters welcomePE) base bounded word cycle index startEq indexEq
  rw [← readDirectAccess_welcomeWord (next.peRegisters welcomePE) word, value]
  exact read


/-- Literal-list form of the base-8 low-word preservation. -/
theorem welcomeBase8Writes_preserves_read_literal (files writeFiles : IntegerRegisterFiles)
    (read : Fin Bank.lm1.capacity) (index : Fin 4) (indexBound : index.val < 2)
    (low : read.val + index.val < 8) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles 8 0, welcomePreparedWrite writeFiles 8 1,
       welcomePreparedWrite writeFiles 8 2, welcomePreparedWrite writeFiles 8 3])
      ⟨.lm1, .long, read⟩ index =
    readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  simpa using welcomeBase8Writes_preserves_read files writeFiles [0, 1, 2, 3]
    read index indexBound low

/-- A Welcome line preserves the LM0 words of every PE. -/
theorem welcomeLineLm0Preserved (base : Nat) (state next : State)
    (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerInstructionLine (.pe [(welcomeExpr base)])
      state = .ok next) (p : PEId) :
    (next.peRegisters p).lm0 = (state.peRegisters p).lm0 := by
  have value := welcome_executeIntegerProducerInstructionLine_peRegisters base state next
    invariant executed p
  rw [value]
  exact welcomeCommits_lm0_preserved (state.peRegisters p) (state.peRegisters p) base


/-- **Upper bound.** The two accepted Welcome lines compute `n_i = m_i + 1`
for all 16 LM1 words, on the sealed whole-machine value model, from the
zero-initialised machine and for every admissible input (`0..50` per word). -/
theorem welcomeAnswer_correct :
    ProofsLean.Correct welcomeSealedMachine welcomeSpec welcomeAnswer := by
  refine ⟨trivial, ?_⟩
  intro input _admissible
  let machineInput : ProofsLean.MNCore.PlusOne.Words := input
  change ∃ result, ProofsLean.execute welcomeSealedMachine welcomeAnswer
      (welcomeInitialState machineInput) = some result ∧
    welcomeSpec.post machineInput result
  obtain ⟨s1, step1, line1, invariant1, value1⟩ :=
    welcomeSealed_step 0 (welcomeInitialState machineInput) (welcomeInitialState_invariant input)
  obtain ⟨s2, step2, line2, _invariant2, value2⟩ :=
    welcomeSealed_step 8 s1 invariant1
  refine ⟨s2, ?_, ?_⟩
  · simp only [ProofsLean.execute, welcomeAnswer]
    rw [step1]
    simp [step2]
  · intro i
    have hi := i.isLt
    have hdivmod := Nat.div_add_mod i.val 2
    have hmodlt := Nat.mod_lt i.val (by decide : 0 < 2)
    by_cases low : i.val < 8
    · -- word 0..7: line 0 wrote it; line 1 preserves it
      let c : Fin 4 := ⟨i.val / 2, by omega⟩
      have startEq : (welcomeDestinationAddress 0 c).val = welcomeWordLongStart i := by
        rw [welcomeDestinationAddress_val 0 (Or.inl rfl) c]
        simp [welcomeWordLongStart, c]
      have read0 := welcomeLineReadback 0 (Or.inl rfl) (welcomeInitialState machineInput) s1
        (welcomeInitialState_invariant input) line1 i c (welcomeWordIndex i)
        startEq rfl ⟨by omega, low⟩
      have preserve := welcomeBase8Writes_preserves_read_literal
        (s1.peRegisters welcomePE) (s1.peRegisters welcomePE)
        (welcomeWordLongAddress i) (welcomeWordIndex i)
        (welcomeWordIndex_lt_two i)
        (by simp [welcomeWordLongAddress, welcomeWordLongStart, welcomeWordIndex]; omega)
      have s2lm1 : (s2.peRegisters welcomePE).lm1
          ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
          (s1.peRegisters welcomePE).lm1
            ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ := by
        rw [← readDirectAccess_welcomeWord (s2.peRegisters welcomePE) i]
        rw [value2 welcomePE]
        rw [preserve]
        rw [readDirectAccess_welcomeWord]
      rw [s2lm1, read0, welcomeInitialState_lm0]
      exact ProofsLean.MNCore.PlusOne.increment_eq_add_one (machineInput i)
    · -- word 8..15: line 1 wrote it
      have high : 8 ≤ i.val := by omega
      let c : Fin 4 := ⟨i.val / 2 - 4, by omega⟩
      have startEq : (welcomeDestinationAddress 8 c).val = welcomeWordLongStart i := by
        rw [welcomeDestinationAddress_val 8 (Or.inr rfl) c]
        simp [welcomeWordLongStart, c]
        omega
      have read8 := welcomeLineReadback 8 (Or.inr rfl) s1 s2 invariant1 line2 i c
        (welcomeWordIndex i) startEq rfl ⟨high, hi⟩
      have lm0preserved := welcomeLineLm0Preserved 0 (welcomeInitialState machineInput) s1
        (welcomeInitialState_invariant input) line1 welcomePE
      rw [read8, lm0preserved, welcomeInitialState_lm0]
      exact ProofsLean.MNCore.PlusOne.increment_eq_add_one (machineInput i)


end ProofsLean.MNCore
