import ProofsLean.WelcomeOptimalFinal
import ProofsLean.WelcomeValueBound
import ProofsLean.WelcomePlainClose
import ProofsLean.StageCommitSpecific
import ProofsLean.GenericLowerBound

/-! # Problem `3.a-plus-b` (A + B) on the sealed whole-machine value model

This module states the challenge problem `3.a-plus-b` — `C = A + B` for two
`32`-word integer vectors stored in LM0 and LM1, with the result written to
LM0 words `32..63` — on the same **sealed whole-machine value model** that
`ProofsLean/WelcomeOptimalFinal.lean` uses for the Welcome problem, proves the
saved six-line answer correct, and attacks a lower bound by a value argument
at an explicitly non-zero input.

## The model

`aplusbSealedMachine` is the sealed machine: `Line` and `lineCost` are the
whole-machine ones, the state is the real `State`, and `step` is the value
transition `executeNormalizedLine` that `wholeMachine.step` invokes *after* its
issue, address-mode and hazard-history checks.  A non-`.ok` value transition is
`none`.  As in `WelcomeOptimal.lean`, the hazard-history layer and the
`.failure`/`.unknown` distinction are **sealed away**; every theorem below is
stated about this restricted machine and carries that restriction.

The input is **PE-uniform**: `A` occupies LM0 words `0..31` of every PE and
`B` occupies LM1 words `0..31`.  The postcondition is **bit-exact** and is
observed on **one PE** (`n0c0b0m0p0`, as in the Welcome model).  Both choices
weaken the official problem (which observes every PE and allows an absolute
error of `1e-4`), so they are sound for a lower bound.

## Strength of the specification

The bit-exact postcondition is *stronger* than the official `1e-4` tolerance.
`LowerBound aplusbSealedMachine aplusbSpec 2` therefore does not formally
imply the official tolerance bound; the transfer needs a tolerance-valued
postcondition.  The refutations below are robust in the sense that they
exhibit a word that is off by `1` (an untouched output word reading `0`
against a target of `1`), so any tolerance below `1` is violated as well; that
robustness is *argued*, not formalised.

## What this module proves

* `aplusbSpec` and `aplusbInitialState` — the problem on the sealed machine,
  stated over a PE-uniform input with the bit-exact wrapping sum as the
  postcondition.
* `aplusbAnswer` — the six accepted lines of
  `problems/challenge/3.a-plus-b/answer.vsm`.
* The executor algebra of those six lines: the concrete address lowering
  (`aplusbIadd_accesses`, `aplusbCopy_accesses`), the `.word` pairwise-add data
  formula (`aplusbIadd_data_eq`), the `passa` identity
  (`aplusb_pass_data_eq`), the per-cycle and four-cycle prepared-write lists
  (`aplusbIadd_cycle`, `aplusbCopy_cycle`, `aplusbIadd_cycles`,
  `aplusbCopy_cycles`), and the integer-stage preparation
  `aplusb_welcomeIntegerPrep_iadd`.
* Empty program, any `nop`, any `mv`, and every syntactically rejected `.pe`
  line are refuted unconditionally
  (`aplusbEmpty_not_correct`, `aplusbNop_not_correct`,
  `aplusbMv_not_correct`, `aplusbPE_checkFalse_not_correct`, ...),
  as is every all-`.noforward` line.
* `aplusbLowerBound_two_iff_residual` — `LowerBound 2` is *equivalent* to the
  refutation of the explicitly stated residual class `AplusBPEUnrefuted`.
* `aplusb_not_correct_of_lm0Narrow` — **the value argument at the witness
  input `A = 1, B = 0`**: a one-line program whose `.lm0` write list is narrow
  (at most four windows of at most four words) leaves some observed output
  word at its initial `0`, while the target there is `1`.  The counting half
  is `aplusb_exists_uncovered_of_windows` (16 covered words out of 32).

## What is not proved here

* `aplusbAnswer_correct` is **not** proved.  The per-cycle and four-cycle
  preparation lemmas and the `iadd` per-PE core success above are the first
  half of the executor link; the missing half is (a) the analogous
  `ipassa` per-PE core success, (b) the per-PE walk over all 4096 PEs and the
  line step (`executeIntegerProducerInstructionLine_pe_plainIntegerALU` gives
  the step once the walk succeeds), (c) the commit readback of the four writes
  into `grf0`/`lm0`, and (d) the six-line composition and final postcondition.
  Consequently no `Optimal` is claimed.
* `LowerBound aplusbSealedMachine aplusbSpec 2` is **not** proved
  unconditionally: by `aplusbLowerBound_two_iff_residual` it is equivalent to
  refuting `AplusBPEUnrefuted`.  The value argument refutes the narrow
  write-shape `AplusBLm0NarrowAtOnes`; the missing piece is the
  *state-general* destination analysis showing that every writer family's
  `.lm0` writes are confined to at most four windows of at most four words
  (brief rule 2).  In particular, even `LowerBound 2` would be weaker than the
  six-line optimum: the answer's score is six.

## The witness and the tolerance

The witness input is `A = 1, B = 0`, where the target is `1` at every observed
word (`aplusbOnesInput_target`) and the initial LM0 output is `0`
(`aplusbOnesInput_initial_lm0_output`).  This is the correction of the `1.a-b`
zero-input pitfall: at the all-zero input the target is `0` and the empty
program is already correct, so no zero-input shape fact can refute anything.

The discrepancy exhibited is `1`, i.e. `|0 - 1| = 1 > 10^{-4}`, so the
refutations also violate the official tolerance; that robustness is argued,
not formalised, because the specification here is bit-exact (hence stronger
than the official `1e-4` one).

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The input, the initial state and the sealed machine -/

/-- One `32`-word integer vector (`$lm[0:32]` / `$ln[0:32]`). -/
abbrev AplusBWords := Fin 32 → BitVec 32

/-- The `3.a-plus-b` input: `A` in LM0 words `0..31`, `B` in LM1 words
`0..31`, independently for every PE. -/
structure AplusBInput where
  /-- `A`, stored in LM0 words `0..31`. -/
  a : PEId → AplusBWords
  /-- `B`, stored in LM1 words `0..31`. -/
  b : PEId → AplusBWords

/-- LM0 of the initial PE files: `A` in words `0..31`, zero elsewhere. -/
def aplusbInitialLm0 (input : AplusBInput) (pe : PEId)
    (address : Fin 4096) : BitVec 32 :=
  if h : address.val < 32 then input.a pe ⟨address.val, h⟩ else 0

/-- LM1 of the initial PE files: `B` in words `0..31`, zero elsewhere. -/
def aplusbInitialLm1 (input : AplusBInput) (pe : PEId)
    (address : Fin 4096) : BitVec 32 :=
  if h : address.val < 32 then input.b pe ⟨address.val, h⟩ else 0

/-- Zero-initialised PE register file carrying `A` in LM0 and `B` in LM1.
The GRF files, `T` and the mask registers are zero, matching `Machine::new`. -/
def aplusbInitialPERegisters (input : AplusBInput) (pe : PEId) :
    IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with
    lm0 := aplusbInitialLm0 input pe
    lm1 := aplusbInitialLm1 input pe }

/-- The initial whole-machine state of `3.a-plus-b`. -/
def aplusbInitialState (input : AplusBInput) : State :=
  { rustSimulatorInitialState with
    peRegisters := fun pe => aplusbInitialPERegisters input pe }

theorem aplusbInitialState_peRegisters (input : AplusBInput) (pe : PEId) :
    (aplusbInitialState input).peRegisters pe = aplusbInitialPERegisters input pe := rfl

theorem aplusbInitialState_maskDirective (input : AplusBInput) :
    (aplusbInitialState input).maskDirective = welcomeMaskDirective := rfl

theorem aplusbInitialState_context (input : AplusBInput) (pe : PEId) :
    (aplusbInitialState input).peContext pe = ParsedIntegerContext.ofLinearIndex pe := rfl

theorem aplusbInitialPERegisters_lm0 (input : AplusBInput) (pe : PEId) (word : Fin 32) :
    (aplusbInitialPERegisters input pe).lm0
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      input.a pe word := by
  simp [aplusbInitialPERegisters, aplusbInitialLm0, word.isLt]

theorem aplusbInitialPERegisters_lm1 (input : AplusBInput) (pe : PEId) (word : Fin 32) :
    (aplusbInitialPERegisters input pe).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      input.b pe word := by
  simp [aplusbInitialPERegisters, aplusbInitialLm1, word.isLt]

theorem aplusbInitialPERegisters_lm0_other (input : AplusBInput) (pe : PEId)
    (address : Fin 4096) (large : 32 ≤ address.val) :
    (aplusbInitialPERegisters input pe).lm0 address = 0 := by
  simp [aplusbInitialPERegisters, aplusbInitialLm0, Nat.not_lt.mpr large]

theorem aplusbInitialPERegisters_lm1_other (input : AplusBInput) (pe : PEId)
    (address : Fin 4096) (large : 32 ≤ address.val) :
    (aplusbInitialPERegisters input pe).lm1 address = 0 := by
  simp [aplusbInitialPERegisters, aplusbInitialLm1, Nat.not_lt.mpr large]

theorem aplusbInitialPERegisters_grf0 (input : AplusBInput) (pe : PEId)
    (address : Fin 512) :
    (aplusbInitialPERegisters input pe).grf0 address = 0 := rfl

/-- The sealed whole-machine value model of `3.a-plus-b`. -/
noncomputable def aplusbSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := AplusBInput
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The observed PE (`n0c0b0m0p0`, as in the Welcome model). -/
abbrev aplusbPE : PEId := welcomePE

/-- The observed output word `j` (`LM0` word `32 + j`), for `j : Fin 32`. -/
def aplusbOutputAddress (j : Fin 32) : Fin 4096 :=
  ⟨32 + j.val, by have := j.isLt; change 32 + j.val < 4096; omega⟩

/-- The `3.a-plus-b` problem on the sealed machine: `A` in LM0 words `0..31`,
`B` in LM1 words `0..31`, and the observed PE's LM0 word `32 + j` must be the
wrapping 32-bit sum `A[j] + B[j]`. -/
noncomputable def aplusbSpec : ProofsLean.Problem aplusbSealedMachine where
  admissible := fun _ => True
  initial := aplusbInitialState
  post := fun input state => ∀ j : Fin 32,
    (state.peRegisters aplusbPE).lm0 (aplusbOutputAddress j) =
      input.a aplusbPE j + input.b aplusbPE j

theorem aplusbSpec_initial (input : AplusBInput) :
    aplusbSpec.initial input = aplusbInitialState input := rfl

theorem aplusbSpec_admissible (input : AplusBInput) : aplusbSpec.admissible input := trivial

/-! ## 2. The six accepted lines of the answer -/

/-- A `.long` (two-word) access region at long-word base `base`: four cycles at
addresses `base, base+2, base+4, base+6`, matching the VSM `$lm<base>v`. -/
def AplusBLongRegion (base : Nat) : Issue.Region :=
  ⟨2, base, base + 2, base + 4, base + 6, false, none⟩

/-- A `.double` (four-word) access region at base `base`: four cycles at
addresses `base, base+4, base+8, base+12`, matching `$llr<base>v`. -/
def AplusBDoubleRegion (base : Nat) : Issue.Region :=
  ⟨4, base, base + 4, base + 8, base + 12, false, none⟩

/-- A direct, unmasked, non-negated memory operand. -/
def AplusBMem (bank : Issue.Bank) (region : Issue.Region) : ParsedOperand :=
  .mem ⟨bank, region⟩ false false false none

/-- Normalized form of `iadd $lm<base>v $ln<base>v $lr<base>v`. -/
def aplusbIaddExpr (base : Nat) : NormalizedExpr where
  op := .alu .add (some .i) false none
  sources := [AplusBMem .lm0 (AplusBLongRegion base),
              AplusBMem .lm1 (AplusBLongRegion base)]
  destinations := [AplusBMem .grf0 (AplusBLongRegion base)]
  flush := none

/-- Normalized form of `ipassa $llr<src>v $llm<dst>v`. -/
def aplusbCopyExpr (src dst : Nat) : NormalizedExpr where
  op := .alu .passa (some .i) false none
  sources := [AplusBMem .grf0 (AplusBDoubleRegion src)]
  destinations := [AplusBMem .lm0 (AplusBDoubleRegion dst)]
  flush := none

/-- The six accepted lines of `problems/challenge/3.a-plus-b/answer.vsm`. -/
def aplusbAnswer : ProofsLean.Program aplusbSealedMachine :=
  [ InstructionLine.pe [aplusbIaddExpr 0],
    InstructionLine.pe [aplusbIaddExpr 8],
    InstructionLine.pe [aplusbIaddExpr 16],
    InstructionLine.pe [aplusbIaddExpr 24],
    InstructionLine.pe [aplusbCopyExpr 0 32],
    InstructionLine.pe [aplusbCopyExpr 16 48] ]

theorem aplusbAnswer_score : ProofsLean.score aplusbSealedMachine aplusbAnswer = 6 := rfl


/-! ## 3. Concrete address, write and data lemmas for the answer lines -/

/-- The `.long` LM0 source address of cycle `cycle` at base `base`. -/
def aplusbLm0LongAddress (base : Nat) (cycle : Fin 4) : Fin 4096 :=
  ⟨(base + 2 * cycle.val) / 2 * 2 % 4096, Nat.mod_lt _ (by decide)⟩

/-- The `.long` GRF0 destination address of cycle `cycle` at base `base`. -/
def aplusbGrf0LongAddress (base : Nat) (cycle : Fin 4) : Fin 512 :=
  ⟨(base + 2 * cycle.val) / 2 * 2 % 512, Nat.mod_lt _ (by decide)⟩

/-- The `.double` LM0 destination address of cycle `cycle` at base `base`. -/
def aplusbLm0DoubleAddress (base : Nat) (cycle : Fin 4) : Fin 4096 :=
  ⟨(base + 4 * cycle.val) / 4 * 4 % 4096, Nat.mod_lt _ (by decide)⟩

/-- The `.double` GRF0 source address of cycle `cycle` at base `base`. -/
def aplusbGrf0DoubleAddress (base : Nat) (cycle : Fin 4) : Fin 512 :=
  ⟨(base + 4 * cycle.val) / 4 * 4 % 512, Nat.mod_lt _ (by decide)⟩

theorem aplusbIadd_integer_request (base : Nat) :
    (aplusbIaddExpr base).op.integerRequest =
      .ok (.integer .word (.arith .add false)) := rfl

theorem aplusbCopy_integer_request (src dst : Nat) :
    (aplusbCopyExpr src dst).op.integerRequest =
      .ok (.integer .word .passa) := rfl

/-- The direct lowering of one cycle of `iadd $lm<base>v $ln<base>v $lr<base>v`. -/
theorem aplusbIadd_accesses (base : Nat) (registers : Masks.RegisterFile)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (tWord : BitVec 32) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (aplusbIaddExpr base).toParsed
        registers welcomeMaskDirective false group l2b l1b mab pe cycle 0 0 tWord =
        some accesses ∧
      accesses.op = .alu .add (some .i) false none ∧
      accesses.sourceX = .memory ⟨.lm0, .long, aplusbLm0LongAddress base cycle⟩ false ∧
      accesses.sourceY = .memory ⟨.lm1, .long, aplusbLm0LongAddress base cycle⟩ false ∧
      accesses.destination = ⟨.grf0, .long, aplusbGrf0LongAddress base cycle⟩ ∧
      accesses.writeSelection = ⟨BitVec.allOnes 4, true⟩ ∧
      accesses.flushSelection = none := by
  have hreq : (ParsedOp.alu .add (some .i) false none).executionRequest =
      .ok (.integer .word (.arith .add false)) :=
    Issue.integer_request_is_execution_request _ _ _ (aplusbIadd_integer_request base)
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  simp only [aplusbIaddExpr, NormalizedExpr.toParsed]
  split
  · rename_i precision aluOp heq
    rw [hreq] at heq
    cases heq
    simp (config := { decide := true }) [AplusBMem, AplusBLongRegion,
      ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
      ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.toDirectMemoryDestination?,
      ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
      directiveTargetsBank, resolveFlushSelection?, welcomeMaskDirective,
      parsedRegionAddressAt, parsedWidth?, issueBankToRegisterBank, Bank.capacity,
      aplusbLm0LongAddress, aplusbGrf0LongAddress]
    all_goals
      have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
        have := cycle.isLt
        omega
      rcases hcycle with h | h | h | h <;> simp [h, Width.words]
  · rename_i bad
    exact False.elim (bad .word (.arith .add false) hreq)

/-- The direct lowering of one cycle of `ipassa $llr<src>v $llm<dst>v`. -/
theorem aplusbCopy_accesses (src dst : Nat) (registers : Masks.RegisterFile)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (tWord : BitVec 32) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (aplusbCopyExpr src dst).toParsed
        registers welcomeMaskDirective false group l2b l1b mab pe cycle 0 0 tWord =
        some accesses ∧
      accesses.op = .alu .passa (some .i) false none ∧
      accesses.sourceX = .memory ⟨.grf0, .double, aplusbGrf0DoubleAddress src cycle⟩ false ∧
      accesses.sourceY = .memory ⟨.grf0, .double, aplusbGrf0DoubleAddress src cycle⟩ false ∧
      accesses.destination = ⟨.lm0, .double, aplusbLm0DoubleAddress dst cycle⟩ ∧
      accesses.writeSelection = ⟨BitVec.allOnes 4, true⟩ ∧
      accesses.flushSelection = none := by
  have hreq : (ParsedOp.alu .passa (some .i) false none).executionRequest =
      .ok (.integer .word .passa) :=
    Issue.integer_request_is_execution_request _ _ _ (aplusbCopy_integer_request src dst)
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  simp only [aplusbCopyExpr, NormalizedExpr.toParsed]
  split
  · rename_i precision aluOp heq
    rw [hreq] at heq
    cases heq
    simp (config := { decide := true }) [AplusBMem, AplusBDoubleRegion,
      ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
      ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.toDirectMemoryDestination?,
      ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
      directiveTargetsBank, resolveFlushSelection?, welcomeMaskDirective,
      parsedRegionAddressAt, parsedWidth?, issueBankToRegisterBank, Bank.capacity,
      aplusbLm0DoubleAddress, aplusbGrf0DoubleAddress]
    all_goals
      have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
        have := cycle.isLt
        omega
      rcases hcycle with h | h | h | h <;> simp [h, Width.words]
  · rename_i bad
    exact False.elim (bad .word .passa hreq)

/-- The prepared `.long` GRF0 write of one `iadd` cycle. -/
def aplusbIaddWrite (files : IntegerRegisterFiles) (base : Nat)
    (cycle : Fin 4) : PreparedParsedMaskedWrite where
  destination := some ⟨.grf0, .long, aplusbGrf0LongAddress base cycle⟩
  maskUpdate := none
  data := unpackALUBus (parsedIntegerRegisterOutput files
    ⟨.lm0, .long, aplusbLm0LongAddress base cycle⟩
    ⟨.lm1, .long, aplusbLm0LongAddress base cycle⟩ .word (.arith .add false) false).value
  selection := ⟨BitVec.allOnes 4, true⟩

/-- The prepared `.double` LM0 write of one `ipassa` cycle. -/
def aplusbCopyWrite (files : IntegerRegisterFiles) (src dst : Nat)
    (cycle : Fin 4) : PreparedParsedMaskedWrite where
  destination := some ⟨.lm0, .double, aplusbLm0DoubleAddress dst cycle⟩
  maskUpdate := none
  data := readDirectAccess files ⟨.grf0, .double, aplusbGrf0DoubleAddress src cycle⟩
  selection := ⟨BitVec.allOnes 4, true⟩

/-- The forwarding slots after one `iadd` cycle. -/
def aplusbIaddSlots (nextSlots : Forwarding.Slots) (files : IntegerRegisterFiles)
    (base : Nat) (cycle : Fin 4) : Forwarding.Slots :=
  fun unit slotCycle =>
    if unit = .alu ∧ slotCycle = cycle then
      .known (pack (aplusbIaddWrite files base cycle).data)
    else nextSlots unit slotCycle

/-- The forwarding slots after one `ipassa` cycle. -/
def aplusbCopySlots (nextSlots : Forwarding.Slots) (files : IntegerRegisterFiles)
    (src dst : Nat) (cycle : Fin 4) : Forwarding.Slots :=
  fun unit slotCycle =>
    if unit = .alu ∧ slotCycle = cycle then
      .known (pack (aplusbCopyWrite files src dst cycle).data)
    else nextSlots unit slotCycle

theorem aplusb_or_shift_append (a b : BitVec 32) :
    a.setWidth 64 <<< 32 ||| b.setWidth 64 = a ++ b := by
  rw [← BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  simp

theorem aplusb_or_shift_append' (a b : BitVec 32) :
    b.setWidth 64 ||| a.setWidth 64 <<< 32 = a ++ b := by
  rw [BitVec.or_comm, aplusb_or_shift_append]

/-- Lane 0 of a packed two-word bus is the second word. -/
theorem aplusb_lane_zero_pack (d : WordBus) :
    IntegerALU.lane .word (pack d) 0 = d 1 := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width, PEMemory.pack]
  exact BitVec.extractLsb'_append_eq_right

/-- Lane 1 of a packed two-word bus is the first word. -/
theorem aplusb_lane_one_pack (d : WordBus) :
    IntegerALU.lane .word (pack d) 1 = d 0 := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width, PEMemory.pack]
  exact BitVec.extractLsb'_append_eq_left

/-- The high half of a `.word` `add` bus is the packed pairwise sums. -/
theorem aplusb_eval_high (a0 a1 b0 b1 : BitVec 32) :
    (IntegerALU.evaluateBus .word (.arith .add false)
      (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
      (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0))
      false).value.high = (a0 + b0) ++ (a1 + b1) := by
  simp only [IntegerALU.evaluateBus, IntegerALU.Precision.lanes, IntegerALU.Precision.width,
    List.range, List.range.loop, List.foldl]
  rw [show IntegerALU.lane .word
        (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0)) 0
        = a1 from aplusb_lane_zero_pack _,
      show IntegerALU.lane .word
        (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0)) 1
        = a0 from aplusb_lane_one_pack _,
      show IntegerALU.lane .word
        (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) 0
        = b1 from aplusb_lane_zero_pack _,
      show IntegerALU.lane .word
        (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) 1
        = b0 from aplusb_lane_one_pack _]
  simp [IntegerALU.evaluateLane, IntegerALU.arithmetic, BitVec.shiftLeft_zero]
  rw [aplusb_or_shift_append']

/-- The low half of a `.word` `add` bus is zero. -/
theorem aplusb_eval_low (a0 a1 b0 b1 : BitVec 32) :
    (IntegerALU.evaluateBus .word (.arith .add false)
      (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
      (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0))
      false).value.low = 0 := by
  simp [IntegerALU.evaluateBus, PEMemory.pack]

/-- The two lanes of a `.word` `iadd` are the pairwise word sums. -/
theorem aplusbIadd_data_eq (a0 a1 b0 b1 : BitVec 32) :
    unpackALUBus (IntegerALU.evaluateBus .word (.arith .add false)
      (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
      (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) false).value =
      (fun i => if i.val = 0 then a0 + b0 else if i.val = 1 then a1 + b1 else 0) := by
  funext i
  rw [show (IntegerALU.evaluateBus .word (.arith .add false)
        (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
        (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) false).value =
      ⟨(IntegerALU.evaluateBus .word (.arith .add false)
          (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
          (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) false).value.high,
        (IntegerALU.evaluateBus .word (.arith .add false)
          (pack (fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else 0))
          (pack (fun i => if i.val = 0 then b0 else if i.val = 1 then b1 else 0)) false).value.low⟩
      from rfl]
  rw [aplusb_eval_high a0 a1 b0 b1, aplusb_eval_low a0 a1 b0 b1]
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.elim0 m) l) k) j) i
  · simp [unpackALUBus]
    exact BitVec.extractLsb'_append_eq_left
  · simp [unpackALUBus]
    exact BitVec.extractLsb'_append_eq_right
  · simp [unpackALUBus]
  · simp [unpackALUBus]

/-- The reconstruction of the high half of a `passa` bus is the identity. -/
theorem aplusb_passa_high (x : BitVec 64) :
    (x.extractLsb' 0 32).setWidth 64 ||| (x.extractLsb' 32 32).setWidth 64 <<< 32 = x := by
  rw [BitVec.or_comm, aplusb_or_shift_append, BitVec.extractLsb'_append_extractLsb']

/-- `passa` copies the whole 128-bit bus unchanged. -/
theorem aplusb_evaluateBus_word_passa (x y : IntegerALU.Bus) (reduced : Bool) :
    (IntegerALU.evaluateBus .word .passa x y reduced).value = x := by
  cases x with
  | mk high low =>
    simp [IntegerALU.evaluateBus, IntegerALU.lane, IntegerALU.evaluateLane,
      IntegerALU.Precision.lanes, IntegerALU.Precision.width, List.range,
      List.range.loop, List.foldl, aplusb_passa_high]

/-- The unpacked four words of a `passa` cycle are its four source words. -/
theorem aplusb_pass_data_eq (bus : WordBus) :
    unpackALUBus (IntegerALU.evaluateBus .word .passa (pack bus) (pack bus) false).value =
      bus := by
  rw [aplusb_evaluateBus_word_passa]
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.elim0 m) l) k) j) i
  all_goals simp [PEMemory.pack, unpackALUBus]
  all_goals first
    | rw [BitVec.extractLsb'_append_eq_left]
    | rw [BitVec.extractLsb'_append_eq_right]

/-- One `iadd` cycle prepares exactly its four-word write. -/
theorem aplusbIadd_cycle
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (base : Nat) (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots
      (aplusbIaddExpr base).toParsed control false false false cycle =
      .ok ([aplusbIaddWrite files base cycle],
        aplusbIaddSlots nextSlots files base cycle) := by
  obtain ⟨accesses, lowered, op, sourceX, sourceY, destination, selection, flush⟩ :=
    aplusbIadd_accesses base files.maskRegisters control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.tWord
  have request : accesses.op.executionRequest = .ok (.integer .word (.arith .add false)) := by
    rw [op]
    exact Issue.integer_request_is_execution_request _ _ _ (aplusbIadd_integer_request base)
  have prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses false =
      .ok (aplusbIaddWrite files base cycle) := by
    rw [prepareParsedMaskedWriteWithForwarding_memory_eq files oldSlots cycle accesses false
      sourceX sourceY flush .word (.arith .add false) request]
    simp [aplusbIaddWrite, destination, selection, parsedIntegerRegisterOutput]
  refine prepareParsedIntegerALUExprCycle_alu_direct files oldSlots nextSlots
    (aplusbIaddExpr base).toParsed control false false false cycle accesses
    (aplusbIaddWrite files base cycle) (aplusbIaddSlots nextSlots files base cycle)
    ⟨.add, some .i, false, none, rfl⟩ ?_ prepared ?_
  · rw [directiveEq, bar0Zero, bar1Zero]
    exact lowered
  · rw [updateParsedIntegerALUForwardingCycle_semantics]
    simp only [Bool.false_eq_true, if_false, aplusbIaddSlots]
    rfl

/-- One `ipassa` cycle prepares exactly its four-word write, copying the source
bus. -/
theorem aplusbCopy_cycle
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (src dst : Nat) (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots
      (aplusbCopyExpr src dst).toParsed control false false false cycle =
      .ok ([aplusbCopyWrite files src dst cycle],
        aplusbCopySlots nextSlots files src dst cycle) := by
  obtain ⟨accesses, lowered, op, sourceX, sourceY, destination, selection, flush⟩ :=
    aplusbCopy_accesses src dst files.maskRegisters control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.tWord
  have request : accesses.op.executionRequest = .ok (.integer .word .passa) := by
    rw [op]
    exact Issue.integer_request_is_execution_request _ _ _ (aplusbCopy_integer_request src dst)
  have prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses false =
      .ok (aplusbCopyWrite files src dst cycle) := by
    rw [prepareParsedMaskedWriteWithForwarding_memory_eq files oldSlots cycle accesses false
      sourceX sourceY flush .word .passa request]
    simp [aplusbCopyWrite, destination, selection, aplusb_pass_data_eq]
  refine prepareParsedIntegerALUExprCycle_alu_direct files oldSlots nextSlots
    (aplusbCopyExpr src dst).toParsed control false false false cycle accesses
    (aplusbCopyWrite files src dst cycle) (aplusbCopySlots nextSlots files src dst cycle)
    ⟨.passa, some .i, false, none, rfl⟩ ?_ prepared ?_
  · rw [directiveEq, bar0Zero, bar1Zero]
    exact lowered
  · rw [updateParsedIntegerALUForwardingCycle_semantics]
    simp only [Bool.false_eq_true, if_false, aplusbCopySlots]
    rfl


/-! ## 4. Four-cycle preparation and per-PE execution of one answer line -/

/-- Four-cycle preparation of one `iadd` line: exactly its four writes, in
cycle order. -/
theorem aplusbIadd_cycles
    (files : IntegerRegisterFiles) (oldSlots initialSlots : Forwarding.Slots)
    (base : Nat) (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ slots,
      prepareParsedIntegerALUExprCycles files oldSlots initialSlots
        (aplusbIaddExpr base).toParsed control false false false =
        .ok ([aplusbIaddWrite files base 0, aplusbIaddWrite files base 1,
          aplusbIaddWrite files base 2, aplusbIaddWrite files base 3], slots) := by
  let s1 := aplusbIaddSlots initialSlots files base 0
  let s2 := aplusbIaddSlots s1 files base 1
  let s3 := aplusbIaddSlots s2 files base 2
  refine ⟨aplusbIaddSlots s3 files base 3, ?_⟩
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbIadd_cycle files oldSlots initialSlots base control 0 directiveEq bar0Zero bar1Zero]
  dsimp only
  simp only [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbIadd_cycle files oldSlots s1 base control 1 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbIadd_cycle files oldSlots s2 base control 2 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbIadd_cycle files oldSlots s3 base control 3 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp [s1, s2, s3, List.cons_append, List.nil_append]

/-- Four-cycle preparation of one `ipassa` line. -/
theorem aplusbCopy_cycles
    (files : IntegerRegisterFiles) (oldSlots initialSlots : Forwarding.Slots)
    (src dst : Nat) (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ slots,
      prepareParsedIntegerALUExprCycles files oldSlots initialSlots
        (aplusbCopyExpr src dst).toParsed control false false false =
        .ok ([aplusbCopyWrite files src dst 0, aplusbCopyWrite files src dst 1,
          aplusbCopyWrite files src dst 2, aplusbCopyWrite files src dst 3], slots) := by
  let s1 := aplusbCopySlots initialSlots files src dst 0
  let s2 := aplusbCopySlots s1 files src dst 1
  let s3 := aplusbCopySlots s2 files src dst 2
  refine ⟨aplusbCopySlots s3 files src dst 3, ?_⟩
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbCopy_cycle files oldSlots initialSlots src dst control 0 directiveEq bar0Zero bar1Zero]
  dsimp only
  simp only [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbCopy_cycle files oldSlots s1 src dst control 1 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbCopy_cycle files oldSlots s2 src dst control 2 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [aplusbCopy_cycle files oldSlots s3 src dst control 3 directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp [s1, s2, s3, List.cons_append, List.nil_append]

/-- The `iadd` line is an integer/matrix-read stage input. -/
theorem aplusbIadd_stageInput (base : Nat) :
    parsedExprIsIntegerMatrixReadStageInput (aplusbIaddExpr base).toParsed = true := by
  simp [parsedExprIsIntegerMatrixReadStageInput, aplusbIaddExpr, NormalizedExpr.toParsed,
    parsedExprWaitTag?, parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
    parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
    parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
    parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
    parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
    parsedExprIsFloatReluProducer]

/-- The `ipassa` line is an integer/matrix-read stage input. -/
theorem aplusbCopy_stageInput (src dst : Nat) :
    parsedExprIsIntegerMatrixReadStageInput (aplusbCopyExpr src dst).toParsed = true := by
  simp [parsedExprIsIntegerMatrixReadStageInput, aplusbCopyExpr, NormalizedExpr.toParsed,
    parsedExprWaitTag?, parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
    parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
    parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
    parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
    parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
    parsedExprIsFloatReluProducer, parsedExprIsPlainIntegerALU]

/-- Fold the singleton integer stage. -/
theorem aplusb_prepareParsedIntegerMatrixReadLineExpressions_singleton
    (files : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expr : ParsedExpr)
    (control : ParsedMaskExecutionControl) (writeList : List PreparedParsedMaskedWrite)
    (slots : Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store
      expr control false false false = .ok (writeList, slots, bars)) :
    prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
      false false false [expr] [] oldSlots [] = .ok (writeList, slots, bars) := by
  simp [prepareParsedIntegerMatrixReadLineExpressions, prepared]

/-- The integer-stage preparation of one plain expression is its four prepared
writes. -/
theorem aplusb_welcomeIntegerPrep_iadd
    (state : State) (pe : PEId) (base : Nat)
    (directiveEq : (parsedPEHazardControl state pe).directive = welcomeMaskDirective)
    (bar0Zero : (parsedPEHazardControl state pe).context.bar0 = 0)
    (bar1Zero : (parsedPEHazardControl state pe).context.bar1 = 0) :
    ∃ slots bars,
      welcomeIntegerPrep state pe [(aplusbIaddExpr base).toParsed] =
        .ok ([aplusbIaddWrite (state.peRegisters pe) base 0,
          aplusbIaddWrite (state.peRegisters pe) base 1,
          aplusbIaddWrite (state.peRegisters pe) base 2,
          aplusbIaddWrite (state.peRegisters pe) base 3], slots, bars) := by
  obtain ⟨slots, prepared⟩ :=
    aplusbIadd_cycles (state.peRegisters pe) (stateForwardingSlots state pe)
      (stateForwardingSlots state pe) base (parsedPEHazardControl state pe)
      directiveEq bar0Zero bar1Zero
  have exprPrepared : prepareParsedIntegerMatrixReadLineExpression (state.peRegisters pe)
      (stateForwardingSlots state pe) (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (aplusbIaddExpr base).toParsed (parsedPEHazardControl state pe) false false false =
      .ok ([aplusbIaddWrite (state.peRegisters pe) base 0,
        aplusbIaddWrite (state.peRegisters pe) base 1,
        aplusbIaddWrite (state.peRegisters pe) base 2,
        aplusbIaddWrite (state.peRegisters pe) base 3], slots, []) := by
    rw [prepareParsedIntegerMatrixReadLineExpression_plain]
    · have hcongr := congrArg (fun r =>
        match r with
        | ProofsLean.StepResult.failure => ProofsLean.StepResult.failure
        | ProofsLean.StepResult.unknown => ProofsLean.StepResult.unknown
        | ProofsLean.StepResult.ok (writes, outputSlots) =>
            ProofsLean.StepResult.ok (writes, outputSlots,
              ([] : List (Bool × BitVec 12)))) prepared
      exact hcongr
    · exact Or.inl ⟨.add, some .i, false, none, rfl⟩
  refine ⟨slots, [], ?_⟩
  unfold welcomeIntegerPrep
  have filter : [((aplusbIaddExpr base).toParsed)].filter
      parsedExprIsIntegerMatrixReadStageInput = [(aplusbIaddExpr base).toParsed] := by
    apply List.filter_eq_self.mpr
    intro expression member
    simp only [List.mem_singleton] at member
    subst member
    exact aplusbIadd_stageInput base
  simp only [filter]
  exact aplusb_prepareParsedIntegerMatrixReadLineExpressions_singleton (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (aplusbIaddExpr base).toParsed (parsedPEHazardControl state pe)
    [aplusbIaddWrite (state.peRegisters pe) base 0,
      aplusbIaddWrite (state.peRegisters pe) base 1,
      aplusbIaddWrite (state.peRegisters pe) base 2,
      aplusbIaddWrite (state.peRegisters pe) base 3] slots [] exprPrepared


/-! ## 6. The one-line refutation: witness input, residual class and value argument -/

/-- The all-zero input. -/
def aplusbZeroInput : AplusBInput where
  a := fun _ _ => 0
  b := fun _ _ => 0

/-- The witness input `A = 1, B = 0`: the target is `1` in every observed word. -/
def aplusbOnesInput : AplusBInput where
  a := fun _ _ => 0x00000001
  b := fun _ _ => 0

theorem aplusbOnesInput_target (j : Fin 32) :
    aplusbOnesInput.a aplusbPE j + aplusbOnesInput.b aplusbPE j = 0x00000001 := by
  simp [aplusbOnesInput]

theorem aplusbOnesInput_initial_lm0_output (j : Fin 32) :
    ((aplusbInitialState aplusbOnesInput).peRegisters aplusbPE).lm0
      (aplusbOutputAddress j) = 0 := by
  simp [aplusbInitialState, aplusbInitialPERegisters, aplusbInitialLm0,
    aplusbOutputAddress]

theorem aplusbOnes_target_ne_zero (j : Fin 32) :
    aplusbOnesInput.a aplusbPE j + aplusbOnesInput.b aplusbPE j ≠ 0 := by
  rw [aplusbOnesInput_target]
  decide

/-- A line whose step is stuck at the initial state of an admissible input is
incorrect. -/
theorem aplusb_not_correct_of_step_none (line : InstructionLine) (input : AplusBInput)
    (stuck : aplusbSealedMachine.step line (aplusbInitialState input) = none) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec ([line] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, _post⟩ := correct.2 input trivial
  rw [aplusbSpec_initial] at executed
  have stepResult : aplusbSealedMachine.step line (aplusbInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [stuck] at stepResult
  simp at stepResult

/-- A line whose successful step leaves the observed PE register file unchanged
is incorrect at a witness where the target differs from the initial value. -/
theorem aplusb_not_correct_of_step_frame (line : InstructionLine) (input : AplusBInput)
    (next : State)
    (step : aplusbSealedMachine.step line (aplusbInitialState input) = some next)
    (frame : next.peRegisters aplusbPE = (aplusbInitialState input).peRegisters aplusbPE)
    (j : Fin 32) (targetNe : input.a aplusbPE j + input.b aplusbPE j ≠ 0) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec ([line] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 input trivial
  rw [aplusbSpec_initial] at executed
  have stepResult : aplusbSealedMachine.step line (aplusbInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have word := post j
  rw [frame] at word
  have initial : ((aplusbInitialState input).peRegisters aplusbPE).lm0
      (aplusbOutputAddress j) = 0 := by
    by_cases small : j.val < 32
    · have large : ¬ 32 + j.val < 32 := by omega
      simp [aplusbInitialState, aplusbInitialPERegisters, aplusbInitialLm0,
        aplusbOutputAddress, large]
    · omega
  rw [initial] at word
  exact targetNe word.symm

theorem aplusbSealed_step_ok {line : InstructionLine} {state next : State}
    (h : aplusbSealedMachine.step line state = some next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  cases e : executeNormalizedLine line.toNormalizedLine state with
  | ok s => simpa [aplusbSealedMachine, e] using h
  | failure => simp [aplusbSealedMachine, e] at h
  | unknown => simp [aplusbSealedMachine, e] at h

theorem aplusbSealed_step_none_of_failure {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .failure) :
    aplusbSealedMachine.step line state = none := by
  simp [aplusbSealedMachine, h]

theorem aplusbSealed_step_none_of_unknown {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .unknown) :
    aplusbSealedMachine.step line state = none := by
  simp [aplusbSealedMachine, h]

/-- The empty program is incorrect: on `A = 1, B = 0` it leaves every observed
LM0 word at its initial `0`, while the target is `1`. -/
theorem aplusbEmpty_not_correct :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([] : ProofsLean.Program aplusbSealedMachine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 aplusbOnesInput trivial
  have stateEq : aplusbInitialState aplusbOnesInput = result := by
    have h : (some (aplusbInitialState aplusbOnesInput) :
        Option aplusbSealedMachine.State) = some result := by
      simpa [ProofsLean.execute] using (by rw [aplusbSpec_initial] at executed; exact executed)
    exact Option.some.inj h
  subst stateEq
  have wanted := post ⟨0, by decide⟩
  rw [aplusbOnesInput_initial_lm0_output, aplusbOnesInput_target] at wanted
  exact absurd wanted.symm (by decide)

/-- No single `nop` line is correct. -/
theorem aplusbNop_not_correct (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (_short : InstructionLine.cost (.nop count wait) < 2) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.nop count wait] : List InstructionLine) := by
  cases step : aplusbSealedMachine.step (InstructionLine.nop count wait)
      (aplusbInitialState aplusbOnesInput) with
  | none => exact aplusb_not_correct_of_step_none _ _ step
  | some next =>
      apply aplusb_not_correct_of_step_frame _ _ next step
      · have executed := aplusbSealed_step_ok step
        exact congrFun (executeNormalizedLine_nop_peRegisters count.val wait _ next executed)
          aplusbPE
      · exact aplusbOnes_target_ne_zero ⟨0, by decide⟩

/-- No single `mv` line is correct. -/
theorem aplusbMv_not_correct (transfer : NormalizedMv) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.mv transfer] : List InstructionLine) := by
  cases step : aplusbSealedMachine.step (InstructionLine.mv transfer)
      (aplusbInitialState aplusbOnesInput) with
  | none => exact aplusb_not_correct_of_step_none _ _ step
  | some next =>
      apply aplusb_not_correct_of_step_frame _ _ next step
      · have executed := aplusbSealed_step_ok step
        exact congrFun (executeNormalizedLine_mv_peRegisters transfer _ next executed)
          aplusbPE
      · exact aplusbOnes_target_ne_zero ⟨0, by decide⟩


/-! ## Syntactic `.pe` refutations -/

theorem aplusbPE_checkFalse_not_correct (expressions : List NormalizedExpr)
    (rejected : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  aplusb_not_correct_of_step_none _ _
    (aplusbSealed_step_none_of_failure (line := .pe expressions)
      (executeNormalizedLine_pe_checkFalse expressions (aplusbInitialState aplusbOnesInput)
        rejected))

theorem aplusb_waitPending_eq (input : AplusBInput) (expression : ParsedExpr) :
    parsedExprWaitPending (aplusbInitialState input) expression =
      parsedExprWaitPending (aplusbInitialState aplusbOnesInput) expression := rfl

theorem aplusbPE_waitPending_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (pending : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = true) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  aplusb_not_correct_of_step_none _ _
    (aplusbSealed_step_none_of_unknown (line := .pe expressions)
      (executeNormalizedLine_pe_waitPending expressions (aplusbInitialState aplusbOnesInput)
        accepted pending))

theorem aplusbPE_unsupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  aplusb_not_correct_of_step_none _ _
    (aplusbSealed_step_none_of_failure (line := .pe expressions)
      (executeNormalizedLine_pe_unsupported expressions (aplusbInitialState aplusbOnesInput)
        accepted waitsComplete unsupported))

theorem aplusbPE_notSupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = false)
    (noUnsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (notSupported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = false) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  aplusb_not_correct_of_step_none _ _
    (aplusbSealed_step_none_of_unknown (line := .pe expressions)
      (executeNormalizedLine_pe_notSupported expressions (aplusbInitialState aplusbOnesInput)
        accepted waitsComplete noUnsupported notSupported))

theorem aplusbPE_noforward_not_correct (expressions : List NormalizedExpr)
    (all : WelcomeAllNoForward expressions) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : aplusbSealedMachine.step (InstructionLine.pe expressions)
      (aplusbInitialState aplusbOnesInput) with
  | none => exact aplusb_not_correct_of_step_none _ _ step
  | some next =>
      apply aplusb_not_correct_of_step_frame _ _ next step
      · have executed := aplusbSealed_step_ok step
        exact congrFun (executeNormalizedLine_pe_peRegisters_noforward expressions _
          next all executed) aplusbPE
      · exact aplusbOnes_target_ne_zero ⟨0, by decide⟩

/-- The four syntactic conditions under which a `.pe` line is not refuted by the
syntactic cases above. -/
def AplusBPEAccepted (expressions : List NormalizedExpr) : Prop :=
  checkParsedTopLine (InstructionLine.pe expressions).toParsed = true ∧
  (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = false ∧
  (expressions.map NormalizedExpr.toParsed).any parsedExprIsUnsupportedRustAlu = false ∧
  (expressions.map NormalizedExpr.toParsed).all parsedExprIsSupportedPELineProducer = true

/-- **The residual class**: a syntactically accepted `.pe` line that is not
all-`.noforward`. -/
def AplusBPEUnrefuted (expressions : List NormalizedExpr) : Prop :=
  AplusBPEAccepted expressions ∧ ¬ WelcomeAllNoForward expressions

/-- Every `.pe` line outside `AplusBPEUnrefuted` is refuted. -/
theorem aplusbPENotUnrefuted_not_correct (expressions : List NormalizedExpr)
    (outside : ¬ AplusBPEUnrefuted expressions) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  by_cases accepted : AplusBPEAccepted expressions
  · by_cases allNoforward : WelcomeAllNoForward expressions
    · exact aplusbPE_noforward_not_correct expressions allNoforward
    · exact absurd ⟨accepted, allNoforward⟩ outside
  · by_cases checkTrue : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true
    · by_cases pendingFalse : (expressions.map NormalizedExpr.toParsed).any
          (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = false
      · by_cases unsupportedFalse : (expressions.map NormalizedExpr.toParsed).any
            parsedExprIsUnsupportedRustAlu = false
        · by_cases supportedTrue : (expressions.map NormalizedExpr.toParsed).all
              parsedExprIsSupportedPELineProducer = true
          · exact absurd ⟨checkTrue, pendingFalse, unsupportedFalse, supportedTrue⟩ accepted
          · have supportedFalse : (expressions.map NormalizedExpr.toParsed).all
                parsedExprIsSupportedPELineProducer = false := by
              cases h : (expressions.map NormalizedExpr.toParsed).all
                  parsedExprIsSupportedPELineProducer <;> simp_all
            exact aplusbPE_notSupported_not_correct expressions checkTrue pendingFalse
              unsupportedFalse supportedFalse
        · have unsupportedTrue : (expressions.map NormalizedExpr.toParsed).any
              parsedExprIsUnsupportedRustAlu = true := by
            cases h : (expressions.map NormalizedExpr.toParsed).any
                parsedExprIsUnsupportedRustAlu <;> simp_all
          exact aplusbPE_unsupported_not_correct expressions checkTrue pendingFalse
            unsupportedTrue
      · have pendingTrue : (expressions.map NormalizedExpr.toParsed).any
            (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) = true := by
          cases h : (expressions.map NormalizedExpr.toParsed).any
              (parsedExprWaitPending (aplusbInitialState aplusbOnesInput)) <;> simp_all
        exact aplusbPE_waitPending_not_correct expressions checkTrue pendingTrue
    · have checkFalse : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false := by
        cases h : checkParsedTopLine (InstructionLine.pe expressions).toParsed <;> simp_all
      exact aplusbPE_checkFalse_not_correct expressions checkFalse

/-- Every line of cost below two outside the residual class is refuted. -/
theorem aplusbShortLine_not_correct (line : InstructionLine)
    (short : InstructionLine.cost line < 2)
    (residual : ∀ expressions : List NormalizedExpr, AplusBPEUnrefuted expressions →
      ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([line] : List InstructionLine) := by
  cases line with
  | pe expressions =>
      by_cases h : AplusBPEUnrefuted expressions
      · exact residual expressions h
      · exact aplusbPENotUnrefuted_not_correct expressions h
  | nop count wait => exact aplusbNop_not_correct count wait short
  | mv transfer => exact aplusbMv_not_correct transfer

/-- **`LowerBound aplusbSealedMachine aplusbSpec 2` is equivalent to the
unrestricted one-line statement.** -/
theorem aplusbLowerBound_two_iff_rejects_short_lines :
    ProofsLean.LowerBound aplusbSealedMachine aplusbSpec 2 ↔
      (∀ line : InstructionLine, InstructionLine.cost line < 2 →
        ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec [line]) := by
  constructor
  · intro lower line short correct
    have bound := lower [line] correct
    have scoreLine : ProofsLean.score aplusbSealedMachine [line] =
        InstructionLine.cost line := rfl
    rw [scoreLine] at bound
    omega
  · intro rejects p correct
    by_contra hle
    have short : ProofsLean.score aplusbSealedMachine p < 2 := by omega
    cases p with
    | nil => exact aplusbEmpty_not_correct correct
    | cons line rest =>
        have positive : 0 < InstructionLine.cost line :=
          aplusbSealedMachine.positiveCost line
        have scoreEq : ProofsLean.score aplusbSealedMachine (line :: rest) =
            InstructionLine.cost line + ProofsLean.score aplusbSealedMachine rest := rfl
        have restZero : ProofsLean.score aplusbSealedMachine rest = 0 := by
          rw [scoreEq] at short
          omega
        have restEmpty : rest = [] := (Generic.score_eq_zero_iff _ _).mp restZero
        subst rest
        have costShort : InstructionLine.cost line < 2 := by
          rw [scoreEq] at short
          simp only [ProofsLean.score] at short
          omega
        exact rejects line costShort correct

/-- **The lower bound from the residual class.** -/
theorem aplusbLowerBound_two_of_residual
    (residual : ∀ expressions : List NormalizedExpr, AplusBPEUnrefuted expressions →
      ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ProofsLean.LowerBound aplusbSealedMachine aplusbSpec 2 := by
  rw [aplusbLowerBound_two_iff_rejects_short_lines]
  intro line short
  exact aplusbShortLine_not_correct line short residual

/-- **The gap, exactly.** -/
theorem aplusbLowerBound_two_iff_residual :
    ProofsLean.LowerBound aplusbSealedMachine aplusbSpec 2 ↔
      (∀ expressions : List NormalizedExpr, AplusBPEUnrefuted expressions →
        ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
          ([InstructionLine.pe expressions] : List InstructionLine)) := by
  constructor
  · intro lower expressions _unrefuted
    rw [aplusbLowerBound_two_iff_rejects_short_lines] at lower
    exact lower (.pe expressions) (by simp [InstructionLine.cost])
  · exact aplusbLowerBound_two_of_residual


/-! ## The LM0 write-list value argument at the witness input -/

/-- A commit step preserves an LM0 word that no write window covers. -/
theorem aplusbCommitStep_lm0_preserves (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (target : Fin Bank.lm0.capacity)
    (value : BitVec 32)
    (keeps : ∀ (width : PEMemory.Width) (address : Fin Bank.lm0.capacity)
        (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm0, width, address⟩ → write.data = data →
      write.selection = selection →
        count .lm0 width ≤ distance .lm0 address target)
    (old : files.lm0 target = value) :
    (welcomeCommitStep files write).lm0 target = value := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
        exact old
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
            exact old
        | some access =>
            cases access with
            | mk bank width address =>
                cases bank with
                | lm0 =>
                    simp only [welcomeCommitStep, writeDirectAccessMasked,
                      writeRegisterBankMasked]
                    rw [writeWordsMasked_preserves_outside .lm0 width files.lm0 address
                      target data selection.flags selection.longLong
                      (keeps width address data selection rfl rfl rfl)]
                    exact old
                | lm1 =>
                    simp only [welcomeCommitStep, writeDirectAccessMasked,
                      writeRegisterBankMasked]
                    exact old
                | grf0 =>
                    simp only [welcomeCommitStep, writeDirectAccessMasked,
                      writeRegisterBankMasked]
                    exact old
                | grf1 =>
                    simp only [welcomeCommitStep, writeDirectAccessMasked,
                      writeRegisterBankMasked]
                    exact old
                | t =>
                    simp only [welcomeCommitStep, writeDirectAccessMasked,
                      writeRegisterBankMasked]
                    exact old

/-- The commit fold preserves an LM0 word outside every write window. -/
theorem aplusbCommit_lm0_preserves_outside (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (target : Fin Bank.lm0.capacity)
    (value : BitVec 32)
    (keeps : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm0.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm0, width, address⟩ → write.data = data →
      write.selection = selection →
        count .lm0 width ≤ distance .lm0 address target)
    (old : files.lm0 target = value) :
    (commitParsedMaskedWrites files writes).lm0 target = value := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using old
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member
        exact keeps item (List.mem_cons_of_mem _ member)
      · exact aplusbCommitStep_lm0_preserves files write target value
          (fun width address data selection destination dataEq selectionEq =>
            keeps write (by simp) width address data selection destination dataEq
              selectionEq)
          old

theorem aplusbOutputAddress_injective {a b : Fin 32}
    (same : aplusbOutputAddress a = aplusbOutputAddress b) : a = b := by
  have values := congrArg Fin.val same
  apply Fin.ext
  simp only [aplusbOutputAddress] at values
  omega

theorem aplusb_advance_distance_lm0 (start target : Fin Bank.lm0.capacity) :
    advance .lm0 start (distance .lm0 start target) = target := by
  apply Fin.ext
  have ht : target.val < 4096 := target.isLt
  have hs : start.val < 4096 := start.isLt
  change (start.val + distance .lm0 start target) % 4096 = target.val
  unfold distance
  change (start.val + (target.val + 4096 - start.val) % 4096) % 4096 = target.val
  exact nat_advance_distance start.val target.val hs ht

theorem aplusb_card_window_le (start : Fin Bank.lm0.capacity) (size : Nat) :
    ((Finset.univ : Finset (Fin 32)).filter
      (fun t => distance .lm0 start (aplusbOutputAddress t) < size)).card ≤ size := by
  classical
  let windowSet := (Finset.univ : Finset (Fin 32)).filter
    (fun t => distance .lm0 start (aplusbOutputAddress t) < size)
  change windowSet.card ≤ size
  rw [← Fintype.card_coe windowSet]
  calc Fintype.card ↥windowSet ≤ Fintype.card (Fin size) := by
        apply Fintype.card_le_of_injective
          (fun t : ↥windowSet =>
            (⟨distance .lm0 start (aplusbOutputAddress t.1), by
              have member := t.2
              simp only [windowSet, Finset.mem_filter, Finset.mem_univ, true_and] at member
              omega⟩ : Fin size))
        intro a b same
        apply Subtype.ext
        have hd : distance .lm0 start (aplusbOutputAddress a.1) =
            distance .lm0 start (aplusbOutputAddress b.1) := by
          simpa using same
        have ea := aplusb_advance_distance_lm0 start (aplusbOutputAddress a.1)
        have eb := aplusb_advance_distance_lm0 start (aplusbOutputAddress b.1)
        exact aplusbOutputAddress_injective (by rw [← ea, ← eb, hd])
    _ = size := by simp

theorem aplusb_card_covered_le :
    ∀ (windows : List (Fin Bank.lm0.capacity × Nat)),
    (∀ p ∈ windows, p.2 ≤ 4) →
    ((Finset.univ : Finset (Fin 32)).filter
      (fun t => ∃ p ∈ windows, distance .lm0 p.1 (aplusbOutputAddress t) < p.2)).card ≤
      4 * windows.length := by
  classical
  intro windows
  induction windows with
  | nil => intro _; simp
  | cons p rest ih =>
      intro sizes
      have hsub : (Finset.univ.filter
            (fun t => ∃ q ∈ p :: rest, distance .lm0 q.1 (aplusbOutputAddress t) < q.2)) ⊆
          (Finset.univ.filter (fun t => distance .lm0 p.1 (aplusbOutputAddress t) < p.2)) ∪
          (Finset.univ.filter
            (fun t => ∃ q ∈ rest, distance .lm0 q.1 (aplusbOutputAddress t) < q.2)) := by
        intro t member
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
        obtain ⟨q, qMem, covered⟩ := member
        rcases List.mem_cons.mp qMem with same | qMem
        · subst same
          exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, covered⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, qMem, covered⟩⟩)
      calc (Finset.univ.filter
              (fun t => ∃ q ∈ p :: rest, distance .lm0 q.1 (aplusbOutputAddress t) < q.2)).card
          ≤ ((Finset.univ.filter (fun t => distance .lm0 p.1 (aplusbOutputAddress t) < p.2)) ∪
              (Finset.univ.filter
                (fun t => ∃ q ∈ rest, distance .lm0 q.1 (aplusbOutputAddress t) < q.2))).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun t => distance .lm0 p.1 (aplusbOutputAddress t) < p.2)).card +
              (Finset.univ.filter
                (fun t => ∃ q ∈ rest, distance .lm0 q.1 (aplusbOutputAddress t) < q.2)).card :=
            Finset.card_union_le _ _
        _ ≤ p.2 + 4 * rest.length := by
            apply Nat.add_le_add
            · exact aplusb_card_window_le p.1 p.2
            · exact ih (fun q qMem => sizes q (List.mem_cons_of_mem _ qMem))
        _ ≤ 4 + 4 * rest.length := by
            have := sizes p (by simp)
            omega
        _ = 4 * (p :: rest).length := by
            rw [List.length_cons]
            omega

/-- **The counting half.**  At most four windows of at most four words each cover
at most sixteen of the thirty-two observed words, so one observed word is
untouched. -/
theorem aplusb_exists_uncovered_of_windows
    (windows : List (Fin Bank.lm0.capacity × Nat))
    (bound : windows.length ≤ 4) (sizes : ∀ p ∈ windows, p.2 ≤ 4) :
    ∃ t : Fin 32, ∀ p ∈ windows,
      ¬ distance .lm0 p.1 (aplusbOutputAddress t) < p.2 := by
  classical
  let covered := (Finset.univ : Finset (Fin 32)).filter
    (fun t => ∃ p ∈ windows, distance .lm0 p.1 (aplusbOutputAddress t) < p.2)
  have bounds : covered.card ≤ 16 := by
    have small : covered.card ≤ 4 * windows.length := aplusb_card_covered_le windows sizes
    have cap : 4 * windows.length ≤ 4 * 4 := Nat.mul_le_mul_left 4 bound
    omega
  have universeCard : (Finset.univ : Finset (Fin 32)).card = 32 := by simp
  have strict : covered.card < (Finset.univ : Finset (Fin 32)).card := by
    omega
  obtain ⟨t, _, untouched⟩ := Finset.exists_mem_notMem_of_card_lt_card strict
  refine ⟨t, ?_⟩
  intro p pMem covers
  exact untouched (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, pMem, covers⟩⟩)

/-- **The narrow LM0 shape at the `A = 1, B = 0` witness input.**  The line's
step commits a write list whose `.lm0` destinations lie in at most four windows
of at most four words. -/
def AplusBLm0NarrowAtOnes (expressions : List NormalizedExpr) : Prop :=
  ∀ next, aplusbSealedMachine.step (.pe expressions) (aplusbInitialState aplusbOnesInput)
      = some next →
    ∃ (writes : List PreparedParsedMaskedWrite)
      (windows : List (Fin Bank.lm0.capacity × Nat)),
      next.peRegisters aplusbPE =
        commitParsedMaskedWrites ((aplusbInitialState aplusbOnesInput).peRegisters aplusbPE)
          writes ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm0.capacity),
        write.destination = some ⟨.lm0, width, address⟩ →
          (address, count .lm0 width) ∈ windows) ∧
      windows.length ≤ 4 ∧ (∀ window ∈ windows, window.2 ≤ 4)

/-- **The value argument at the witness input.**  A line whose LM0 write list
at `A = 1, B = 0` is narrow leaves some observed word at its initial `0`, while
the target there is `1`. -/
theorem aplusb_not_correct_of_lm0Narrow (expressions : List NormalizedExpr)
    (shape : AplusBLm0NarrowAtOnes expressions) :
    ¬ ProofsLean.Correct aplusbSealedMachine aplusbSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : aplusbSealedMachine.step (.pe expressions) (aplusbInitialState aplusbOnesInput) with
  | none => exact aplusb_not_correct_of_step_none _ _ step
  | some next =>
      intro correct
      obtain ⟨writes, windows, committed, covers, bound, sizes⟩ := shape next step
      obtain ⟨word, untouched⟩ := aplusb_exists_uncovered_of_windows windows bound sizes
      obtain ⟨result, executed, post⟩ := correct.2 aplusbOnesInput trivial
      rw [aplusbSpec_initial] at executed
      have stepResult : aplusbSealedMachine.step (.pe expressions)
          (aplusbInitialState aplusbOnesInput) = some result := by
        simpa [ProofsLean.execute] using executed
      rw [step] at stepResult
      have resultEq : result = next := (Option.some.inj stepResult).symm
      subst result
      have zero : (next.peRegisters aplusbPE).lm0 (aplusbOutputAddress word) = 0 := by
        rw [committed]
        apply aplusbCommit_lm0_preserves_outside
          ((aplusbInitialState aplusbOnesInput).peRegisters aplusbPE) writes
          (aplusbOutputAddress word) 0
        · intro write writeMem width address data selection destination dataEq selectionEq
          subst dataEq selectionEq
          have member := covers write writeMem width address destination
          by_cases within : distance .lm0 address (aplusbOutputAddress word) < count .lm0 width
          · exact absurd within (untouched (address, count .lm0 width) member)
          · exact Nat.le_of_not_lt within
        · exact aplusbOnesInput_initial_lm0_output word
      have wanted := post word
      rw [zero, aplusbOnesInput_target] at wanted
      exact absurd wanted.symm (by decide)

/-! ## 7. Executor composition of one plain single-expression line -/

/-- The plain-expression facts needed by the per-PE executor. -/
theorem aplusb_plain_basics_2 (expr : NormalizedExpr)
    (plain : parsedExprIsPlainIntegerALU expr.toParsed = true) :
    ([expr.toParsed].filter parsedExprIsSupportedFloatMAUProducer = []) ∧
    ([expr.toParsed].any parsedExprIsIntegerProducer = true) ∧
    ([expr.toParsed].any parsedExprIsSupportedFloatMAUProducer = false) ∧
    ([expr.toParsed].any parsedExprIsMatrixReadProducer = false) ∧
    ([expr.toParsed].any (fun expression => match expression.op with
      | .noforward => true | _ => false) = false) := by
  cases h : expr.toParsed with
  | mk op sources destinations flush text =>
    cases op <;>
      simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
        parsedExprIsSupportedFloatMAUProducer, parsedExprIsMatrixReadProducer,
        parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
        parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer]

/-- The four-cycle stage of the `iadd` line, with its commit pinned. -/
theorem aplusbIadd_fourCycleStep (state : State) (pe : PEId) (base : Nat)
    (directiveEq : (parsedPEHazardControl state pe).directive = welcomeMaskDirective)
    (bar0Zero : (parsedPEHazardControl state pe).context.bar0 = 0)
    (bar1Zero : (parsedPEHazardControl state pe).context.bar1 = 0) :
    ∃ nextSlots bars,
      parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe)
        (stateForwardingSlots state pe)
        (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
          (ParsedIntegerContext.ofLinearIndex pe).l2b
          (ParsedIntegerContext.ofLinearIndex pe).l1b)
        (List.filter parsedExprIsIntegerMatrixReadStageInput [(aplusbIaddExpr base).toParsed])
        { directive := state.maskDirective,
          context :=
            { pe := (ParsedIntegerContext.ofLinearIndex pe).pe,
              cycle := (ParsedIntegerContext.ofLinearIndex pe).cycle,
              bar0 := (state.peContext pe).bar0,
              bar1 := (state.peContext pe).bar1,
              tWord := (state.peContext pe).tWord,
              group := (ParsedIntegerContext.ofLinearIndex pe).group,
              l2b := (ParsedIntegerContext.ofLinearIndex pe).l2b,
              l1b := (ParsedIntegerContext.ofLinearIndex pe).l1b,
              mab := (ParsedIntegerContext.ofLinearIndex pe).mab },
          elapsedWords := state.hazardClock } false =
        .ok (commitParsedMaskedWrites (state.peRegisters pe)
          [aplusbIaddWrite (state.peRegisters pe) base 0,
            aplusbIaddWrite (state.peRegisters pe) base 1,
            aplusbIaddWrite (state.peRegisters pe) base 2,
            aplusbIaddWrite (state.peRegisters pe) base 3], nextSlots, bars) := by
  obtain ⟨slots, bars, prep⟩ :=
    aplusb_welcomeIntegerPrep_iadd state pe base directiveEq bar0Zero bar1Zero
  have preparedEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (List.filter parsedExprIsIntegerMatrixReadStageInput [(aplusbIaddExpr base).toParsed])
      (parsedPEHazardControl state pe) false = .ok
        ([aplusbIaddWrite (state.peRegisters pe) base 0,
          aplusbIaddWrite (state.peRegisters pe) base 1,
          aplusbIaddWrite (state.peRegisters pe) base 2,
          aplusbIaddWrite (state.peRegisters pe) base 3], slots, bars) := by
    simpa [welcomeIntegerPrep] using prep
  refine ⟨slots, bars, ?_⟩
  have h := parsedIntegerMatrixReadLineFourCycleStep_commit_eq (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (List.filter parsedExprIsIntegerMatrixReadStageInput [(aplusbIaddExpr base).toParsed])
    (parsedPEHazardControl state pe) false
    ([aplusbIaddWrite (state.peRegisters pe) base 0,
      aplusbIaddWrite (state.peRegisters pe) base 1,
      aplusbIaddWrite (state.peRegisters pe) base 2,
      aplusbIaddWrite (state.peRegisters pe) base 3], slots, bars) preparedEq
  simpa [parsedPEHazardControl] using h

/-- One per-PE core step of the `iadd` line. -/
theorem aplusbIadd_core_success (state : State) (pe : PEId) (base : Nat)
    (directiveEq : (parsedPEHazardControl state pe).directive = welcomeMaskDirective)
    (bar0Zero : (parsedPEHazardControl state pe).context.bar0 = 0)
    (bar1Zero : (parsedPEHazardControl state pe).context.bar1 = 0) :
    ∃ next, executeIntegerProducerLineAtPECore [(aplusbIaddExpr base).toParsed] state pe =
      .ok next := by
  obtain ⟨nextSlots, bars, fourEq⟩ :=
    aplusbIadd_fourCycleStep state pe base directiveEq bar0Zero bar1Zero
  obtain ⟨floatEmpty, hasALU, hasMAU, hasMatrixRead, noForward⟩ :=
    aplusb_plain_basics_2 (aplusbIaddExpr base) rfl
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  simp only [fourEq]
  rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)]
  dsimp only
  simp only [hasALU, hasMatrixRead, noForward]
  exact ⟨_, rfl⟩

end ProofsLean.MNCore
