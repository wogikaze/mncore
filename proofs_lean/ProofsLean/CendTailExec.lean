import ProofsLean.CendTail
import ProofsLean.CendLine1Walk

/-! # `12.convert-endian` — executor-level facts for the tail (lines 2 and 3)

This module continues `ProofsLean/CendTail.lean`.  It proves, at the executor
level, the facts about lines 2 and 3 that the value chain needs, and it isolates
one modelling mismatch between `CendTail.CendTailComputation.mauSlots` and the
executor's float-MAU datapath.

## What is proved here

### The MAU forwarding payload of `fvfma`

* `cendMauForwardBus` — the bus a single-precision `fvfma` actually installs as
  the `.mau` forwarding payload: the FMA result in the **high** half and `0` in
  the **low** half.
* `cendFmaCycle` — the per-cycle executor computation
  `executeParsedFloatMAUCycleAtPE` on `cendFmaExpr`, for an arbitrary register
  file and PE context, provided the `.alu` forwarding slot at the cycle carries
  the immediate bus `cendImmediateBus`.  The result bus is exactly
  `cendMauForwardBus`.
* `cendMauShiftBus_ne_forward` — `CendTail.cendMauShiftBus` has the FMA word in
  **both** halves, so it is *not* the bus the executor installs.

### The value chain is unaffected by the low half

`CendTail.cendSbslData` consumes only the high half of the MAU bus
(`IntegerALU.lane` reads `bus.high`), so it holds verbatim for the real bus:

* `evaluateBus_value_high_irrelevant` — `IntegerALU.evaluateBus`'s result
  depends on its second operand only through that operand's high half.
* `cendSbslData_forward` — the `sbsl` datapath on `cendMauForwardBus` writes
  `byteSwap32 w`.

### A corrected residual and the unconditional value chain

`CendTailComputationForward` is `CendTailComputation` with its `.mau` slot field
corrected to `cendMauForwardBus`.  `cendTail_of_forwardComputation` and
`cendAnswerCorrect_of_forwardTail` re-prove the value-chain assembly for it, so
the whole `Correct` argument is ready once the executor fields of the corrected
structure are supplied.

### Address lowering of the answer operands

The destination/source resolutions `$m0v`, `$r8v`, `$n[1,0,3,2]`, `$s0v` at an
arbitrary PE, cycle and BAR are computed (`cendM0_access`, `cendR8_access`,
`cendN2103_access`, `cendS0_access`).  These are the per-cycle inputs of the
integer-stage preparation of lines 2 and 3.

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-! ## 1. Cycle enumeration and the `$m0v` word index -/

/-- Every `Fin 4` is one of `0, 1, 2, 3` (no Mathlib `fin_cases` in this
project). -/
theorem cendCycle_cases (cycle : Fin 4) :
    cycle = 0 ∨ cycle = 1 ∨ cycle = 2 ∨ cycle = 3 := by
  have h := cycle.isLt
  rcases Nat.lt_or_ge cycle.val 1 with h0 | h0
  · left; exact Fin.ext (by simpa using h0)
  rcases Nat.lt_or_ge cycle.val 2 with h1 | h1
  · right; left; exact Fin.ext (by omega)
  rcases Nat.lt_or_ge cycle.val 3 with h2 | h2
  · right; right; left; exact Fin.ext (by omega)
  · right; right; right; exact Fin.ext (by omega)

/-- The LM0 address of cycle `c` seen as a `word` access with `BAR0 = 0`. -/
def cendWordIndex (c : Fin 4) : Fin Bank.lm0.capacity :=
  ⟨c.val, by have h := c.isLt; simp [Bank.capacity]; omega⟩

/-- `CendTail.cendLm0Word` at `BAR0 = 0` is the plain word index. -/
theorem cendLm0Word_zero (memory : Memory .lm0) (c : Fin 4) :
    cendLm0Word memory 0 c = memory (cendWordIndex c) := by
  unfold cendLm0Word cendWordIndex
  congr 1
  apply Fin.ext
  simp
  omega

/-! ## 2. Address lowering of the answer operands

`$m0v` reads LM0 word `(BAR0 + c) mod 4096`; `$r8v` writes GRF0 word `8 + c`;
`$n[1,0,3,2]` writes LM1 word `(BAR1 + [1,0,3,2][c]) mod 4096`; `$s0v` writes
GRF1 word `c`.  Each access is a `word` access and ignores PE, group and T. -/

theorem cendM0_access (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? cendM0 false pe cycle bar0 bar1 tWord =
      some ⟨.lm0, .word,
        ⟨(bar0.toNat + cycle.val) % 4096, Nat.mod_lt _ (by decide)⟩⟩ := by
  simp [cendM0, ParsedOperand.toDirectMemoryAccessMode?, issueBankToRegisterBank,
    parsedWidth?, parsedRegionAddressAt, Bank.capacity, Width.words]
  rcases cendCycle_cases cycle with h | h | h | h <;> rw [h] <;> rfl

theorem cendR8_access (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? cendR8 true pe cycle bar0 bar1 tWord =
      some ⟨.grf0, .word,
        ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ := by
  simp [cendR8, ParsedOperand.toDirectMemoryAccessMode?, issueBankToRegisterBank,
    parsedWidth?, parsedRegionAddressAt, Bank.capacity, Width.words]
  rcases cendCycle_cases cycle with h | h | h | h <;> rw [h] <;> rfl

theorem cendN2103_access (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? cendN2103 true pe cycle bar0 bar1 tWord =
      some ⟨.lm1, .word,
        ⟨(bar1.toNat + (cendSbslDestination cycle).val) % 4096,
          Nat.mod_lt _ (by decide)⟩⟩ := by
  simp [cendN2103, ParsedOperand.toDirectMemoryAccessMode?, issueBankToRegisterBank,
    parsedWidth?, parsedRegionAddressAt, Bank.capacity, Width.words, cendSbslDestination]
  rcases cendCycle_cases cycle with h | h | h | h <;> rw [h] <;> rfl

theorem cendS0_access (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryAccessMode? cendS0 true pe cycle bar0 bar1 tWord =
      some ⟨.grf1, .word,
        ⟨(0 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ := by
  simp [cendS0, ParsedOperand.toDirectMemoryAccessMode?, issueBankToRegisterBank,
    parsedWidth?, parsedRegionAddressAt, Bank.capacity, Width.words]
  rcases cendCycle_cases cycle with h | h | h | h <;> rw [h] <;> rfl

/-! ## 3. The `fvfma` row at the executor level -/

/-- The parsed `fvfma` row of the answer, written out (`NormalizedExpr.toParsed`
strips the display text, which is empty here anyway). -/
theorem cendFmaExpr_eq :
    cendFmaExpr.normalize.toParsed =
      ⟨.mau .f false .fma none false, [cendAluf, cendAluf, cendAluf], [cendS0], none, ""⟩ :=
  rfl

/-- **The executor's lowering of `fvfma`**: three forwarded ALU reads with no
negation/extension/rounding, one GRF1 destination. -/
theorem cendFma_lowered (ctx : ParsedIntegerContext) :
    lowerParsedFloatFma?
        ⟨.mau .f false .fma none false, [cendAluf, cendAluf, cendAluf], [cendS0], none, ""⟩ ctx =
      some ⟨.forward .aluf false, .forward .aluf false, .forward .aluf false,
        false, false, false, false, false, false, false, false, false, [cendS0]⟩ := by
  unfold lowerParsedFloatFma?
  dsimp only
  simp [cendAluf, cendS0, parsedFloatMAUSourceAttrs?, ParsedOperand.toParsedIntegerInput?,
    parsedFloatMAUDestinationRole, List.all]

/-- The single-precision FMA of three copies of the immediate word
`0x34F80010`, as the executor's `singleFmaBus` computes it. -/
theorem cendFmaBusValue :
    singleFmaBus cendImmediateBus.high cendImmediateBus.high cendImmediateBus.high =
      ((0x34F80018 : BitVec 32) ++ (0x34F80018 : BitVec 32)) := by
  simp only [singleFmaBus, cendImmediateBus, cendMauShiftWord]
  decide

/-- The bus a single-precision `fvfma` actually puts on the MAU forwarding slot:
the FMA result `0x34F80018 ++ 0x34F80018` in the high half, `0` in the low
half.  (The executor's cycle runner stores its 64-bit result as
`⟨result, 0⟩`; it never duplicates it into the low half.) -/
def cendMauForwardBus : IntegerALU.Bus :=
  ⟨(0x34F80018 : BitVec 32) ++ (0x34F80018 : BitVec 32), 0⟩

/-- **`CendTail.cendMauShiftBus` is not the executor's MAU payload.**  The value
chain of `CendTail` uses `cendMauShiftBus` (which has the FMA word in both
halves, matching `CendTail.cendMauShiftBus_eq`), while the executor installs
`cendMauForwardBus` (low half zero). -/
theorem cendMauShiftBus_ne_forward : cendMauShiftBus ≠ cendMauForwardBus := by
  intro h
  have low := congrArg IntegerALU.Bus.low h
  have zero : cendMauForwardBus.low = 0 := rfl
  rw [zero] at low
  have nonzero : cendMauShiftBus.low ≠ 0 := by decide
  exact nonzero low

/-- **The executor's `fvfma` cycle, exactly.**  With the `.alu` forwarding slot
at the cycle carrying the immediate bus, `executeParsedFloatMAUCycleAtPE` returns
the FMA bus `cendMauForwardBus` (and the unchanged register file). -/
theorem cendFmaCycle (readFiles files : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (cycle : Fin 4)
    (slotsEq : oldSlots .alu cycle = .known cendImmediateBus) :
    executeParsedFloatMAUCycleAtPE readFiles files oldSlots cendFmaExpr.normalize.toParsed
        context cycle =
      .ok (files, cendMauForwardBus,
        parsedVectorMAUFlags .single false cendMauForwardBus) := by
  rw [cendFmaExpr_eq]
  unfold executeParsedFloatMAUCycleAtPE
  simp [cendFma_lowered, ParsedIntegerInput.readWithForwarding,
    ParsedIntegerInput.forwardUnit, ParsedIntegerInput.applyRounding, slotsEq,
    cendMauForwardBus, cendFmaBusValue, parsedMauHalfSelectsPE, prepareSingleMAUSource]

/-! ## 4. The `sbsl` datapath consumes only the high half of the MAU bus -/

/-- **`IntegerALU.evaluateBus`'s result ignores the second operand's low half.**
Both the lane values and the result's high half are computed from `y.high`;
the result's low half is copied from the first operand. -/
theorem evaluateBus_value_high_irrelevant (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (r : Bool) (low : BitVec 64) :
    (IntegerALU.evaluateBus p op x ⟨y.high, low⟩ r).value =
      (IntegerALU.evaluateBus p op x y r).value := by
  cases y with
  | mk high low' => rfl

/-- **The `sbsl` datapath on the executor's real MAU bus.**  `CendTail.cendSbslData`
for `cendMauForwardBus`: the word written to LM1 is `byteSwap32 w`. -/
theorem cendSbslData_forward (w : BitVec 32) :
    (PEMemory.unpackALUBus
      (IntegerALU.evaluateBus .half (.shift .rotateLeft) (cendIbslResultBus w)
        cendMauForwardBus false).value) 0 = byteSwap32 w := by
  have hbus : cendMauForwardBus = ⟨cendMauShiftBus.high, (0 : BitVec 64)⟩ := by
    simp [cendMauForwardBus, cendMauShiftBus]
  rw [hbus, evaluateBus_value_high_irrelevant]
  exact cendSbslData w

/-- `linePreparedSlots` installs the float-MAU stage's cycle output verbatim in
the `.mau` slot when a float-MAU producer ran.  Together with `cendFmaCycle`
(and `executeParsedFloatMAUCyclesAtPE`, which stores each cycle's `output`
unchanged) this is why the `.mau` payload of line 2 is `cendMauForwardBus`, not
`cendMauShiftBus`. -/
theorem linePreparedSlots_mau (intSlots : Forwarding.Slots)
    (floatOutputs : Fin 4 → IntegerALU.Bus) (cycle : Fin 4) :
    linePreparedSlots intSlots floatOutputs true .mau cycle = .known (floatOutputs cycle) :=
  rfl

/-! ## 4b. Line 1's committed register file at PE 0

The `line1` field's register half is unconditional: line 1's result at PE 0 is
the explicit `cendLine1Files` commit.  Only the two BAR equalities remain as
hypotheses (they need the per-PE context frame of line 1's walk). -/

/-- **PE 0's register file after line 1**, for the actual result `s1` of the
line-1 step (uniqueness of `executeNormalizedLine`'s result). -/
theorem cendLine1Files_of_execution (input : BitVec 64) (s1 : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) =
      .ok s1) :
    s1.peRegisters cendPE = cendLine1Files input := by
  obtain ⟨next, lineExecuted, filesAll, _, _, _, _, _, _⟩ := cendLine1_next input
  rw [lineExecuted] at executed
  have same : next = s1 := StepResult.ok.inj executed
  subst same
  exact filesAll cendPE

/-- **Line 1's value facts from its execution**, modulo the two BAR equalities.
The register half is `cendLine1Files_of_execution`; `cendLine1Facts_of_commit`
then converts the commit pin into the LM0 input halves. -/
theorem cendLine1Facts_of_execution (input : BitVec 64) (s1 : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) =
      .ok s1)
    (bar0 : (s1.peContext cendPE).bar0 = 0)
    (bar1 : (s1.peContext cendPE).bar1 = 0) :
    CendLine1Facts input s1 :=
  cendLine1Facts_of_commit input s1 (cendLine1Files_of_execution input s1 executed) bar0 bar1

/-! ## 5. The corrected residual and the value chain

`CendTail.CendTailComputation`'s `mauSlots` field asks for
`.known cendMauShiftBus`, but the executor installs `.known cendMauForwardBus`
(§3).  The structure below is the same residual with that field corrected.  The
value-chain assembly is re-proved for it, so `Correct` follows as soon as the
executor fields of this structure are supplied. -/

/-- **The corrected tail residual.**  Identical to `CendTail.CendTailComputation`
except that line 2's `.mau` forwarding slots are the executor's actual payload
`cendMauForwardBus` rather than `cendMauShiftBus`. -/
structure CendTailComputationForward (input : BitVec 64) (s1 : State) where
  line1 : CendLine1Facts input s1
  afterTwo : State
  line2 : executeNormalizedLine (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 =
    .ok afterTwo
  aluSlots : ∀ c : Fin 4,
    stateForwardingSlots afterTwo cendPE .alu c =
      .known (cendIbslResultBus
        (cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 c))
  mauSlots : ∀ c : Fin 4,
    stateForwardingSlots afterTwo cendPE .mau c = .known cendMauForwardBus
  afterTwoBar0 : (afterTwo.peContext cendPE).bar0 = (s1.peContext cendPE).bar0
  afterTwoBar1 : (afterTwo.peContext cendPE).bar1 = (s1.peContext cendPE).bar1
  afterTwoLm0 : (afterTwo.peRegisters cendPE).lm0 = (s1.peRegisters cendPE).lm0
  afterThree : State
  line3 : executeNormalizedLine (.pe [cendSbslExpr.normalize]) afterTwo = .ok afterThree
  afterThreeLm1 : (afterThree.peRegisters cendPE).lm1 =
    cendSbslLm1 (afterTwo.peRegisters cendPE).lm1
      (fun c => byteSwap32
        (cendLm0Word (afterTwo.peRegisters cendPE).lm0 (afterTwo.peContext cendPE).bar0 c))

/-- **The value chain closes the tail from the corrected per-line computation.**
This is `CendTail.cendTail_of_computation` with the corrected MAU slot field; its
proof is identical because the `sbsl` value only depends on line 3's LM1 commit,
whose data are already given as `byteSwap32` of the LM0 words. -/
theorem cendTail_of_forwardComputation
    (computation : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      CendTailComputationForward input s1) :
    ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      ∃ result : State,
        ProofsLean.execute cendSealedMachine
            [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
             .pe [cendSbslExpr.normalize]] s1 = some result ∧
        cendOutputPair result = byteSwap64 input := by
  intro input s1 line1
  obtain ⟨facts, afterTwo, line2, aluSlots, mauSlots, afterTwoBar0, afterTwoBar1,
    afterTwoLm0, afterThree, line3, afterThreeLm1⟩ := computation input s1 line1
  refine ⟨afterThree, ?_, ?_⟩
  · have stepTwo : cendSealedMachine.step
        (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 = some afterTwo := by
      simp only [cendSealedMachine, InstructionLine.toNormalizedLine, line2]
    have stepThree : cendSealedMachine.step (.pe [cendSbslExpr.normalize]) afterTwo =
        some afterThree := by
      simp only [cendSealedMachine, InstructionLine.toNormalizedLine, line3]
    show (cendSealedMachine.step
        (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1).bind
      (fun next => ProofsLean.execute cendSealedMachine
        [.pe [cendSbslExpr.normalize]] next) = some afterThree
    rw [stepTwo]
    show (cendSealedMachine.step (.pe [cendSbslExpr.normalize]) afterTwo).bind
      (fun next => some next) = some afterThree
    rw [stepThree]
    rfl
  · unfold cendOutputPair
    rw [afterThreeLm1, cendSbslLm1_readPair]
    have hlm0 : cendLm0Word (afterTwo.peRegisters cendPE).lm0
        (afterTwo.peContext cendPE).bar0 0 = input.extractLsb' 32 32 := by
      rw [afterTwoLm0, afterTwoBar0]
      exact facts.lm0_zero
    have hlm1 : cendLm0Word (afterTwo.peRegisters cendPE).lm0
        (afterTwo.peContext cendPE).bar0 1 = input.extractLsb' 0 32 := by
      rw [afterTwoLm0, afterTwoBar0]
      exact facts.lm0_one
    rw [hlm1, hlm0]
    exact (byteSwap64_eq_byteSwap32_halves input).symm

/-- **`Correct` from the corrected per-line computation** (and line 1's
existence, which `CendLine1Walk.cendAnswerExecResidual_line1` supplies). -/
theorem cendAnswerCorrect_of_forwardTail
    (line1 : ∀ input : BitVec 64, ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next)
    (computation : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      CendTailComputationForward input s1) :
    ProofsLean.Correct cendSealedMachine cendSpec cendAnswer :=
  cendAnswerCorrect_of_residual
    (cendAnswerExecResidual_of_line1_and_tail line1
      (cendTail_of_forwardComputation computation))

/-- **`Correct` from the corrected residual in `Prop` form.**  Line 1's
existence is unconditional (`CendLine1Walk.cendAnswerExecResidual_line1`), so the
only remaining executor work is inhabiting `CendTailComputationForward`. -/
theorem cendAnswerCorrect_of_forwardResidual
    (residual : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      Nonempty (CendTailComputationForward input s1)) :
    ProofsLean.Correct cendSealedMachine cendSpec cendAnswer :=
  cendAnswerCorrect_of_forwardTail cendAnswerExecResidual_line1
    (fun input s1 line1 => (residual input s1 line1).some)

/-! ## 6. The exact residual

`CendTail.CendTailComputation` cannot be inhabited: its `mauSlots` field asks
for `.known cendMauShiftBus`, while the executor's float-MAU stage installs the
cycle outputs of `executeParsedFloatMAUCycleAtPE` (stored verbatim by
`executeParsedFloatMAUCyclesAtPE` and wrapped in `.known` by
`linePreparedSlots`), and `cendFmaCycle` computes that output to be
`cendMauForwardBus ≠ cendMauShiftBus` (`cendMauShiftBus_ne_forward`).

Consequently the exact remaining residual is:

* either prove `CendTailComputationForward` (the structure of §5, which is
  `CendTailComputation` with `mauSlots : .known cendMauForwardBus`), for every
  input and every line-1 result.  This is precisely the same executor work —
  the two 4096-PE walks of lines 2 and 3, the per-cycle integer preparation of
  the `ibsl` and `sbsl` rows, and the float-MAU stage of `fvfma` — as the
  original residual, with the `.mau` payload now the one the executor really
  installs;
* or amend `CendTail.cendMauShiftBus` to `⟨fmaWord ++ fmaWord, 0⟩` and
  `CendTailComputation.mauSlots` accordingly (the value chain is unaffected:
  `cendSbslData_forward` proves `CendSbslData` for the real bus), after which the
  original structure becomes the corrected one. -/

/-- **The residual as a `Prop`**: the corrected per-line executor computation.
This is the only missing piece for unconditional `Correct`. -/
def CendTailForwardResidual : Prop :=
  ∀ (input : BitVec 64) (s1 : State),
    executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
    Nonempty (CendTailComputationForward input s1)

/-! ## 7. Trust report -/

#print axioms cendM0_access
#print axioms cendR8_access
#print axioms cendN2103_access
#print axioms cendS0_access
#print axioms cendFma_lowered
#print axioms cendFmaCycle
#print axioms cendMauShiftBus_ne_forward
#print axioms cendSbslData_forward
#print axioms cendTail_of_forwardComputation
#print axioms cendLine1Files_of_execution
#print axioms cendLine1Facts_of_execution
#print axioms cendAnswerCorrect_of_forwardTail
#print axioms cendAnswerCorrect_of_forwardResidual

end ProofsLean.MNCore
