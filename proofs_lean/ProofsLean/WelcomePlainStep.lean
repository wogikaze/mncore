import ProofsLean.WelcomePlainClose

/-! # Assembling the plain-class per-cycle write shape

This module discharges `WelcomePEPlainStepShapeExceptImmediate`, the last
remaining obligation of `WelcomePlainShape.lean` §10 for the plain integer-ALU
class.  Together with the already-proved `welcomePEPlainImmediateDoubleObligation`
it yields `WelcomePEPlainShapeObligation` through
`welcomePEPlainShapeObligation_of_two`.

The content is the per-cycle analysis of the nine branches of
`prepareParsedIntegerALUExprCycle` at the all-zero initial state:

* every `.lm1` prepared write resolves a destination operand of the row, with
  the same access (hence the same static bank and width, and an aligned
  address);
* a `.lm1 .double` prepared write has a copied third data word;
* each cycle chunk contains at most one `.lm1` write.

The four chunks of `prepareParsedIntegerALUExprCycles_four` then give either
`Lm1WritesDoubleCopy` (when the unique `LM1` destination has width `.double`) or
`Lm1WritesNarrow` (otherwise).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 0. The all-zero initial state -/

/-- The register file of PE 0 at the all-zero initial state. -/
abbrev welcomeZeroFiles : IntegerRegisterFiles :=
  welcomeInitialPERegisters welcomeZeroWords

/-- The forwarding slots of PE 0 at the all-zero initial state. -/
abbrev welcomeZeroSlots : ProofsLean.MNCore.Forwarding.Slots :=
  stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE

/-- The preparation control of PE 0 at the all-zero initial state. -/
abbrev welcomeZeroControl : ParsedMaskExecutionControl :=
  parsedPEHazardControl (welcomeInitialState welcomeZeroWords) welcomePE

theorem welcomeZeroSlots_poison (unit : ProofsLean.MNCore.Forwarding.Unit)
    (cycle : Fin 4) : welcomeZeroSlots unit cycle = .poison :=
  welcomeZeroForwardingSlots_poison unit cycle

/-- Every coordinate of the PE 0 control is the one of `ofLinearIndex welcomePE`. -/
theorem welcomeZeroControl_context_group :
    welcomeZeroControl.context.group = (ParsedIntegerContext.ofLinearIndex welcomePE).group := rfl

theorem welcomeZeroControl_context_l2b :
    welcomeZeroControl.context.l2b = (ParsedIntegerContext.ofLinearIndex welcomePE).l2b := rfl

theorem welcomeZeroControl_context_l1b :
    welcomeZeroControl.context.l1b = (ParsedIntegerContext.ofLinearIndex welcomePE).l1b := rfl

theorem welcomeZeroControl_context_mab :
    welcomeZeroControl.context.mab = (ParsedIntegerContext.ofLinearIndex welcomePE).mab := rfl

theorem welcomeZeroControl_context_pe :
    welcomeZeroControl.context.pe = (ParsedIntegerContext.ofLinearIndex welcomePE).pe := rfl

/-- A zero low half has a copied high word. -/
theorem isWelcomeCopy_extractLsb_zero :
    IsWelcomeCopy ((0 : BitVec 64).extractLsb' 32 32) := by
  have h : (0 : BitVec 64).extractLsb' 32 32 = (0 : BitVec 32) := by decide
  rw [h]
  exact isWelcomeCopy_zero

/-- Every memory read at the all-zero initial state has a copied high word. -/
theorem welcomeZero_read_memory_copy (access : DirectMemoryAccess) (rounded : Bool) :
    IsWelcomeCopy
      ((ParsedIntegerInput.applyRounding rounded
        (pack (readDirectAccess welcomeZeroFiles access))).low.extractLsb' 32 32) := by
  have lowZero := welcomeZero_applyRounding_pack_low_zero access rounded
  rw [lowZero]
  exact isWelcomeCopy_extractLsb_zero

/-- Every `.fixed` read at PE 0 has a copied high word. -/
theorem welcomeZero_read_fixed_copy (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    IsWelcomeCopy
      ((replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision welcomeZeroControl.context.group
          welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
          welcomeZeroControl.context.mab welcomeZeroControl.context.pe)).low.extractLsb'
        32 32) := by
  rw [welcomeZeroControl_context_group, welcomeZeroControl_context_l2b,
    welcomeZeroControl_context_l1b, welcomeZeroControl_context_mab,
    welcomeZeroControl_context_pe]
  exact welcomeFixedBus_isWelcomeCopy fixed precision

/-! ## 1. The first-source reads at the all-zero state are copies

Every integer ALU source operand lowers to a `ParsedIntegerInput`.  At the
all-zero state a direct memory read is the zero bus (or its rounded form, whose
low half is zero), a `.fixed` read is the replicated constant of PE 0 (zero or
`0x80000000`/`0x80008000`), and a forwarding read cannot succeed because every
slot is still poison.  Hence every *successful* first-source read has a copied
high word of its low half — exactly the hypothesis of
`prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_read_copy`. -/

/-- The shape of a `.fixed` result of a source lowering. -/
theorem toParsedIntegerInput?_fixed_shape
    (operand : ParsedOperand) (precision : IntegerALU.Precision)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (value : IntegerALU.Bus)
    (lowered : ParsedOperand.toParsedIntegerInput? operand precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some (.fixed value)) :
    ∃ fixed, value = replicateIntegerLane precision
      (ParsedFixed.integerValue fixed precision group l2b l1b mab pe) := by
  cases operand with
  | fixed fixed =>
      have h := Option.some.inj lowered
      injection h with hv
      exact ⟨fixed, hv.symm⟩
  | mem access negated extended rounded mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | bar lm1 width mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.bar lm1 width mask) pe cycle bar0
          bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | forward kind negated extended rounded => simp [ParsedOperand.toParsedIntegerInput?] at lowered
  | omr entry mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.omr entry mask) pe cycle bar0 bar1
          tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | matrix group' width row =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.matrix group' width row) pe cycle bar0
          bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | nowrite =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? .nowrite pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | l1bm width address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l1bm width address) pe cycle bar0 bar1
          tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | l2bm address l2b' =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l2bm address l2b') pe cycle bar0 bar1
          tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
  | dar address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.dar address) pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered

/-- A successful read of a lowered source at the all-zero state has a copied
high word of its low half. -/
theorem welcomeZero_toParsedIntegerInput_read_copy
    (operand : ParsedOperand) (precision : IntegerALU.Precision)
    (cycle : Fin 4) (input : ParsedIntegerInput)
    (lowered : ParsedOperand.toParsedIntegerInput? operand precision
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some input)
    (x : IntegerALU.Bus)
    (read : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle input
      = .ok x) :
    IsWelcomeCopy (x.low.extractLsb' 32 32) := by
  cases operand with
  | fixed fixed =>
      have inputEq : input = .fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision welcomeZeroControl.context.group
            welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
            welcomeZeroControl.context.mab welcomeZeroControl.context.pe)) :=
        (Option.some.inj lowered).symm
      subst inputEq
      simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
        StepResult.ok.injEq] at read
      subst read
      exact welcomeZero_read_fixed_copy fixed precision
  | forward kind negated extended rounded =>
      have inputEq : input = .forward kind rounded := (Option.some.inj lowered).symm
      subst inputEq
      simp [ParsedIntegerInput.readWithForwarding, welcomeZeroSlots_poison] at read
  | mem access negated extended rounded mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' rounded := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' rounded
  | bar lm1 width mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.bar lm1 width mask)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | omr entry mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.omr entry mask)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | matrix group' width row =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.matrix group' width row)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | nowrite =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? .nowrite
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | l1bm width address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l1bm width address)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | l2bm address l2b' =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l2bm address l2b')
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false
  | dar address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.dar address)
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some access' =>
          have inputEq : input = .memory access' false := by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm
          subst inputEq
          simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
            StepResult.ok.injEq] at read
          subst read
          exact welcomeZero_read_memory_copy access' false

/-- **The third data word of an integer ALU evaluation is a copy** whenever the
first operand's high word is. -/
theorem data_word_two_isWelcomeCopy_of_bus
    (op : ParsedOp) (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (reduced : Bool) (selection : Option PEWordSelection)
    (copy : IsWelcomeCopy (x.low.extractLsb' 32 32))
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : op.executionRequest = .ok (.integer precision aluOp))
    (evaluated : evaluateParsedIntegerAlu op x y reduced = .ok output) :
    ∀ bound : 2 < 4, IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection output.value)) ⟨2, bound⟩) := by
  intro bound
  rw [parsed_integer_evaluation_uses_requested_semantics op precision aluOp request x y reduced]
    at evaluated
  obtain rfl := StepResult.ok.inj evaluated
  rw [unpackALUBus_word_two]
  exact parsedOutputAfterFlush_word_two_isWelcomeCopy _ _
    (evaluateBus_word_two_isWelcomeCopy precision aluOp x y reduced copy bound)

/-- **The third data word of the zero request is a copy.** -/
theorem zero_data_word_two_isWelcomeCopy (selection : Option PEWordSelection) :
    ∀ bound : 2 < 4, IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection (⟨0, 0⟩ : IntegerALU.Bus)))
        ⟨2, bound⟩) := by
  intro bound
  rw [unpackALUBus_word_two]
  exact parsedOutputAfterFlush_word_two_isWelcomeCopy _ _ isWelcomeCopy_extractLsb_zero


/-! ## 2. The lowered first source of each branch -/

/-- The first source of the direct lowering of an integer ALU row is one of the
row's source operands, lowered by `ParsedOperand.toParsedIntegerInput?`. -/
theorem toDirectMaskedIntegerAccessesInLine?_sourceX_eq
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∃ (sourceX : ParsedOperand),
      some accesses.sourceX = ParsedOperand.toParsedIntegerInput? sourceX
        parsedPrecision.laneWidth group l2b l1b mab pe cycle bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by symm; assumption⟩)


/-! ## 3. Integer ALU evaluations and their requests -/

/-- A successful evaluation of an integer ALU row uses an `.integer` request. -/
theorem alu_evaluation_is_integer
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (reduced : Bool)
    (evaluated : evaluateParsedIntegerAlu (.alu name (some parsedPrecision) unsigned arg)
      x y reduced = .ok output) :
    ∃ precision aluOp,
      (ParsedOp.alu name (some parsedPrecision) unsigned arg).executionRequest
        = .ok (.integer precision aluOp) := by
  unfold evaluateParsedIntegerAlu at evaluated
  cases h : (ParsedOp.alu name (some parsedPrecision) unsigned arg).integerRequest with
  | ok request =>
      cases request with
      | integer precision aluOp =>
          exact ⟨precision, aluOp, by simp [ParsedOp.executionRequest, h]⟩
      | unimplemented encoding => simp [ParsedOp.executionRequest, h] at evaluated
  | failure => simp [ParsedOp.executionRequest, h] at evaluated
  | unknown => simp [ParsedOp.executionRequest, h] at evaluated

/-- A successful prepared write's first read is known. -/
theorem prepareParsedMaskedWriteWithForwarding_readX_ok
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced = .ok write) :
    ∃ x, ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  cases readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp [readX] at prepared
  | unknown => simp [readX] at prepared
  | ok x => exact ⟨x, rfl⟩

/-- **The copied third data word of a direct prepared write.**  With the row's
operation an integer ALU and a copied first read, the prepared write's third data
word is a copy. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_copy
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (cycle : Fin 4) (reduced : Bool) (x : IntegerALU.Bus)
    (operation : accesses.op = .alu name (some parsedPrecision) unsigned arg)
    (readX : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceX = .ok x)
    (copy : IsWelcomeCopy (x.low.extractLsb' 32 32))
    (prepared : prepareParsedMaskedWriteWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses reduced = .ok write) :
    ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  rw [readX] at prepared
  cases readY : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceY with
  | failure => simp [readY] at prepared
  | unknown => simp [readY] at prepared
  | ok y =>
      cases evaluated : evaluateParsedIntegerAlu accesses.op x y reduced with
      | failure => simp [readY, evaluated] at prepared
      | unknown => simp [readY, evaluated] at prepared
      | ok output =>
          simp only [readY, evaluated, StepResult.ok.injEq] at prepared
          have evaluatedAlu : evaluateParsedIntegerAlu
              (.alu name (some parsedPrecision) unsigned arg) x y reduced = .ok output := by
            rw [← operation]
            exact evaluated
          obtain ⟨precision, aluOp, request⟩ :=
            alu_evaluation_is_integer name parsedPrecision unsigned arg x y output reduced evaluatedAlu
          have requestAccesses : accesses.op.executionRequest = .ok (.integer precision aluOp) := by
            rw [operation]
            exact request
          have useRequest := parsed_integer_evaluation_uses_requested_semantics accesses.op
            precision aluOp requestAccesses x y reduced
          rw [useRequest] at evaluated
          obtain rfl := StepResult.ok.inj evaluated
          intro bound
          subst prepared
          dsimp only
          rw [unpackALUBus_word_two]
          exact parsedOutputAfterFlush_word_two_isWelcomeCopy _ _
            (evaluateBus_word_two_isWelcomeCopy precision aluOp x y reduced copy bound)



/-! ## 4. Destination provenance of the mixed and multiple lowerings -/

/-- The destination access of a prepared write resolves one of the row's
destination operands (equality first, for term-mode proofs). -/
def DestResolves (expression : ParsedExpr) (cycle : Fin 4) (access : DirectMemoryAccess) : Prop :=
  ∃ destination : ParsedOperand,
    ParsedOperand.toDirectMemoryDestination? destination welcomeZeroControl.context.pe cycle
        welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord = some access ∧
      destination ∈ expression.destinations

/-- The direct lowering's destination resolves a destination operand. -/
theorem destResolves_of_direct
    (expression : ParsedExpr) (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    DestResolves expression cycle accesses.destination := by
  obtain ⟨destination, member, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord accesses lowered
  exact ⟨destination, resolved, member⟩

/-- Every destination access of the multiple-destination lowering resolves a
destination operand. -/
theorem destResolves_of_multiple
    (expression : ParsedExpr) (cycle : Fin 4)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∀ access ∈ accesses, DestResolves expression cycle access.destination := by
  intro access member
  obtain ⟨destination, memberDestination, resolved⟩ :=
    toDirectMaskedIntegerWritesInLine?_mem_provenance expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord accesses lowered access member
  exact ⟨destination, resolved, memberDestination⟩

/-- The memory-then-input lowering's memory access resolves the row's memory
destination operand. -/
theorem destResolves_of_memoryThenInput
    (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    DestResolves expression cycle accesses.memory := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by assumption, by simp⟩)

/-- The input-then-memory lowering's memory access resolves the row's memory
destination operand, which it records. -/
theorem destResolves_of_inputThenMemory
    (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ParsedOperand.toDirectMemoryDestination? accesses.memoryOperand
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses.memory ∧
      accesses.memoryOperand ∈ expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     dsimp only
     exact ⟨by assumption, by simp⟩)



/-! ## 5. The multiple-destination lowering as a `mapM` -/

/-- The multiple-destination lowering is a `mapM` of the single-destination
lowering over the row's destinations. -/
theorem toDirectMaskedIntegerWritesInLine?_mapM
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg) (cycle : Fin 4)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses) :
    expression.destinations.mapM (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle
        welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord) = some accesses := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  unfold ParsedExpr.toDirectMaskedIntegerWritesInLine? at lowered
  dsimp only at lowered
  cases destinations with
  | nil => simp at lowered
  | cons destination rest => exact lowered

/-- The head access of the multiple-destination lowering has a lowered first
source. -/
theorem toDirectMaskedIntegerWritesInLine?_head_sourceX_eq
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest)) :
    ∃ sourceX : ParsedOperand,
      some access.sourceX = ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM expression name parsedPrecision
    unsigned arg operation cycle (access :: rest) lowered
  cases destinations : expression.destinations with
  | nil => rw [destinations] at mapped; simp at mapped
  | cons destination restDestinations =>
      rw [destinations] at mapped
      obtain ⟨_, getEq⟩ := list_mapM_getElem (fun destination =>
        ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
        (destination :: restDestinations) (access :: rest) mapped
      have hd : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some access := by
        have := getEq 0 (by simp) (by simp)
        simpa using this
      exact toDirectMaskedIntegerAccessesInLine?_sourceX_eq
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
        name parsedPrecision unsigned arg operation access hd

/-- The operations of the multiple-destination lowering are the row's operation. -/
theorem toDirectMaskedIntegerWritesInLine?_op
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∀ access ∈ accesses, access.op = expression.op := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM expression name parsedPrecision
    unsigned arg operation cycle accesses lowered
  intro access member
  obtain ⟨destination, _, loweredHere⟩ :=
    list_mapM_mem (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
      expression.destinations accesses mapped access member
  cases loweredHereOne : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
  | none => rw [loweredHereOne] at loweredHere; simp at loweredHere
  | some first =>
      rw [loweredHereOne] at loweredHere
      obtain rfl := Option.some.inj loweredHere
      exact toDirectMaskedIntegerAccessesInLine?_op
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord first loweredHereOne

/-- At most one `.lm1` access among the multiple-destination lowering's
accesses. -/
theorem toDirectMaskedIntegerWritesInLine?_lm1_count_le
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    (accesses.filter (fun access => access.destination.bank == PEMemory.Bank.lm1)).length ≤ 1 := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM expression name parsedPrecision
    unsigned arg operation cycle accesses lowered
  have sound : ∀ destination access,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some access →
      access.destination.bank = PEMemory.Bank.lm1 →
      ParsedOperand.isLm1MemoryDestination destination = true := by
    intro destination access hLowered hbank
    obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord access hLowered
    simp only [List.mem_singleton] at resolvedMem
    subst resolved
    have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
    rw [resolvedEq] at static
    simp only [Option.map_some] at static
    have pair : ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, access.destination.width) := by
      rw [← static, hbank]
    exact directDestinationBankWidth_isLm1 _ _ pair
  have count := mapM_lm1_count_le (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
    ParsedOperand.isLm1MemoryDestination sound expression.destinations accesses mapped
  have one := lm1Destinations_count_le_one expression 0 nodup
  omega



/-- The first source of the memory-then-input lowering is a lowered source
operand. -/
theorem parsedIntegerMaskMemoryThenInputExprAccessesInLine?_sourceX_eq
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∃ sourceX : ParsedOperand,
      some accesses.sourceX = ParsedOperand.toParsedIntegerInput? sourceX
        parsedPrecision.laneWidth welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab welcomeZeroControl.context.pe
        cycle welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by symm; assumption⟩)

/-- The first source of the input-then-memory lowering is a lowered source
operand. -/
theorem parsedIntegerMaskInputThenMemoryExprAccessesInLine?_sourceX_eq
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∃ sourceX : ParsedOperand,
      some accesses.sourceX = ParsedOperand.toParsedIntegerInput? sourceX
        parsedPrecision.laneWidth welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab welcomeZeroControl.context.pe
        cycle welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by symm; assumption⟩)

/-! ## 6. The constant stage -/

/-- Every `.memory` constant target resolves a destination operand. -/
theorem destResolves_of_constantTargets
    (expression : ParsedExpr) (cycle : Fin 4) (targets : List ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets) :
    ∀ target ∈ targets, ∀ accesses : ParsedMaskedIntegerAccesses, target = .memory accesses →
      DestResolves expression cycle accesses.destination := by
  intro target member accesses isMemory
  obtain ⟨destination, destinationMem, loweredDestination⟩ :=
    toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord targets lowered target member
  rw [isMemory] at loweredDestination
  obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
    toDirectMaskedConstantDestination_memory_provenance expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord destination accesses loweredDestination
  simp only [List.mem_singleton] at resolvedMem
  subst resolved
  exact ⟨destination, resolvedEq, destinationMem⟩

/-- Every prepared write of the constant stage is the prepared image of one of
the targets. -/
theorem prepareParsedMaskedConstantWrites_mem (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (writes : List PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets = .ok writes) :
    ∀ write ∈ writes, ∃ target ∈ targets,
      prepareParsedConstantTarget welcomeZeroFiles cycle target = .ok write := by
  induction targets generalizing writes with
  | nil =>
      simp [prepareParsedMaskedConstantWrites] at prepared
      subst prepared
      intro write member
      simp at member
  | cons target rest ih =>
      cases head : prepareParsedConstantTarget welcomeZeroFiles cycle target with
      | failure => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | unknown => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | ok headWrite =>
          cases tail : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle rest with
          | failure => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | unknown => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | ok writes' =>
              simp only [prepareParsedMaskedConstantWrites, head, tail, StepResult.ok.injEq]
                at prepared
              subst prepared
              intro write member
              rcases List.mem_cons.mp member with same | later
              · subst same
                exact ⟨target, by simp, head⟩
              · obtain ⟨other, otherMem, otherPrepared⟩ := ih writes' tail write later
                exact ⟨other, List.mem_cons_of_mem _ otherMem, otherPrepared⟩

/-- At most one `.lm1` write among the constant stage's destination writes. -/
theorem prepareParsedMaskedConstantWrites_lm1_count_le (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (writes : List PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets = .ok writes) :
    (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
      (targets.filter ParsedConstantDestination.isLm1Target).length := by
  induction targets generalizing writes with
  | nil =>
      simp [prepareParsedMaskedConstantWrites] at prepared
      subst prepared
      simp
  | cons target rest ih =>
      cases head : prepareParsedConstantTarget welcomeZeroFiles cycle target with
      | failure => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | unknown => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | ok headWrite =>
          cases tail : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle rest with
          | failure => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | unknown => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | ok writes' =>
              simp only [prepareParsedMaskedConstantWrites, head, tail, StepResult.ok.injEq]
                at prepared
              subst prepared
              have ihle := ih writes' tail
              rw [List.filter_cons, List.filter_cons]
              cases target with
              | memory accesses =>
                  have destinationEq : headWrite.destination = some accesses.destination :=
                    prepareParsedMaskedWrite_destination welcomeZeroFiles accesses false headWrite
                      (by simpa [prepareParsedConstantTarget] using head)
                  have keepEq : PreparedParsedMaskedWrite.isLm1Write headWrite =
                      ParsedConstantDestination.isLm1Target (.memory accesses) := by
                    simp [PreparedParsedMaskedWrite.isLm1Write,
                      ParsedConstantDestination.isLm1Target, destinationEq]
                  by_cases lm1 : ParsedConstantDestination.isLm1Target (.memory accesses) = true
                  · rw [if_pos (by rw [keepEq]; exact lm1), if_pos lm1]
                    simp only [List.length_cons]
                    omega
                  · rw [if_neg (by rw [keepEq]; exact lm1), if_neg lm1]
                    omega
              | maskRegister entry =>
                  simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at head
                  subst head
                  rw [if_neg (by simp [PreparedParsedMaskedWrite.isLm1Write]),
                    if_neg (by simp [ParsedConstantDestination.isLm1Target])]
                  omega
              | noWrite =>
                  simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at head
                  subst head
                  rw [if_neg (by simp [PreparedParsedMaskedWrite.isLm1Write]),
                    if_neg (by simp [ParsedConstantDestination.isLm1Target])]
                  omega


/-! ## 7. The per-chunk shape facts -/

/-- The three per-cycle facts consumed by the four-chunk assembly: destination
provenance, the copied third data word of `.double` writes, and the `LM1`
count bound. -/
def Lm1ChunkFacts (expression : ParsedExpr) (cycle : Fin 4)
    (writes : List PreparedParsedMaskedWrite) : Prop :=
  (∀ write ∈ writes, ∀ access : DirectMemoryAccess, write.destination = some access →
      access.bank = PEMemory.Bank.lm1 → DestResolves expression cycle access) ∧
  (∀ write ∈ writes, ∀ address : Fin PEMemory.Bank.lm1.capacity,
      write.destination = some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, address⟩ →
      ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩)) ∧
  (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1

/-- A single write with no destination satisfies all three facts. -/
theorem lm1ChunkFacts_singleton_none (expression : ParsedExpr) (cycle : Fin 4)
    (write : PreparedParsedMaskedWrite) (isNone : write.destination = none) :
    Lm1ChunkFacts expression cycle [write] := by
  refine ⟨?_, ?_, ?_⟩
  · intro item member access destinationEq bank
    simp only [List.mem_singleton] at member
    subst member
    rw [isNone] at destinationEq
    simp at destinationEq
  · intro item member address destinationEq
    simp only [List.mem_singleton] at member
    subst member
    rw [isNone] at destinationEq
    simp at destinationEq
  · simp [PreparedParsedMaskedWrite.isLm1Write, isNone]

/-- **The direct branch.** -/
theorem lm1ChunkFacts_direct (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses false = .ok write) :
    Lm1ChunkFacts expression cycle [write] := by
  have destinationEq := prepareParsedMaskedWriteWithForwarding_destination welcomeZeroFiles
    welcomeZeroSlots cycle accesses false write prepared
  have provenance := destResolves_of_direct expression cycle accesses lowered
  obtain ⟨x, readX⟩ := prepareParsedMaskedWriteWithForwarding_readX_ok welcomeZeroFiles
    welcomeZeroSlots cycle accesses false write prepared
  obtain ⟨sourceX, sourceEq⟩ := toDirectMaskedIntegerAccessesInLine?_sourceX_eq expression
    welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
    (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
    welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
    welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord name parsedPrecision
    unsigned arg operation accesses lowered
  have accessesOp := toDirectMaskedIntegerAccessesInLine?_op expression
    welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
    (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
    welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
    welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord accesses lowered
  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX parsedPrecision.laneWidth
    cycle accesses.sourceX sourceEq.symm x readX
  have dataCopy := prepareParsedMaskedWriteWithForwarding_data_two_copy name parsedPrecision
    unsigned arg accesses write cycle false x (accessesOp.trans operation) readX copy prepared
  refine ⟨?_, ?_, ?_⟩
  · intro item member access destinationEq' bank
    simp only [List.mem_singleton] at member
    subst member
    rw [destinationEq] at destinationEq'
    obtain rfl := Option.some.inj destinationEq'
    exact provenance
  · intro item member address destinationEq' bound
    simp only [List.mem_singleton] at member
    subst member
    exact dataCopy bound
  · simp only [List.filter_cons, List.filter_nil, List.length_cons, List.length_nil]
    by_cases lm1 : PreparedParsedMaskedWrite.isLm1Write write = true
    · rw [if_pos lm1]; simp
    · rw [if_neg lm1]; simp

/-- The `LM1` count of the multiple-destination replication. -/
theorem replicatePreparedIntegerResult_lm1_count_le (access : ParsedMaskedIntegerAccesses)
    (rest : List ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (destinationEq : write.destination = some access.destination) :
    ((write :: replicatePreparedIntegerResult rest write).filter
        PreparedParsedMaskedWrite.isLm1Write).length ≤
      ((access :: rest).filter
        (fun item => item.destination.bank == PEMemory.Bank.lm1)).length := by
  have headEq : PreparedParsedMaskedWrite.isLm1Write write =
      (access.destination.bank == PEMemory.Bank.lm1) := by
    simp [PreparedParsedMaskedWrite.isLm1Write, destinationEq]
  have mapFilter : ∀ (items : List ParsedMaskedIntegerAccesses),
      ((items.map (fun entry =>
        ({ write with destination := some entry.destination, selection := entry.writeSelection } :
          PreparedParsedMaskedWrite))).filter PreparedParsedMaskedWrite.isLm1Write).length =
      (items.filter (fun entry => entry.destination.bank == PEMemory.Bank.lm1)).length := by
    intro items
    induction items with
    | nil => simp
    | cons item items ih =>
        simp only [List.map_cons, List.filter_cons]
        have itemEq : PreparedParsedMaskedWrite.isLm1Write
            ({ write with destination := some item.destination, selection := item.writeSelection } :
              PreparedParsedMaskedWrite) = (item.destination.bank == PEMemory.Bank.lm1) := by
          simp [PreparedParsedMaskedWrite.isLm1Write]
        rw [itemEq]
        cases hm1 : (item.destination.bank == PEMemory.Bank.lm1) <;> simp [hm1, ih]
  have lengths : (List.filter PreparedParsedMaskedWrite.isLm1Write
      (replicatePreparedIntegerResult rest write)).length =
      (List.filter (fun item => item.destination.bank == PEMemory.Bank.lm1) rest).length := by
    simpa [replicatePreparedIntegerResult] using mapFilter rest
  rw [List.filter_cons, List.filter_cons, headEq]
  cases head : (access.destination.bank == PEMemory.Bank.lm1) <;> simp [head, lengths]

/-- **The multiple-destination branch.** -/
theorem lm1ChunkFacts_multiple (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      access false = .ok write) :
    Lm1ChunkFacts expression cycle (write :: replicatePreparedIntegerResult rest write) := by
  have destinationEq := prepareParsedMaskedWriteWithForwarding_destination welcomeZeroFiles
    welcomeZeroSlots cycle access false write prepared
  have headProvenance := destResolves_of_multiple expression cycle (access :: rest) lowered
    access (by simp)
  have tailProvenance : ∀ item ∈ rest, DestResolves expression cycle item.destination := by
    intro item member
    exact destResolves_of_multiple expression cycle (access :: rest) lowered item
      (List.mem_cons_of_mem _ member)
  obtain ⟨x, readX⟩ := prepareParsedMaskedWriteWithForwarding_readX_ok welcomeZeroFiles
    welcomeZeroSlots cycle access false write prepared
  obtain ⟨sourceX, sourceEq⟩ := toDirectMaskedIntegerWritesInLine?_head_sourceX_eq expression
    name parsedPrecision unsigned arg cycle operation access rest lowered
  have accessOp := toDirectMaskedIntegerWritesInLine?_op expression name parsedPrecision
    unsigned arg cycle operation (access :: rest) lowered access (by simp)
  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX parsedPrecision.laneWidth
    cycle access.sourceX sourceEq.symm x readX
  have dataCopy := prepareParsedMaskedWriteWithForwarding_data_two_copy name parsedPrecision
    unsigned arg access write cycle false x (accessOp.trans operation) readX copy prepared
  have dataPreserved : ∀ item ∈ replicatePreparedIntegerResult rest write,
      item.data = write.data :=
    replicatePreparedIntegerResult_preserves_data rest write
  refine ⟨?_, ?_, ?_⟩
  · intro item member destinationAccess destinationEq' bank
    rcases List.mem_cons.mp member with same | later
    · subst same
      rw [destinationEq] at destinationEq'
      obtain rfl := Option.some.inj destinationEq'
      exact headProvenance
    · rcases List.mem_map.mp later with ⟨other, otherMem, otherEq⟩
      subst otherEq
      have otherDestination :
          ({ write with destination := some other.destination, selection := other.writeSelection } :
            PreparedParsedMaskedWrite).destination = some other.destination := rfl
      rw [otherDestination] at destinationEq'
      obtain rfl := Option.some.inj destinationEq'
      exact tailProvenance other otherMem
  · intro item member address destinationEq' bound
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact dataCopy bound
    · rw [dataPreserved item later]
      exact dataCopy bound
  · have count := toDirectMaskedIntegerWritesInLine?_lm1_count_le expression name
      parsedPrecision unsigned arg cycle operation nodup (access :: rest) lowered
    have bound := replicatePreparedIntegerResult_lm1_count_le access rest write destinationEq
    omega



/-- **The memory-then-input branch.** -/
theorem lm1ChunkFacts_memoryThenInput (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
      welcomeZeroFiles welcomeZeroSlots cycle accesses flushSelection false
      = .ok (memoryWrites, omrWrite)) :
    Lm1ChunkFacts expression cycle (memoryWrites ++ [omrWrite]) := by
  have provenance := destResolves_of_memoryThenInput expression cycle name parsedPrecision
    unsigned arg operation accesses lowered
  obtain ⟨sourceX, sourceEq⟩ := parsedIntegerMaskMemoryThenInputExprAccessesInLine?_sourceX_eq
    expression name parsedPrecision unsigned arg cycle operation accesses lowered
  unfold prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceX with
  | failure => simp [hx] at prepared
  | unknown => simp [hx] at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
          accesses.sourceY with
      | failure => simp [hx, hy] at prepared
      | unknown => simp [hx, hy] at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y false with
          | failure => simp [hx, hy, he] at prepared
          | unknown => simp [hx, hy, he] at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨writesEq, producerEq⟩ := prepared
              subst writesEq
              have omrNone : omrWrite.destination = none := by rw [← producerEq]
              have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX
                parsedPrecision.laneWidth cycle accesses.sourceX sourceEq.symm x hx
              obtain ⟨precision, aluOp, integerRequest⟩ := accesses.hasIntegerRequest
              have request := integer_request_is_execution_request accesses.op precision aluOp
                integerRequest
              have dataCopy : ∀ bound : 2 < 4,
                  IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection
                    output.value)) ⟨2, bound⟩) :=
                data_word_two_isWelcomeCopy_of_bus accesses.op x y output false flushSelection
                  copy precision aluOp request he
              refine ⟨?_, ?_, ?_⟩
              · intro item member access destinationEq bank
                rcases List.mem_append.mp member with earlier | later
                · simp only [List.mem_singleton] at earlier
                  subst item
                  simp only [List.mem_singleton] at destinationEq
                  obtain rfl := Option.some.inj destinationEq
                  exact provenance
                · simp only [List.mem_singleton] at later
                  subst item
                  rw [omrNone] at destinationEq
                  simp at destinationEq
              · intro item member address destinationEq bound
                rcases List.mem_append.mp member with earlier | later
                · simp only [List.mem_singleton] at earlier
                  subst item
                  exact dataCopy bound
                · simp only [List.mem_singleton] at later
                  subst item
                  rw [omrNone] at destinationEq
                  simp at destinationEq
              · have omrFilter : [omrWrite].filter PreparedParsedMaskedWrite.isLm1Write = [] := by
                  rw [List.filter_eq_nil_iff]
                  intro item member
                  simp only [List.mem_singleton] at member
                  subst item
                  simp [PreparedParsedMaskedWrite.isLm1Write, omrNone]
                rw [List.filter_append, omrFilter, List.append_nil]
                rw [List.filter_cons, List.filter_nil]
                split <;> simp



/-- **The input-then-memory branch.** -/
theorem lm1ChunkFacts_inputThenMemory (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
      welcomeZeroFiles welcomeZeroSlots cycle accesses welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) flushSelection false
      = .ok (memoryWrites, omrWrite)) :
    Lm1ChunkFacts expression cycle memoryWrites := by
  obtain ⟨memoryResolution, memoryMember⟩ := destResolves_of_inputThenMemory expression cycle
    name parsedPrecision unsigned arg operation accesses lowered
  have memoryProvenance : DestResolves expression cycle accesses.memory :=
    ⟨accesses.memoryOperand, memoryResolution, memoryMember⟩
  obtain ⟨sourceX, sourceEq⟩ := parsedIntegerMaskInputThenMemoryExprAccessesInLine?_sourceX_eq
    expression name parsedPrecision unsigned arg cycle operation accesses lowered
  unfold prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceX with
  | failure => simp [hx] at prepared
  | unknown => simp [hx] at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
          accesses.sourceY with
      | failure => simp [hx, hy] at prepared
      | unknown => simp [hx, hy] at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y false with
          | failure => simp [hx, hy, he] at prepared
          | unknown => simp [hx, hy, he] at prepared
          | ok output =>
              cases hm : ParsedOperand.resolveMemoryWriteSelection? accesses.memoryOperand
                  accesses.memory.bank
                  (ProofsLean.MNCore.Masks.writeRegister welcomeZeroFiles.maskRegisters
                    accesses.destination cycle
                    (BitVec.ofBoolListLE
                      [output.flags 0, output.flags 1, output.flags 2, output.flags 3])
                    accesses.omrSelection)
                  cycle welcomeZeroControl.directive
                  (parsedExprHasSingleLineWriteMask expression) with
              | none => simp [hx, hy, he, hm] at prepared
              | some memorySelection =>
                  simp only [hx, hy, he, hm, StepResult.ok.injEq, Prod.mk.injEq] at prepared
                  obtain ⟨writesEq, producerEq⟩ := prepared
                  subst writesEq
                  have omrNone : omrWrite.destination = none := by rw [← producerEq]
                  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX
                    parsedPrecision.laneWidth cycle accesses.sourceX sourceEq.symm x hx
                  obtain ⟨precision, aluOp, integerRequest⟩ := accesses.hasIntegerRequest
                  have request := integer_request_is_execution_request accesses.op precision aluOp
                    integerRequest
                  have dataCopy : ∀ bound : 2 < 4,
                      IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection
                        output.value)) ⟨2, bound⟩) :=
                    data_word_two_isWelcomeCopy_of_bus accesses.op x y output false flushSelection
                      copy precision aluOp request he
                  refine ⟨?_, ?_, ?_⟩
                  · intro item member access destinationEq bank
                    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                      at member
                    rcases member with same | same
                    · subst item
                      simp at destinationEq
                    · subst item
                      obtain rfl := Option.some.inj destinationEq
                      exact memoryProvenance
                  · intro item member address destinationEq bound
                    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                      at member
                    rcases member with same | same
                    · subst item
                      simp at destinationEq
                    · subst item
                      exact dataCopy bound
                  · rw [List.filter_cons, List.filter_cons, List.filter_nil]
                    simp only [PreparedParsedMaskedWrite.isLm1Write]
                    by_cases h : accesses.memory.bank = PEMemory.Bank.lm1 <;> simp [h]



/-- The prepared write of a `.zero` row has a copied third data word. -/
theorem prepareParsedMaskedWrite_zero_data_two_copy
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (opZero : accesses.op = .zero)
    (prepared : prepareParsedMaskedWrite welcomeZeroFiles accesses false = .ok write) :
    ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
  intro bound
  obtain ⟨x, y, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedMaskedWrite_data welcomeZeroFiles accesses false write prepared
  rw [opZero] at evaluated
  obtain rfl := StepResult.ok.inj evaluated
  rw [dataEq]
  exact zero_data_word_two_isWelcomeCopy _ bound

/-- A `.memory` constant destination carries the row's operation. -/
theorem toDirectMaskedConstantDestination?_default_op
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand)
    (notNowrite : destination ≠ .nowrite)
    (notOmr : ∀ entry mask, destination ≠ .omr entry mask)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    accesses.op = expression.op := by
  rw [toDirectMaskedConstantDestination?_eq_bind expression registers directive hasSingleLineMask
    group l2b l1b mab pe cycle bar0 bar1 tWord destination notNowrite notOmr] at lowered
  cases hLowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { expression with destinations := [destination] } registers directive hasSingleLineMask
      group l2b l1b mab pe cycle bar0 bar1 tWord with
  | none => rw [hLowered] at lowered; simp at lowered
  | some val =>
      rw [hLowered] at lowered
      simp only [Option.bind, Option.some.injEq] at lowered
      injection lowered with hEq
      simpa [hEq] using toDirectMaskedIntegerAccessesInLine?_op
        { expression with destinations := [destination] } registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord val hLowered

/-- A `.memory` constant destination carries the row's operation (all operand
shapes). -/
theorem toDirectMaskedConstantDestination?_memory_op
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    accesses.op = expression.op := by
  cases destination with
  | nowrite => simp [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
  | omr entry mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases hEntry : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none =>
          rw [hEntry] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some maskEntry =>
          cases hSelection : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask) registers
              cycle directive hasSingleLineMask with
          | none =>
              rw [hEntry, hSelection] at lowered
              simp only [Bind.bind, Option.bind] at lowered
              simp at lowered
          | some selection =>
              rw [hEntry, hSelection] at lowered
              simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
              simp at lowered
  | mem access negated extended rounded mask =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | bar lm1 width mask =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | forward kind negated extended rounded =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | fixed kind =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | matrix group' width row =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | l1bm width address =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | l2bm address l2b' =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered
  | dar address =>
      exact toDirectMaskedConstantDestination?_default_op expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord _ (by simp) (by simp)
        accesses lowered


/-- The destination provenance and count facts shared by the two constant
branches. -/
theorem lm1ChunkFacts_constant_provenance_and_count
    (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none)
    (destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets) :
    (∀ write ∈ destinationWrites ++ [producerWrite], ∀ access : DirectMemoryAccess,
        write.destination = some access → access.bank = PEMemory.Bank.lm1 →
        DestResolves expression cycle access) ∧
      ((destinationWrites ++ [producerWrite]).filter
        PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 := by
  have targetProvenance := destResolves_of_constantTargets expression cycle targets lowered
  have destinations := prepareParsedMaskedConstantWrites_destinations welcomeZeroFiles cycle
    targets destinationWrites prepared
  refine ⟨?_, ?_⟩
  · intro write member access destinationEq bank
    rcases List.mem_append.mp member with earlier | later
    · rcases destinations write earlier with isNone | ⟨target, targetMem, accesses, isMemory,
        writeDestination⟩
      · rw [isNone] at destinationEq
        simp at destinationEq
      · rw [writeDestination] at destinationEq
        obtain rfl := Option.some.inj destinationEq
        exact targetProvenance target targetMem accesses isMemory
    · simp only [List.mem_singleton] at later
      subst later
      rw [producerNone] at destinationEq
      simp at destinationEq
  · have producerFilter : [producerWrite].filter
        PreparedParsedMaskedWrite.isLm1Write = [] := by
      rw [List.filter_eq_nil_iff]
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp [PreparedParsedMaskedWrite.isLm1Write, producerNone]
    have count := prepareParsedMaskedConstantWrites_lm1_count_le cycle targets destinationWrites
      prepared
    have targetBound := constantTargets_lm1_count_le expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord expression.destinations targets
      destinationsLowered
    have targetBound' : (targets.filter ParsedConstantDestination.isLm1Target).length ≤
        (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length :=
      targetBound
    have one := lm1Destinations_count_le_one expression 0 nodup
    rw [List.filter_append, producerFilter, List.append_nil]
    omega

/-- **The `.zero` constant branch.** -/
theorem lm1ChunkFacts_zero (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (isZero : expression.op = .zero)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none) :
    Lm1ChunkFacts expression cycle (destinationWrites ++ [producerWrite]) := by
  have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets := by
    unfold ParsedExpr.toDirectMaskedConstantWrites? at lowered
    rw [isZero] at lowered
    simpa using lowered
  obtain ⟨provenance, count⟩ := lm1ChunkFacts_constant_provenance_and_count expression cycle
    targets destinationWrites producerWrite lowered prepared nodup producerNone destinationsLowered
  have mem := prepareParsedMaskedConstantWrites_mem cycle targets destinationWrites prepared
  refine ⟨provenance, ?_, count⟩
  intro write member address destinationEq bound
  rcases List.mem_append.mp member with earlier | later
  · obtain ⟨target, targetMem, targetPrepared⟩ := mem write earlier
    cases target with
    | memory accesses' =>
        have preparedWrite : prepareParsedMaskedWrite welcomeZeroFiles accesses' false
            = .ok write := by
          simpa [prepareParsedConstantTarget] using targetPrepared
        obtain ⟨destination, destinationMem, loweredDestination⟩ :=
          toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord targets lowered
            (.memory accesses') targetMem
        have opZero : accesses'.op = .zero := by
          rw [toDirectMaskedConstantDestination?_memory_op expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord destination accesses'
            loweredDestination, isZero]
        exact prepareParsedMaskedWrite_zero_data_two_copy accesses' write opZero preparedWrite bound
    | maskRegister entry =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
    | noWrite =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
  · simp only [List.mem_singleton] at later
    subst later
    rw [producerNone] at destinationEq
    simp at destinationEq

/-- **The `.immediate` constant branch.**  Here the `LM1 .double` case cannot
arise, because the escaping immediate-double configuration is excluded. -/
theorem lm1ChunkFacts_immediate (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (payload : BitVec 32) (sparse : Bool)
    (isImmediate : expression.op = .immediate payload sparse)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none)
    (notDouble : ∀ d ∈ expression.destinations,
      ParsedOperand.directDestinationBankWidth? d ≠
        some (PEMemory.Bank.lm1, PEMemory.Width.double)) :
    Lm1ChunkFacts expression cycle (destinationWrites ++ [producerWrite]) := by
  have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets := by
    unfold ParsedExpr.toDirectMaskedConstantWrites? at lowered
    rw [isImmediate] at lowered
    simpa using lowered
  obtain ⟨provenance, count⟩ := lm1ChunkFacts_constant_provenance_and_count expression cycle
    targets destinationWrites producerWrite lowered prepared nodup producerNone destinationsLowered
  have mem := prepareParsedMaskedConstantWrites_mem cycle targets destinationWrites prepared
  refine ⟨provenance, ?_, count⟩
  intro write member address destinationEq bound
  rcases List.mem_append.mp member with earlier | later
  · obtain ⟨target, targetMem, targetPrepared⟩ := mem write earlier
    cases target with
    | memory accesses' =>
        have preparedWrite : prepareParsedMaskedWrite welcomeZeroFiles accesses' false
            = .ok write := by
          simpa [prepareParsedConstantTarget] using targetPrepared
        have preparedDestination : write.destination = some accesses'.destination :=
          prepareParsedMaskedWrite_destination welcomeZeroFiles accesses' false write preparedWrite
        have accessesDestination : accesses'.destination =
            ⟨PEMemory.Bank.lm1, PEMemory.Width.double, address⟩ := by
          rw [preparedDestination] at destinationEq
          exact Option.some.inj destinationEq
        obtain ⟨destination, destinationMem, loweredDestination⟩ :=
          toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord targets lowered
            (.memory accesses') targetMem
        obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
          toDirectMaskedConstantDestination_memory_provenance expression
            welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
            (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
            welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
            welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
            welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
            welcomeZeroControl.context.tWord destination accesses' loweredDestination
        simp only [List.mem_singleton] at resolvedMem
        rw [resolvedMem] at resolvedEq
        have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
        rw [resolvedEq] at static
        simp only [Option.map_some] at static
        have pair : ParsedOperand.directDestinationBankWidth? destination =
            some (PEMemory.Bank.lm1, PEMemory.Width.double) := by
          rw [← static, accessesDestination]
        exact absurd pair (notDouble destination destinationMem)
    | maskRegister entry =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
    | noWrite =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
  · simp only [List.mem_singleton] at later
    subst later
    rw [producerNone] at destinationEq
    simp at destinationEq




/-! ## 8. Branch inversions of the cycle preparation

Each branch lemma takes the exact lowering that fired and the successful cycle
preparation, extracts the returned write list, and hands over to the per-branch
shape facts of section 7. -/

/-- The direct-access branch. -/
theorem chunkFacts_of_direct
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedMaskedIntegerAccesses) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_direct _ cycle name parsedPrecision unsigned arg rfl accesses write
        lowered preparedWrite

/-- The multiple-destination branch. -/
theorem chunkFacts_of_multiple
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest))
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_multiple _ cycle name parsedPrecision unsigned arg rfl nodup access rest
        write lowered preparedWrite

/-- The OMR-mask branch. -/
theorem chunkFacts_of_omr
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskAccesses) (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, lowered, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerMaskALUWriteWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses flushSelection false write preparedWrite)

/-- The no-write branch. -/
theorem chunkFacts_of_noWrite
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerNoWriteAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerNoWriteALUWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses false write preparedWrite)

/-- The BAR branch. -/
theorem chunkFacts_of_bar
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerBarAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerBarExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerBarALUWithForwarding_destination_none welcomeZeroFiles welcomeZeroSlots cycle accesses false write
          preparedWrite)

/-- The mask-input branch. -/
theorem chunkFacts_of_maskInput
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskInputAccesses) (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, lowered, flushResolved]
    at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses flushSelection false write preparedWrite)

/-- The memory-then-input branch. -/
theorem chunkFacts_of_memoryThenInput
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, inputFailed, lowered,
    flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i memoryWrites omrWrite preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_memoryThenInput _ cycle name parsedPrecision unsigned arg rfl
        accesses flushSelection memoryWrites omrWrite lowered preparedWrite

/-- The input-then-memory branch. -/
theorem chunkFacts_of_inputThenMemory
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive (parsedExprHasSingleLineWriteMask expression)
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (memoryThenInputFailed : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, inputFailed,
    memoryThenInputFailed, lowered, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i memoryWrites omrWrite preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_inputThenMemory _ cycle name parsedPrecision unsigned arg rfl
        accesses flushSelection memoryWrites omrWrite lowered preparedWrite

/-- The `.zero` constant branch. -/
theorem chunkFacts_of_zero
    (expression : ParsedExpr) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression = ⟨.zero, sources, destinations, flush, text⟩)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (preparedWrites : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  rw [preparedWrites, zero_has_execution_request, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i slots' updated
    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
    obtain ⟨writesEq, _⟩ := prep
    subst writesEq
    exact lm1ChunkFacts_zero _ cycle targets destinationWrites _
      rfl lowered preparedWrites nodup rfl

/-- The `.immediate` constant branch. -/
theorem chunkFacts_of_immediate
    (expression : ParsedExpr) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (payload : BitVec 32) (sparse : Bool)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.immediate payload sparse, sources, destinations, flush, text⟩)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : ∀ d ∈ destinations, ParsedOperand.directDestinationBankWidth? d ≠
      some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression) welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (preparedWrites : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl (parsedExprHasSingleLineWriteMask expression) noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  rw [preparedWrites, immediate_has_execution_request, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i slots' updated
    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
    obtain ⟨writesEq, _⟩ := prep
    subst writesEq
    exact lm1ChunkFacts_immediate _ cycle targets destinationWrites _ payload sparse rfl
      lowered preparedWrites nodup rfl (fun d member => notDouble d member)

/-! ## 9. The per-cycle chunk lemma -/

/-- **Every cycle chunk satisfies the three shape facts.**  The branch
inversions above are dispatched by a case analysis on which lowering fires. -/
theorem prepareParsedIntegerALUExprCycle_lm1_facts
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (notDouble : ∀ payload sparse, op = .immediate payload sparse → ∀ d ∈ destinations,
      ParsedOperand.directDestinationBankWidth? d ≠
        some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : ((⟨op, sources, destinations, flush, text⟩ : ParsedExpr).toIssueExpr 0).writeBanks.Nodup)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots
      ⟨op, sources, destinations, flush, text⟩ welcomeZeroControl
      (parsedExprHasSingleLineWriteMask ⟨op, sources, destinations, flush, text⟩)
      noForward false cycle = .ok (writes, slots)) :
    Lm1ChunkFacts ⟨op, sources, destinations, flush, text⟩ cycle writes := by
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none =>
          cases destinations with
          | nil =>
              simp only [prepareParsedIntegerALUExprCycle,
                ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
                ParsedExpr.toDirectMaskedIntegerWritesInLine?,
                parsedIntegerMaskExprAccessesInLine?,
                parsedIntegerNoWriteExprAccessesInLine?,
                parsedIntegerBarExprAccessesInLine?,
                parsedIntegerMaskInputExprAccessesInLine?,
                parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
                parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at prep
              simp at prep
          | cons destination rest =>
              simp only [prepareParsedIntegerALUExprCycle,
                ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
                ParsedExpr.toDirectMaskedIntegerWritesInLine?,
                parsedIntegerMaskExprAccessesInLine?,
                parsedIntegerNoWriteExprAccessesInLine?,
                parsedIntegerBarExprAccessesInLine?,
                parsedIntegerMaskInputExprAccessesInLine?,
                parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
                parsedIntegerMaskInputThenMemoryExprAccessesInLine?,
                List.mapM_cons] at prep
              cases destination with
              | omr entry mask =>
                  cases rest with
                  | nil =>
                      cases entry with
                      | mk value valueLt => cases value <;> simp at prep
                  | cons item items => simp at prep
              | mem access negated extended rounded mask => simp at prep
              | bar lm1 width mask => simp at prep
              | forward kind negated extended rounded => simp at prep
              | fixed kind => simp at prep
              | matrix group width row => simp at prep
              | nowrite => simp at prep
              | l1bm width address => simp at prep
              | l2bm address l2b => simp at prep
              | dar address => simp at prep
      | some parsedPrecision =>
          cases hdirect : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
              ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
              welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
              (parsedExprHasSingleLineWriteMask
                ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush,
                  text⟩)
              welcomeZeroControl.context.group welcomeZeroControl.context.l2b
              welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
              welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
              welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
          | some accesses =>
              exact chunkFacts_of_direct _ name parsedPrecision unsigned arg sources destinations
                flush text noForward cycle nextSlots accesses writes slots rfl hdirect prep
          | none =>
              cases hmultiple : ParsedExpr.toDirectMaskedIntegerWritesInLine?
                  ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush,
                    text⟩ welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
                  (parsedExprHasSingleLineWriteMask
                    ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                      flush, text⟩)
                  welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                  welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                  welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                  welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
              | some accessList =>
                  cases accessList with
                  | nil => simp [prepareParsedIntegerALUExprCycle, hdirect, hmultiple] at prep
                  | cons access rest =>
                      exact chunkFacts_of_multiple _ name parsedPrecision unsigned arg sources
                        destinations flush text noForward cycle nextSlots access rest writes slots
                        rfl hdirect nodup hmultiple prep
              | none =>
                  cases homr : parsedIntegerMaskExprAccessesInLine?
                      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                        flush, text⟩ welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
                      (parsedExprHasSingleLineWriteMask
                        ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                          flush, text⟩)
                      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                  | some omrAccesses =>
                      cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters
                          cycle with
                      | none =>
                          simp [prepareParsedIntegerALUExprCycle, hdirect, hmultiple, homr,
                            hflush] at prep
                      | some flushSelection =>
                          exact chunkFacts_of_omr _ name parsedPrecision unsigned arg sources
                            destinations flush text noForward cycle nextSlots omrAccesses
                            flushSelection writes slots rfl hdirect hmultiple homr hflush prep
                  | none =>
                      cases hnoWrite : parsedIntegerNoWriteExprAccessesInLine?
                          ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                            flush, text⟩ welcomeZeroFiles.maskRegisters
                          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.group
                          welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
                          welcomeZeroControl.context.mab welcomeZeroControl.context.bar0
                          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                      | some noWriteAccesses =>
                          exact chunkFacts_of_noWrite _ name parsedPrecision unsigned arg sources
                            destinations flush text noForward cycle nextSlots noWriteAccesses
                            writes slots rfl hdirect hmultiple homr hnoWrite prep
                      | none =>
                          cases hbar : parsedIntegerBarExprAccessesInLine?
                              ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
                              welcomeZeroControl.directive
                              (parsedExprHasSingleLineWriteMask
                                ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                  destinations, flush, text⟩)
                              welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                              welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                              welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                              welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                          | some barAccesses =>
                              exact chunkFacts_of_bar _ name parsedPrecision unsigned arg
                                sources destinations flush text noForward cycle nextSlots
                                barAccesses writes slots rfl hdirect hmultiple homr hnoWrite hbar
                                prep
                          | none =>
                              cases hinput : parsedIntegerMaskInputExprAccessesInLine?
                                  ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                    destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
                                  welcomeZeroControl.directive
                                  (parsedExprHasSingleLineWriteMask
                                    ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                      destinations, flush, text⟩)
                                  welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                                  welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                                  welcomeZeroControl.context.pe cycle
                                  welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
                                  welcomeZeroControl.context.tWord with
                              | some inputAccesses =>
                                  cases hflush : resolveFlushSelection? flush
                                      welcomeZeroFiles.maskRegisters cycle with
                                  | none =>
                                      simp [prepareParsedIntegerALUExprCycle, hdirect,
                                        hmultiple, homr, hnoWrite, hbar, hinput, hflush] at prep
                                  | some flushSelection =>
                                      exact chunkFacts_of_maskInput _ name parsedPrecision
                                        unsigned arg sources destinations flush text noForward
                                        cycle nextSlots inputAccesses flushSelection writes slots
                                        rfl hdirect hmultiple homr hnoWrite hbar hflush hinput
                                        prep
                              | none =>
                                  cases hmixed :
                                      parsedIntegerMaskMemoryThenInputExprAccessesInLine?
                                        ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                          destinations, flush, text⟩
                                        welcomeZeroFiles.maskRegisters
                                        welcomeZeroControl.directive
                                        (parsedExprHasSingleLineWriteMask
                                          ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                            destinations, flush, text⟩)
                                        welcomeZeroControl.context.group
                                        welcomeZeroControl.context.l2b
                                        welcomeZeroControl.context.l1b
                                        welcomeZeroControl.context.mab
                                        welcomeZeroControl.context.pe cycle
                                        welcomeZeroControl.context.bar0
                                        welcomeZeroControl.context.bar1
                                        welcomeZeroControl.context.tWord with
                                  | some mixedAccesses =>
                                      cases hflush : resolveFlushSelection? flush
                                          welcomeZeroFiles.maskRegisters cycle with
                                      | none =>
                                          simp [prepareParsedIntegerALUExprCycle, hdirect,
                                            hmultiple, homr, hnoWrite, hbar, hinput, hmixed,
                                            hflush] at prep
                                      | some flushSelection =>
                                          exact chunkFacts_of_memoryThenInput _ name
                                            parsedPrecision unsigned arg sources destinations
                                            flush text noForward cycle nextSlots mixedAccesses
                                            flushSelection writes slots rfl hdirect hmultiple
                                            homr hnoWrite hbar hinput hmixed hflush prep
                                  | none =>
                                      cases hreverse :
                                          parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                            ⟨.alu name (some parsedPrecision) unsigned arg,
                                              sources, destinations, flush, text⟩
                                            welcomeZeroFiles.maskRegisters
                                            welcomeZeroControl.directive
                                            (parsedExprHasSingleLineWriteMask
                                              ⟨.alu name (some parsedPrecision) unsigned arg,
                                                sources, destinations, flush, text⟩)
                                            welcomeZeroControl.context.group
                                            welcomeZeroControl.context.l2b
                                            welcomeZeroControl.context.l1b
                                            welcomeZeroControl.context.mab
                                            welcomeZeroControl.context.pe cycle
                                            welcomeZeroControl.context.bar0
                                            welcomeZeroControl.context.bar1
                                            welcomeZeroControl.context.tWord with
                                      | some reverseAccesses =>
                                          cases hflush : resolveFlushSelection? flush
                                              welcomeZeroFiles.maskRegisters cycle with
                                          | none =>
                                              simp [prepareParsedIntegerALUExprCycle, hdirect,
                                                hmultiple, homr, hnoWrite, hbar, hinput,
                                                hmixed, hreverse, hflush] at prep
                                          | some flushSelection =>
                                              exact chunkFacts_of_inputThenMemory _ name
                                                parsedPrecision unsigned arg sources
                                                destinations flush text noForward cycle
                                                nextSlots reverseAccesses flushSelection writes
                                                slots rfl hdirect hmultiple homr hnoWrite hbar
                                                hinput hmixed hreverse hflush prep
                                      | none =>
                                          unfold prepareParsedIntegerALUExprCycle at prep
                                          dsimp only at prep
                                          rw [hdirect, hmultiple, homr, hnoWrite, hbar, hinput,
                                            hmixed, hreverse] at prep
                                          dsimp only at prep
                                          cases destinations with
                                          | nil => simp at prep
                                          | cons destination rest =>
                                              cases destination with
                                              | omr entry mask =>
                                                  cases rest with
                                                  | nil =>
                                                      cases entry with
                                                      | mk value valueLt =>
                                                          cases value <;> simp at prep
                                                  | cons item items => simp at prep
                                              | mem access negated extended rounded mask =>
                                                  simp at prep
                                              | bar lm1 width mask => simp at prep
                                              | forward kind negated extended rounded =>
                                                  simp at prep
                                              | fixed kind => simp at prep
                                              | matrix group width row => simp at prep
                                              | nowrite => simp at prep
                                              | l1bm width address => simp at prep
                                              | l2bm address l2b => simp at prep
                                              | dar address => simp at prep
  | zero =>
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.zero, sources, destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive
          (parsedExprHasSingleLineWriteMask ⟨.zero, sources, destinations, flush, text⟩)
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none =>
          simp [prepareParsedIntegerALUExprCycle, hlowered] at prep
      | some targets =>
          cases hprepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | ok destinationWrites =>
              cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle with
              | none =>
                  unfold prepareParsedIntegerALUExprCycle at prep
                  dsimp only at prep
                  rw [hlowered] at prep
                  dsimp only at prep
                  rw [hprepared, zero_has_execution_request, hflush] at prep
                  simp at prep
              | some flushSelection =>
                  exact chunkFacts_of_zero _ sources destinations flush text noForward cycle
                    nextSlots targets destinationWrites flushSelection writes slots rfl nodup
                    hlowered hprepared hflush prep
  | immediate payload sparse =>
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩
          welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
          (parsedExprHasSingleLineWriteMask
            ⟨.immediate payload sparse, sources, destinations, flush, text⟩)
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none =>
          simp [prepareParsedIntegerALUExprCycle, hlowered] at prep
      | some targets =>
          cases hprepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | ok destinationWrites =>
              cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle with
              | none =>
                  unfold prepareParsedIntegerALUExprCycle at prep
                  dsimp only at prep
                  rw [hlowered] at prep
                  dsimp only at prep
                  rw [hprepared, immediate_has_execution_request, hflush] at prep
                  simp at prep
              | some flushSelection =>
                  exact chunkFacts_of_immediate _ sources destinations flush text noForward cycle
                    nextSlots payload sparse targets destinationWrites flushSelection writes slots
                    rfl nodup (fun d member => notDouble payload sparse rfl d member) hlowered
                    hprepared hflush prep
  | mau precision matrix kind half round => simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixWrite precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixRead precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | wait tag => simp [prepareParsedIntegerALUExprCycle] at prep
  | noforward => simp [prepareParsedIntegerALUExprCycle] at prep
  | l1bm operation => simp [prepareParsedIntegerALUExprCycle] at prep
  | l2bm operation => simp [prepareParsedIntegerALUExprCycle] at prep

/-! ## 10. Assembly of the four chunks -/

/-- **The `LM1` width is cycle-independent.**  Two `.lm1` writes resolved at any
cycles resolve the same destination operand (the unique `.lm1` destination), so
their widths agree. -/
theorem destResolves_width_eq
    (expression : ParsedExpr) (cycle cycle' : Fin 4) (a b : DirectMemoryAccess)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (ha : DestResolves expression cycle a) (hb : DestResolves expression cycle' b)
    (bankA : a.bank = PEMemory.Bank.lm1) (bankB : b.bank = PEMemory.Bank.lm1) :
    a.width = b.width := by
  obtain ⟨da, resa, mema⟩ := ha
  obtain ⟨db, resb, memb⟩ := hb
  obtain ⟨ia, hia, ae⟩ := List.mem_iff_getElem.mp mema
  obtain ⟨ib, hib, be⟩ := List.mem_iff_getElem.mp memb
  have staticA := ParsedOperand.toDirectMemoryDestination?_bankWidth da
    welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
  rw [resa] at staticA
  simp only [Option.map_some] at staticA
  have staticB := ParsedOperand.toDirectMemoryDestination?_bankWidth db
    welcomeZeroControl.context.pe cycle' welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
  rw [resb] at staticB
  simp only [Option.map_some] at staticB
  have pairA : ParsedOperand.directDestinationBankWidth? da =
      some (PEMemory.Bank.lm1, a.width) := by
    rw [← staticA, bankA]
  have pairB : ParsedOperand.directDestinationBankWidth? db =
      some (PEMemory.Bank.lm1, b.width) := by
    rw [← staticB, bankB]
  have pairA' : ParsedOperand.directDestinationBankWidth?
      expression.destinations[(⟨ia, hia⟩ : Fin expression.destinations.length)] =
        some (PEMemory.Bank.lm1, a.width) := by
    have h := pairA
    first
      | (rw [ae] at h; exact h)
      | (rw [← ae] at h; exact h)
  have pairB' : ParsedOperand.directDestinationBankWidth?
      expression.destinations[(⟨ib, hib⟩ : Fin expression.destinations.length)] =
        some (PEMemory.Bank.lm1, b.width) := by
    have h := pairB
    first
      | (rw [be] at h; exact h)
      | (rw [← be] at h; exact h)
  have same := lm1Destinations_unique_positions expression 0 nodup ⟨ia, hia⟩ ⟨ib, hib⟩
    a.width b.width pairA' pairB'
  have dEq : da = db := by
    have key := congrArg (fun index : Fin expression.destinations.length =>
      expression.destinations[index]) same
    first
      | (rw [ae, be]; exact key)
      | (rw [← ae, ← be]; exact key)
  rw [dEq] at pairA
  rw [pairA] at pairB
  exact (Prod.mk.inj (Option.some.inj pairB)).2

/-- Membership in the window list of a prepared write list. -/
theorem mem_lm1WindowsOfWrites (writes : List PreparedParsedMaskedWrite) :
    ∀ entry ∈ lm1WindowsOfWrites writes,
      ∃ write ∈ writes, ∃ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
        write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ ∧
          entry = (address, count PEMemory.Bank.lm1 width) := by
  induction writes with
  | nil => intro entry member; simp [lm1WindowsOfWrites] at member
  | cons write rest ih =>
      intro entry member
      cases hdest : write.destination with
      | none =>
          simp only [lm1WindowsOfWrites, hdest, List.nil_append] at member
          obtain ⟨other, otherMem, width, address, otherDest, otherEq⟩ := ih entry member
          exact ⟨other, List.mem_cons_of_mem _ otherMem, width, address, otherDest, otherEq⟩
      | some access =>
          cases access with
          | mk bank width address =>
              cases bank with
              | lm1 =>
                  simp only [lm1WindowsOfWrites, hdest, List.cons_append, List.mem_cons,
                    List.mem_singleton] at member
                  rcases member with here | later
                  · subst here
                    exact ⟨write, by simp, width, address, by simp [hdest], rfl⟩
                  · obtain ⟨other, otherMem, otherWidth, otherAddress, otherDest, otherEq⟩ :=
                      ih entry later
                    exact ⟨other, List.mem_cons_of_mem _ otherMem, otherWidth, otherAddress,
                      otherDest, otherEq⟩
              | lm0 =>
                  simp only [lm1WindowsOfWrites, hdest, List.nil_append] at member
                  obtain ⟨other, otherMem, otherWidth, otherAddress, otherDest, otherEq⟩ :=
                    ih entry member
                  exact ⟨other, List.mem_cons_of_mem _ otherMem, otherWidth, otherAddress,
                    otherDest, otherEq⟩
              | grf0 =>
                  simp only [lm1WindowsOfWrites, hdest, List.nil_append] at member
                  obtain ⟨other, otherMem, otherWidth, otherAddress, otherDest, otherEq⟩ :=
                    ih entry member
                  exact ⟨other, List.mem_cons_of_mem _ otherMem, otherWidth, otherAddress,
                    otherDest, otherEq⟩
              | grf1 =>
                  simp only [lm1WindowsOfWrites, hdest, List.nil_append] at member
                  obtain ⟨other, otherMem, otherWidth, otherAddress, otherDest, otherEq⟩ :=
                    ih entry member
                  exact ⟨other, List.mem_cons_of_mem _ otherMem, otherWidth, otherAddress,
                    otherDest, otherEq⟩
              | t =>
                  simp only [lm1WindowsOfWrites, hdest, List.nil_append] at member
                  obtain ⟨other, otherMem, otherWidth, otherAddress, otherDest, otherEq⟩ :=
                    ih entry member
                  exact ⟨other, List.mem_cons_of_mem _ otherMem, otherWidth, otherAddress,
                    otherDest, otherEq⟩

/-- A write's window belongs to the window list of the containing write list. -/
theorem mem_lm1WindowsOfWrites_of_write (writes : List PreparedParsedMaskedWrite) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
      (address, count PEMemory.Bank.lm1 width) ∈ lm1WindowsOfWrites writes := by
  induction writes with
  | nil => intro write member; simp at member
  | cons head rest ih =>
      intro write member width address destinationEq
      rcases List.mem_cons.mp member with same | later
      · subst same
        simp [lm1WindowsOfWrites, destinationEq]
      · have inRest := ih write later width address destinationEq
        cases hdest : head.destination with
        | none =>
            simp only [lm1WindowsOfWrites, hdest, List.nil_append]
            exact inRest
        | some access =>
            cases access with
            | mk bank headWidth headAddress =>
                cases bank with
                | lm1 =>
                    simp only [lm1WindowsOfWrites, hdest, List.cons_append]
                    exact List.mem_cons_of_mem _ inRest
                | lm0 =>
                    simp only [lm1WindowsOfWrites, hdest, List.nil_append]
                    exact inRest
                | grf0 =>
                    simp only [lm1WindowsOfWrites, hdest, List.nil_append]
                    exact inRest
                | grf1 =>
                    simp only [lm1WindowsOfWrites, hdest, List.nil_append]
                    exact inRest
                | t =>
                    simp only [lm1WindowsOfWrites, hdest, List.nil_append]
                    exact inRest

/-- **The four chunks give the write-list shape.** -/
theorem lm1WritesShape_of_chunks (expression : ParsedExpr)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (w0 w1 w2 w3 : List PreparedParsedMaskedWrite)
    (f0 : Lm1ChunkFacts expression 0 w0) (f1 : Lm1ChunkFacts expression 1 w1)
    (f2 : Lm1ChunkFacts expression 2 w2) (f3 : Lm1ChunkFacts expression 3 w3) :
    Lm1WritesDoubleCopy (w0 ++ w1 ++ w2 ++ w3) ∨
      Lm1WritesNarrow (w0 ++ w1 ++ w2 ++ w3) := by
  set writes : List PreparedParsedMaskedWrite := w0 ++ w1 ++ w2 ++ w3 with writesEq
  have memSplit : ∀ {write : PreparedParsedMaskedWrite}, write ∈ writes →
      write ∈ w0 ∨ write ∈ w1 ∨ write ∈ w2 ∨ write ∈ w3 := by
    intro write member
    simp only [writes, List.mem_append] at member
    tauto
  have globalProv : ∀ write ∈ writes, ∀ access : DirectMemoryAccess,
      write.destination = some access → access.bank = PEMemory.Bank.lm1 →
      ∃ d ∈ expression.destinations, ∃ cycle : Fin 4,
        ParsedOperand.toDirectMemoryDestination? d welcomeZeroControl.context.pe cycle
          welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
          welcomeZeroControl.context.tWord = some access := by
    intro write member access destinationEq bank
    rcases memSplit member with h0 | h1 | h2 | h3
    · obtain ⟨d, resolves, dMember⟩ := f0.1 write h0 access destinationEq bank
      exact ⟨d, dMember, 0, resolves⟩
    · obtain ⟨d, resolves, dMember⟩ := f1.1 write h1 access destinationEq bank
      exact ⟨d, dMember, 1, resolves⟩
    · obtain ⟨d, resolves, dMember⟩ := f2.1 write h2 access destinationEq bank
      exact ⟨d, dMember, 2, resolves⟩
    · obtain ⟨d, resolves, dMember⟩ := f3.1 write h3 access destinationEq bank
      exact ⟨d, dMember, 3, resolves⟩
  have doubleCopyOf : ∀ write ∈ writes, ∀ address : Fin PEMemory.Bank.lm1.capacity,
      write.destination = some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, address⟩ →
      ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
    intro write member address destinationEq bound
    rcases memSplit member with h0 | h1 | h2 | h3
    · exact f0.2.1 write h0 address destinationEq bound
    · exact f1.2.1 write h1 address destinationEq bound
    · exact f2.2.1 write h2 address destinationEq bound
    · exact f3.2.1 write h3 address destinationEq bound
  have countBound : (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
    have h0 := f0.2.2
    have h1 := f1.2.2
    have h2 := f2.2.2
    have h3 := f3.2.2
    simp only [writes, List.filter_append, List.length_append] at *
    omega
  by_cases hasDouble : ∃ (write : PreparedParsedMaskedWrite) (address : Fin PEMemory.Bank.lm1.capacity),
      write ∈ writes ∧ write.destination = some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, address⟩
  · left
    intro write member width address data selection destinationEq dataEq selectionEq
    obtain ⟨witness, witnessAddress, witnessMem, witnessDestination⟩ := hasDouble
    obtain ⟨witnessD, witnessDMem, witnessCycle, witnessResolves⟩ :=
      globalProv witness witnessMem ⟨PEMemory.Bank.lm1, PEMemory.Width.double, witnessAddress⟩
        witnessDestination rfl
    obtain ⟨d, dMember, cycle, resolves⟩ := globalProv write member
      ⟨PEMemory.Bank.lm1, width, address⟩ destinationEq rfl
    have witnessDR : DestResolves expression witnessCycle
        ⟨PEMemory.Bank.lm1, PEMemory.Width.double, witnessAddress⟩ :=
      ⟨witnessD, witnessResolves, witnessDMem⟩
    have writeDR : DestResolves expression cycle ⟨PEMemory.Bank.lm1, width, address⟩ :=
      ⟨d, resolves, dMember⟩
    have widthEq : width = PEMemory.Width.double :=
      destResolves_width_eq expression cycle witnessCycle ⟨PEMemory.Bank.lm1, width, address⟩
        ⟨PEMemory.Bank.lm1, PEMemory.Width.double, witnessAddress⟩ nodup writeDR witnessDR rfl rfl
    have aligned := parsedOperand_toDirectMemoryAccessMode_aligned d true
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
      ⟨PEMemory.Bank.lm1, width, address⟩ resolves
    refine ⟨widthEq, ?_, ?_⟩
    · subst widthEq
      exact aligned
    · intro bound
      subst widthEq
      rw [← dataEq]
      exact doubleCopyOf write member address destinationEq bound
  · right
    refine ⟨lm1WindowsOfWrites writes, ?_, ?_, ?_⟩
    · intro write member width address destinationEq
      exact mem_lm1WindowsOfWrites_of_write writes write member width address destinationEq
    · rw [lm1Windows_length_eq_count]
      exact countBound
    · intro window windowMem
      obtain ⟨write, member, width, address, destinationEq, windowEq⟩ :=
        mem_lm1WindowsOfWrites writes window windowMem
      rw [windowEq]
      show count PEMemory.Bank.lm1 width ≤ 2
      have notDouble : width ≠ PEMemory.Width.double := by
        intro widthDouble
        apply hasDouble
        exact ⟨write, address, member, by rw [destinationEq, widthDouble]⟩
      cases width with
      | word => decide
      | long => decide
      | double => exact absurd rfl notDouble

/-! ## 11. The remaining obligation -/

/-- **`WelcomePEPlainStepShapeExceptImmediate` is discharged.** -/
theorem welcomePEPlainStepShapeExceptImmediate : WelcomePEPlainStepShapeExceptImmediate := by
  intro expressions unrefuted plain notImmediate next step
  obtain ⟨e, same, ePlain⟩ := plain_single_expression expressions unrefuted plain
  subst same
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    welcomeSealed_pe_prepared [e] (welcomeInitialState welcomeZeroWords) unrefuted.1.1
      (by simpa using plain) step
  have prep' : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots
      e.toParsed welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
      (match e.toParsed.op with
        | ParsedOp.noforward => true
        | _ => false) false = .ok (writes, slots) := by
    have h := welcomeIntegerPrep_inv (welcomeInitialState welcomeZeroWords) e.toParsed ePlain
      writes slots bars prep
    have filesEq : (welcomeInitialState welcomeZeroWords).peRegisters welcomePE =
        welcomeZeroFiles := rfl
    have slotsEq : stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE =
        welcomeZeroSlots := rfl
    have controlEq : parsedPEHazardControl (welcomeInitialState welcomeZeroWords) welcomePE =
        welcomeZeroControl := rfl
    rw [filesEq, slotsEq, controlEq] at h
    simp only [List.any_cons, List.any_nil, Bool.or_false] at h
    exact h
  obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
    prepareParsedIntegerALUExprCycles_four welcomeZeroFiles welcomeZeroSlots e.toParsed
      welcomeZeroControl (parsedExprHasSingleLineWriteMask e.toParsed)
      (match e.toParsed.op with
        | ParsedOp.noforward => true
        | _ => false) false writes slots prep'
  have legal := welcomePEUnrefuted_legal [e] unrefuted
  have memProject : e.toParsed.toIssueExpr 0 ∈ projectLine [e.toParsed] := by
    simp [projectLine, projectFrom]
  have nodup : (e.toParsed.toIssueExpr 0).writeBanks.Nodup :=
    welcomeLm1WritesNodup [e] legal _ memProject
  have notDouble : ∀ payload sparse, e.toParsed.op = .immediate payload sparse →
      ∀ d ∈ e.toParsed.destinations, ParsedOperand.directDestinationBankWidth? d ≠
        some (PEMemory.Bank.lm1, PEMemory.Width.double) := by
    intro payload sparse isImmediate d member pair
    apply notImmediate
    exact ⟨e.toParsed, by simp, ⟨payload, sparse, isImmediate⟩, d, member, pair⟩
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
  refine ⟨writes, committed, ?_⟩
  rw [writesEq]
  exact shape

/-- The discharged obligation has exactly the type of the `Prop` stated in
`WelcomePlainShape.lean`, and together with the already-proved immediate case it
yields the plain-class shape obligation. -/
theorem welcomePEPlainShapeObligation :
    WelcomePEPlainShapeObligation :=
  welcomePEPlainShapeObligation_of_two welcomePEPlainStepShapeExceptImmediate
    welcomePEPlainImmediateDoubleObligation

/-- The discharged obligation has exactly the type of the `Prop` stated in
`WelcomePlainShape.lean` §10. -/
example : WelcomePEPlainStepShapeExceptImmediate := welcomePEPlainStepShapeExceptImmediate


end ProofsLean.MNCore
