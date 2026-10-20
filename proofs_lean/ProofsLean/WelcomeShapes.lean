import ProofsLean.WelcomeProvenance

/-! # Write shapes for the Welcome lower bound

`WelcomeProvenance.lean` reduces `LowerBound welcomeSealedMachine welcomeSpec 2`
to ten `Prop` obligations.  This module proves the pieces of those obligations
that follow from the executor *without* assuming the residual class
`WelcomePEResidual` to be empty or inhabited.

## Proved here

* `parsedOperand_toDirectMemoryAccessMode_aligned` — every access produced by
  `ParsedOperand.toDirectMemoryAccessMode?` (hence by
  `ParsedOperand.toDirectMemoryDestination?`) has an address aligned to its own
  width in words.  This is the "4-aligned" half of the `.double` block shape,
  for every destination of every lowering, with no hypothesis on the row.
* `WelcomePEConstantOp` / `WelcomePEConstantRow` / `WelcomePEConstantLine` —
  the `.zero`/`.immediate` row class of
  `WelcomePEConstantInputIndependentObligation`.
* `evaluateParsedIntegerAlu_constant` — a constant row's whole `StepResult` is
  independent of both operand buses and of the `reduced` flag.
* `prepareParsedMaskedWrite_eq_of_constant_memory` — a constant row whose
  sources are direct memory reads prepares the *same* masked write on any
  register file (the reads are total and their values are ignored).
* `toDirectMaskedIntegerAccessesInLine?_op` — the accesses of the direct
  integer lowering carry the row's own operation.
* `toDirectMaskedConstantDestination?_eq_bind`,
  `toDirectMaskedConstantDestination?_default_shape`,
  `toDirectMaskedConstantDestination?_shape` — a `.memory` constant destination
  carries the row's constant operation and exactly two direct memory sources.

## Not proved here

The ten `Prop` obligations of `WelcomeProvenance.lean` are **not** discharged:

* the `.double` shape obligations all quantify over `WelcomePEResidual`, so they
  are vacuous unless that class is inhabited (which is the theorem being
  proved); and the third-data-word condition is not a consequence of the
  residual hypothesis — a `.fixed .msb1` first operand has a nonzero third data
  word while its low half still reaches the written words;
* `WelcomePENarrowCoverageObligation` additionally quantifies over *arbitrary*
  write lists satisfying only the commit equation, not over the executor's own
  prepared list;
* `WelcomePEConstantInputIndependentObligation` is true but needs the
  destination-list induction and the 4096-PE bisimulation that are listed in
  the module report; only its per-row ingredients are proved above.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-- **Alignment of direct-memory destinations.** Every access returned by the
direct-memory address resolver is aligned to its own width in words: the
resolved address is `(raw / words * words) % capacity`, and the width divides
the capacity of every PE register bank. -/
theorem parsedOperand_toDirectMemoryAccessMode_aligned (operand : ParsedOperand)
    (allowDestinationMask : Bool) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (access : DirectMemoryAccess)
    (lowered : ParsedOperand.toDirectMemoryAccessMode? operand allowDestinationMask pe cycle
      bar0 bar1 tWord = some access) :
    access.address.val % access.width.words = 0 := by
  cases operand with
  | mem memoryAccess negated extended rounded mask =>
      simp only [ParsedOperand.toDirectMemoryAccessMode?] at lowered
      split at lowered
      · simp at lowered
      · cases hb : issueBankToRegisterBank memoryAccess.bank with
        | none => simp [hb] at lowered
        | some bank =>
            cases hw : parsedWidth? memoryAccess.region.width with
            | none => simp [hb, hw] at lowered
            | some width =>
                simp only [hb, hw] at lowered
                split at lowered
                · simp at lowered
                · simp only [Option.some.injEq] at lowered
                  subst lowered
                  show (if (bank == PEMemory.Bank.t) = true then cycle.val * 4 else
                    ((((if (bank == PEMemory.Bank.lm0) = true then bar0.toNat
                         else if (bank == PEMemory.Bank.lm1) = true then bar1.toNat else 0) +
                        (if memoryAccess.region.tIndirect = true then tWord.toNat else 0)) +
                      parsedRegionAddressAt memoryAccess.region cycle +
                      (match memoryAccess.region.madpe with
                       | some threshold => if (pe.val ≤ threshold) then width.words else 0
                       | none => 0)) / width.words * width.words % bank.capacity)) %
                    width.words = 0
                  by_cases isT : bank = PEMemory.Bank.t
                  · rw [if_pos (by simp [isT])]
                    cases width <;> simp [Width.words] <;> omega
                  · rw [if_neg (by simp [isT])]
                    have dvd : width.words ∣ bank.capacity := by
                      cases width <;> cases bank <;> decide
                    rw [Nat.mod_mod_of_dvd _ dvd]
                    exact Nat.mod_eq_zero_of_dvd ⟨_, by rw [Nat.mul_comm]⟩
  | bar _ _ mask => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | forward _ _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | fixed kind => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | omr _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | matrix _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | nowrite => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l1bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l2bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | dar _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered

/-- An operation whose execution request is constant: `.zero` or `.immediate`.
Such an operation's ALU output does not depend on either operand bus. -/
def WelcomePEConstantOp (op : ParsedOp) : Prop :=
  op = .zero ∨ ∃ value sparse, op = .immediate value sparse

/-- A parsed row whose operation is constant. -/
def WelcomePEConstantRow (expression : ParsedExpr) : Prop :=
  WelcomePEConstantOp expression.op

/-- A normalized line all of whose rows are constant. -/
def WelcomePEConstantLine (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed, WelcomePEConstantRow expression

/-- **Constant rows ignore their operand buses.** The whole `StepResult` of the
parsed integer ALU evaluation of a `.zero`/`.immediate` row is independent of
both buses and of the `reduced` flag. -/
theorem evaluateParsedIntegerAlu_constant (op : ParsedOp) (x y x' y' : IntegerALU.Bus)
    (reduced reduced' : Bool) (constant : WelcomePEConstantOp op) :
    evaluateParsedIntegerAlu op x y reduced = evaluateParsedIntegerAlu op x' y' reduced' := by
  rcases constant with rfl | ⟨v, s, rfl⟩
  · simp [evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest]
  · simp [evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest]

/-- **Constant writes do not read the register file.** A prepared masked write
whose operation is `.zero` or `.immediate` and whose sources are direct memory
accesses is the same write for *any* register file: the reads are total and the
evaluation ignores them. -/
theorem prepareParsedMaskedWrite_eq_of_constant_memory
    (filesA filesB : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses)
    (reduced : Bool) (constant : WelcomePEConstantOp accesses.op)
    (sourceXAccess sourceYAccess : DirectMemoryAccess) (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY) :
    prepareParsedMaskedWrite filesA accesses reduced =
      prepareParsedMaskedWrite filesB accesses reduced := by
  unfold prepareParsedMaskedWrite
  rw [sourceX, sourceY]
  simp only [ParsedIntegerInput.read]
  rw [evaluateParsedIntegerAlu_constant accesses.op
    (ParsedIntegerInput.applyRounding roundedX (pack (readDirectAccess filesA sourceXAccess)))
    (ParsedIntegerInput.applyRounding roundedY (pack (readDirectAccess filesA sourceYAccess)))
    (ParsedIntegerInput.applyRounding roundedX (pack (readDirectAccess filesB sourceXAccess)))
    (ParsedIntegerInput.applyRounding roundedY (pack (readDirectAccess filesB sourceYAccess)))
    reduced reduced constant]


/-! ## 2. The per-cycle destination shape of the direct lowering

The `.double` shape needs two facts about the direct lowering used by
`prepareParsedIntegerALUExprCycle`: the destination of the single prepared write
is the resolved operand access (so its address is width-aligned by
`parsedOperand_toDirectMemoryAccessMode_aligned`), and its operation is the
row's operation.  Both are read off the definition of
`ParsedExpr.toDirectMaskedIntegerAccessesInLine?`. -/

theorem toDirectMaskedIntegerAccessesInLine?_op
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
      | some parsedPrecision =>
          simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
          repeat' split at lowered
          all_goals (try simp_all)
          all_goals rw [← lowered]
  | zero =>
      simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
      repeat' split at lowered
      all_goals (try simp_all)
      all_goals rw [← lowered]
  | immediate value sparse =>
      simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
      repeat' split at lowered
      all_goals (try simp_all)
      all_goals rw [← lowered]
  | mau precision matrix kind half round => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | matrixWrite precision => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | matrixRead precision => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | wait tag => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | noforward => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | l1bm operation => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  | l2bm operation => simp [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered

/-- The default case of `toDirectMaskedConstantDestination?` as an explicit
`Option.bind` over the one-destination integer lowering. -/
theorem toDirectMaskedConstantDestination?_eq_bind
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand)
    (notNowrite : destination ≠ .nowrite)
    (notOmr : ∀ entry mask, destination ≠ .omr entry mask) :
    ParsedExpr.toDirectMaskedConstantDestination? expression registers directive hasSingleLineMask
      group l2b l1b mab pe cycle bar0 bar1 tWord destination =
      (ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { op := expression.op, sources := expression.sources, destinations := [destination],
          flush := expression.flush, text := expression.text }
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord).bind
        (fun lowered => some (ParsedConstantDestination.memory lowered)) := by
  rw [ParsedExpr.toDirectMaskedConstantDestination?.eq_3 expression registers directive
    hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination notNowrite notOmr]
  rfl



/-- The shape of one lowered constant destination in the default case: a
`.memory` target carries the row's constant operation and two direct memory
sources. -/
theorem toDirectMaskedConstantDestination?_default_shape
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (constant : WelcomePEConstantRow expression)
    (destination : ParsedOperand)
    (notNowrite : destination ≠ .nowrite)
    (notOmr : ∀ entry mask, destination ≠ .omr entry mask)
    (target : ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination = some target)
    (accesses : ParsedMaskedIntegerAccesses) (isMemory : target = .memory accesses) :
    WelcomePEConstantOp accesses.op ∧
      ∃ ax ay rx ry, accesses.sourceX = .memory ax rx ∧ accesses.sourceY = .memory ay ry := by
  rw [toDirectMaskedConstantDestination?_eq_bind expression registers directive hasSingleLineMask
    group l2b l1b mab pe cycle bar0 bar1 tWord destination notNowrite notOmr] at lowered
  cases hLowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { op := expression.op, sources := expression.sources, destinations := [destination],
        flush := expression.flush, text := expression.text }
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
  · rw [hLowered] at lowered
    simp only [Option.bind] at lowered
    simp at lowered
  · rename_i val
    rw [hLowered] at lowered
    simp only [Option.bind, Option.some.injEq] at lowered
    have accessEq : accesses = val := by
      rw [← lowered] at isMemory
      simpa using isMemory.symm
    subst accesses
    have opEq := toDirectMaskedIntegerAccessesInLine?_op
      { op := expression.op, sources := expression.sources, destinations := [destination],
        flush := expression.flush, text := expression.text }
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord val hLowered
    have sources := ParsedExpr.toDirectMaskedIntegerAccessesInLine_constant_sources_are_memory
      { op := expression.op, sources := expression.sources, destinations := [destination],
        flush := expression.flush, text := expression.text }
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
      constant val hLowered
    refine ⟨?_, val.destination, val.destination, false, false, sources.1, sources.2⟩
    rw [opEq]
    exact constant


/-- The shape of one lowered constant destination. -/
theorem toDirectMaskedConstantDestination?_shape
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (constant : WelcomePEConstantRow expression)
    (destination : ParsedOperand) (target : ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination = some target)
    (accesses : ParsedMaskedIntegerAccesses) (isMemory : target = .memory accesses) :
    WelcomePEConstantOp accesses.op ∧
      ∃ ax ay rx ry, accesses.sourceX = .memory ax rx ∧ accesses.sourceY = .memory ay ry := by
  cases destination with
  | nowrite =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      simp only [Option.some.injEq] at lowered
      rw [← lowered] at isMemory
      simp at isMemory
  | omr entry mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases hEntry : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask)
      · rw [hEntry] at lowered
        simp only [Bind.bind, Option.bind] at lowered
        simp at lowered
      · rename_i maskEntry
        cases hSel : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
            registers cycle directive hasSingleLineMask
        · rw [hEntry, hSel] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
        · rw [hEntry, hSel] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          rw [← lowered] at isMemory
          simp at isMemory
  | mem access negated extended rounded mask =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | bar lm1 width mask =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | forward kind negated extended rounded =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | fixed kind =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | matrix y width row =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | l1bm width address =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | l2bm address l2bValue =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory
  | dar address =>
      exact toDirectMaskedConstantDestination?_default_shape expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord constant _ (by simp)
        (by simp) target lowered accesses isMemory


end ProofsLean.MNCore
