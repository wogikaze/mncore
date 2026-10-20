import ProofsLean.WelcomeStageCommit

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

theorem isLm1Write_eq_false_of_destination_ne (write : PreparedParsedMaskedWrite)
    (h : ∀ access : DirectMemoryAccess, write.destination = some access →
      access.bank ≠ PEMemory.Bank.lm1) :
    PreparedParsedMaskedWrite.isLm1Write write = false := by
  rcases write with ⟨destination, update, data, selection⟩
  cases destination with
  | none => rfl
  | some access =>
      have := h access rfl
      simp [PreparedParsedMaskedWrite.isLm1Write, beq_eq_false_iff_ne, this]

theorem isLm1Write_eq_false_of_destination_none (write : PreparedParsedMaskedWrite)
    (h : write.destination = none) :
    PreparedParsedMaskedWrite.isLm1Write write = false := by
  rcases write with ⟨destination, update, data, selection⟩
  cases destination with
  | none => rfl
  | some access => simp at h

theorem destination_bank_ne_of_static
    (destination : ParsedOperand) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (access : DirectMemoryAccess)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (resolved : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1
      tWord = some access) :
    access.bank ≠ PEMemory.Bank.lm1 := by
  have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination pe cycle
    bar0 bar1 tWord
  rw [resolved] at static
  simp only [Option.map_some] at static
  exact noLm1 access.bank access.width static.symm

theorem directAccesses_destination_bank_ne
    (expression : ParsedExpr) (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    accesses.destination.bank ≠ PEMemory.Bank.lm1 := by
  obtain ⟨destination, member, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses lowered
  exact destination_bank_ne_of_static destination control.context.pe cycle control.context.bar0
    control.context.bar1 control.context.tWord accesses.destination
    (noLm1 destination member) resolved

theorem toDirectMaskedConstantDestination?_memory_resolution
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
      some accesses.destination := by
  cases destination with
  | nowrite => simp [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
  | omr entry mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some maskEntry =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask) registers
              cycle directive hasSingleLineMask with
          | none =>
              rw [h, h2] at lowered
              simp only [Bind.bind, Option.bind] at lowered
              simp at lowered
          | some selection =>
              rw [h, h2] at lowered
              simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
              simp at lowered
  | mem access negated extended rounded mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.mem access negated extended rounded
            mask] } registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1
          tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.mem access negated extended
                rounded mask] } registers directive hasSingleLineMask group l2b l1b mab pe cycle
              bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | bar lm1 width mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.bar lm1 width mask] } registers
          directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.bar lm1 width mask] } registers
              directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | forward kind negated extended rounded =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.forward kind negated extended rounded] }
          registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.forward kind negated extended
                rounded] } registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0
              bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | fixed kind =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.fixed kind] } registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.fixed kind] } registers directive
              hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | matrix matrixGroup width row =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.matrix matrixGroup width row] } registers
          directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.matrix matrixGroup width row] } registers
              directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | l1bm width address =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.l1bm width address] } registers
          directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.l1bm width address] } registers
              directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | l2bm address l2b' =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.l2bm address l2b'] } registers
          directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.l2bm address l2b'] } registers
              directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq
  | dar address =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [ParsedOperand.dar address] } registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind] at lowered
          simp at lowered
      | some found =>
          rw [h] at lowered
          simp only [Bind.bind, Option.bind, Option.some.injEq] at lowered
          injection lowered with foundEq
          subst foundEq
          obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
              { expression with destinations := [ParsedOperand.dar address] } registers directive
              hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord found h
          simp only [List.mem_singleton] at resolvedMem
          subst resolvedMem
          exact resolvedEq

theorem prepareParsedMaskedWriteWithForwarding_lm1_free
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write)
    (bank : accesses.destination.bank ≠ PEMemory.Bank.lm1) :
    PreparedParsedMaskedWrite.isLm1Write write = false := by
  apply isLm1Write_eq_false_of_destination_ne
  intro access h
  rw [prepareParsedMaskedWriteWithForwarding_destination files slots cycle accesses reduced
    write prepared] at h
  obtain rfl := Option.some.inj h
  exact bank

theorem prepareParsedMaskedWrite_lm1_free
    (files : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWrite files accesses reduced = .ok write)
    (bank : accesses.destination.bank ≠ PEMemory.Bank.lm1) :
    PreparedParsedMaskedWrite.isLm1Write write = false := by
  apply isLm1Write_eq_false_of_destination_ne
  intro access h
  rw [prepareParsedMaskedWrite_destination files accesses reduced write prepared] at h
  obtain rfl := Option.some.inj h
  exact bank

theorem prepareParsedConstantTarget_lm1_free
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (target : ParsedConstantDestination) (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedConstantTarget files cycle target = .ok write)
    (free : ∀ accesses, target = .memory accesses →
      accesses.destination.bank ≠ PEMemory.Bank.lm1) :
    PreparedParsedMaskedWrite.isLm1Write write = false := by
  cases target with
  | memory accesses =>
      exact prepareParsedMaskedWrite_lm1_free files accesses false write prepared
        (free accesses rfl)
  | maskRegister entry =>
      exact isLm1Write_eq_false_of_destination_none write (by
        simp [prepareParsedConstantTarget] at prepared
        subst prepared
        rfl)
  | noWrite =>
      exact isLm1Write_eq_false_of_destination_none write (by
        simp [prepareParsedConstantTarget] at prepared
        subst prepared
        rfl)

theorem prepareParsedMaskedConstantWrites_lm1_free
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination)
    (writes : List PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets = .ok writes)
    (free : ∀ target ∈ targets, ∀ accesses, target = .memory accesses →
      accesses.destination.bank ≠ PEMemory.Bank.lm1) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  induction targets generalizing writes with
  | nil =>
      simp only [prepareParsedMaskedConstantWrites, StepResult.ok.injEq] at prepared
      subst prepared
      intro write member
      simp at member
  | cons target rest ih =>
      cases head : prepareParsedConstantTarget files cycle target with
      | failure => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | unknown => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | ok headWrite =>
          cases tail : prepareParsedMaskedConstantWrites files cycle rest with
          | failure => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | unknown => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | ok tailWrites =>
              simp only [prepareParsedMaskedConstantWrites, head, tail, StepResult.ok.injEq]
                at prepared
              rw [← prepared]
              intro write member
              rcases List.mem_cons.mp member with same | later
              · rw [same]
                exact prepareParsedConstantTarget_lm1_free files cycle target headWrite head
                  (fun accesses isMemory => free target (by simp) accesses isMemory)
              · exact ih tailWrites tail
                  (fun other otherMem accesses isMemory =>
                    free other (List.mem_cons_of_mem _ otherMem) accesses isMemory) write later

theorem parsedIntegerMaskMemoryThenInputExprAccessesInLine?_memory_resolution
    (expression : ParsedExpr) (files : IntegerRegisterFiles) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression files.maskRegisters
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∃ destination : ParsedOperand,
      ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
        some accesses.memory ∧ destination ∈ expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by assumption, by simp⟩)

theorem parsedIntegerMaskInputThenMemoryExprAccessesInLine?_memory_resolution
    (expression : ParsedExpr) (files : IntegerRegisterFiles) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression files.maskRegisters
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ParsedOperand.toDirectMemoryDestination? accesses.memoryOperand pe cycle bar0 bar1 tWord =
        some accesses.memory ∧
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

theorem mapM_targets_notLm1 (f : ParsedOperand → Option ParsedMatrixReadTarget) :
    ∀ (destinations : List ParsedOperand) (targets : List ParsedMatrixReadTarget),
      destinations.mapM f = some targets →
      (∀ d ∈ destinations, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
        f d = some (.memory access selection) → access.bank ≠ PEMemory.Bank.lm1) →
      ∀ target ∈ targets, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
        target = .memory access selection → access.bank ≠ PEMemory.Bank.lm1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro targets mapped facts target member
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp at member
  | cons d rest ih =>
      intro targets mapped facts target member
      obtain ⟨b, bs, head, tail, rfl⟩ := mapM_cons_inv f d rest targets mapped
      rcases List.mem_cons.mp member with same | later
      · subst same
        intro access selection targetEq
        exact facts d (by simp) access selection (by rw [head, targetEq])
      · exact ih bs tail (fun d' mem' => facts d' (List.mem_cons_of_mem _ mem'))
          target later

theorem parsedMatrixReadTargetAt?_memory_bank_ne
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (context : ParsedIntegerContext) (target : ParsedOperand)
    (access : DirectMemoryAccess) (selection : PEWordSelection)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? target = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (lowered : parsedMatrixReadTargetAt? registers directive hasSingleLineMask context target =
      some (.memory access selection)) :
    access.bank ≠ PEMemory.Bank.lm1 :=
  destination_bank_ne_of_static target context.pe context.cycle context.bar0 context.bar1
    context.tWord access noLm1 (parsedMatrixReadTargetAt?_memory registers directive
      hasSingleLineMask context target access selection lowered)

theorem prepareParsedMatrixReadTargets_lm1_free
    (targets : List ParsedMatrixReadTarget) (output : IntegerALU.Bus)
    (free : ∀ target ∈ targets, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
      target = .memory access selection → access.bank ≠ PEMemory.Bank.lm1) :
    ∀ (writes : List PreparedParsedMaskedWrite) (barUpdates : List (Bool × BitVec 12)),
      prepareParsedMatrixReadTargets targets output = .ok (writes, barUpdates) →
      ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  induction targets with
  | nil =>
      intro writes bars prepared write member
      simp only [prepareParsedMatrixReadTargets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      simp at member
  | cons target rest ih =>
      intro writes bars prepared write member
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              rcases List.mem_cons.mp member with same | later
              · rw [same]
                exact isLm1Write_eq_false_of_destination_none _ rfl
              · exact ih (fun item itemMem => free item (List.mem_cons_of_mem _ itemMem))
                  restWrites restBars h write later
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              rcases List.mem_cons.mp member with same | later
              · rw [same]
                apply isLm1Write_eq_false_of_destination_ne
                intro access' haccess
                simp only [Option.some.injEq] at haccess
                subst haccess
                exact free (.memory access selection) (by simp) access selection rfl
              · exact ih (fun item itemMem => free item (List.mem_cons_of_mem _ itemMem))
                  restWrites restBars h write later
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              exact ih (fun item itemMem => free item (List.mem_cons_of_mem _ itemMem))
                restWrites restBars h write member

theorem prepareParsedMatrixReadTargets_lm1_free_of_expression
    (expression : ParsedExpr) (files : IntegerRegisterFiles) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext)
    (accesses : ParsedMatrixReadAccesses) (output : IntegerALU.Bus)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (targetsMapped : expression.destinations.mapM (fun target =>
      parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask context target) =
        some accesses.targets) :
    ∀ target ∈ accesses.targets, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
      target = .memory access selection → access.bank ≠ PEMemory.Bank.lm1 :=
  mapM_targets_notLm1 _ expression.destinations accesses.targets targetsMapped
    (fun destination member access selection lowered =>
      parsedMatrixReadTargetAt?_memory_bank_ne files.maskRegisters directive hasSingleLineMask
        context destination access selection (noLm1 destination member) lowered)

theorem prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_lm1_free
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (memoryBank : accesses.memory.bank ≠ PEMemory.Bank.lm1)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files slots cycle
      accesses flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∀ write ∈ memoryWrites ++ [omrWrite],
      PreparedParsedMaskedWrite.isLm1Write write = false := by
  obtain ⟨bus, flags, memoryShape, omrShape⟩ :=
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape files slots cycle
      accesses flushSelection reduced memoryWrites omrWrite prepared
  intro item member
  rcases List.mem_append.mp member with earlier | later
  · rw [memoryShape] at earlier
    rw [List.mem_singleton] at earlier
    rw [earlier]
    exact isLm1Write_eq_false_of_destination_ne _ (by
      intro access haccess
      simp only [Option.some.injEq] at haccess
      subst haccess
      exact memoryBank)
  · rw [List.mem_singleton] at later
    rw [later, omrShape]
    exact isLm1Write_eq_false_of_destination_none _ rfl

theorem prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_lm1_free
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (memoryBank : accesses.memory.bank ≠ PEMemory.Bank.lm1)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files slots cycle
      accesses directive hasSingleLineMask flushSelection reduced
        = .ok (memoryWrites, omrWrite)) :
    ∀ write ∈ memoryWrites ++ [omrWrite],
      PreparedParsedMaskedWrite.isLm1Write write = false := by
  obtain ⟨bus, flags, memorySelection, memoryShape, omrShape⟩ :=
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape files slots cycle
      accesses directive hasSingleLineMask flushSelection reduced memoryWrites omrWrite prepared
  intro item member
  rcases List.mem_append.mp member with earlier | later
  · rw [memoryShape] at earlier
    rcases List.mem_cons.mp earlier with first | second
    · rw [first]
      exact isLm1Write_eq_false_of_destination_none _ rfl
    · rw [List.mem_singleton] at second
      rw [second]
      exact isLm1Write_eq_false_of_destination_ne _ (by
        intro access haccess
        simp only [Option.some.injEq] at haccess
        subst haccess
        exact memoryBank)
  · rw [List.mem_singleton] at later
    rw [later, omrShape]
    exact isLm1Write_eq_false_of_destination_none _ rfl

theorem prepareParsedIntegerALUExprCycle_lm1_free
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle = .ok (writes, slots))
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none =>
          simp only [prepareParsedIntegerALUExprCycle,
            ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
            ParsedExpr.toDirectMaskedIntegerWritesInLine?,
            parsedIntegerMaskExprAccessesInLine?,
            parsedIntegerNoWriteExprAccessesInLine?,
            parsedIntegerBarExprAccessesInLine?,
            parsedIntegerMaskInputExprAccessesInLine?,
            parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
            parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at prep
          cases destinations with
          | nil => simp at prep
          | cons destination rest =>
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
          cases directCall : ParsedExpr.toDirectMaskedIntegerAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
          | some accesses =>
            simp only [prepareParsedIntegerALUExprCycle] at prep
            rw [directCall] at prep
            dsimp only at prep
            cases preparedCall : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced with
            | failure => rw [preparedCall] at prep; simp at prep
            | unknown => rw [preparedCall] at prep; simp at prep
            | ok write =>
              rw [preparedCall] at prep
              dsimp only at prep
              split at prep
              · simp at prep
              · simp at prep
              · rename_i slots' updated
                simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                obtain ⟨rfl, rfl⟩ := prep
                intro item member
                rw [List.mem_singleton] at member
                rw [member]
                exact prepareParsedMaskedWriteWithForwarding_lm1_free files oldSlots cycle
                  accesses reduced write preparedCall
                  (directAccesses_destination_bank_ne ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files control hasSingleLineMask
                    cycle accesses directCall noLm1)
          | none =>
            cases multipleCall : ParsedExpr.toDirectMaskedIntegerWritesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
            | some accessList =>
              cases accessList with
              | nil => simp [prepareParsedIntegerALUExprCycle, directCall, multipleCall] at prep
              | cons access rest =>
                simp only [prepareParsedIntegerALUExprCycle] at prep
                rw [directCall, multipleCall] at prep
                dsimp only at prep
                cases preparedCall : prepareParsedMaskedWriteWithForwarding files oldSlots cycle access reduced with
                | failure => rw [preparedCall] at prep; simp at prep
                | unknown => rw [preparedCall] at prep; simp at prep
                | ok write =>
                  rw [preparedCall] at prep
                  dsimp only at prep
                  split at prep
                  · simp at prep
                  · simp at prep
                  · rename_i slots' updated
                    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                    obtain ⟨rfl, rfl⟩ := prep
                    have accessBank : ∀ a ∈ access :: rest,
                      a.destination.bank ≠ PEMemory.Bank.lm1 := by
                      intro a member
                      obtain ⟨destination, destinationMem, resolved⟩ :=
                        toDirectMaskedIntegerWritesInLine?_mem_provenance ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
                          files.maskRegisters control.directive hasSingleLineMask
                          control.context.group control.context.l2b control.context.l1b
                          control.context.mab control.context.pe cycle control.context.bar0
                          control.context.bar1 control.context.tWord (access :: rest)
                          multipleCall a member
                      exact destination_bank_ne_of_static destination control.context.pe
                        cycle control.context.bar0 control.context.bar1 control.context.tWord
                        a.destination (noLm1 destination destinationMem) resolved
                    intro item member
                    rcases List.mem_cons.mp member with same | later
                    · rw [same]
                      exact prepareParsedMaskedWriteWithForwarding_lm1_free files oldSlots
                        cycle access reduced write preparedCall
                        (accessBank access (by simp))
                    · rcases List.mem_map.mp later with ⟨other, otherMem, otherEq⟩
                      rw [← otherEq]
                      exact isLm1Write_eq_false_of_destination_ne _ (by
                        intro access' haccess
                        simp only [Option.some.injEq] at haccess
                        subst haccess
                        exact accessBank other (List.mem_cons_of_mem _ otherMem))
            | none =>
              cases omrCall : parsedIntegerMaskExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
              | some omrAccesses =>
                cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
                | none =>
                  simp [prepareParsedIntegerALUExprCycle, directCall, multipleCall, omrCall,
                    flushCall] at prep
                | some flushSelection =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [directCall, multipleCall, omrCall, flushCall] at prep
                  dsimp only at prep
                  cases preparedCall : prepareParsedIntegerMaskALUWriteWithForwarding files oldSlots cycle omrAccesses flushSelection reduced with
                  | failure => rw [preparedCall] at prep; simp at prep
                  | unknown => rw [preparedCall] at prep; simp at prep
                  | ok write =>
                    rw [preparedCall] at prep
                    dsimp only at prep
                    split at prep
                    · simp at prep
                    · simp at prep
                    · rename_i slots' updated
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      obtain ⟨rfl, rfl⟩ := prep
                      intro item member
                      rw [List.mem_singleton] at member
                      rw [member]
                      exact isLm1Write_eq_false_of_destination_none _
                        (prepareParsedIntegerMaskALUWriteWithForwarding_destination_none files oldSlots cycle omrAccesses flushSelection reduced write preparedCall)

              | none =>
                cases noWriteCall : parsedIntegerNoWriteExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.context.pe cycle control.context.group control.context.l2b control.context.l1b control.context.mab control.context.bar0 control.context.bar1 control.context.tWord with
                | some noWriteAccesses =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [directCall, multipleCall, omrCall, noWriteCall] at prep
                  dsimp only at prep
                  cases preparedCall : prepareParsedIntegerNoWriteALUWithForwarding files oldSlots cycle noWriteAccesses reduced with
                  | failure => rw [preparedCall] at prep; simp at prep
                  | unknown => rw [preparedCall] at prep; simp at prep
                  | ok write =>
                    rw [preparedCall] at prep
                    dsimp only at prep
                    split at prep
                    · simp at prep
                    · simp at prep
                    · rename_i slots' updated
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      obtain ⟨rfl, rfl⟩ := prep
                      intro item member
                      rw [List.mem_singleton] at member
                      rw [member]
                      exact isLm1Write_eq_false_of_destination_none _
                        (prepareParsedIntegerNoWriteALUWithForwarding_destination_none files oldSlots cycle noWriteAccesses reduced write preparedCall)

                | none =>
                  cases barCall : parsedIntegerBarExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
                  | some barAccesses =>
                    simp only [prepareParsedIntegerALUExprCycle] at prep
                    rw [directCall, multipleCall, omrCall, noWriteCall, barCall] at prep
                    dsimp only at prep
                    cases preparedCall : prepareParsedIntegerBarALUWithForwarding files oldSlots cycle barAccesses reduced with
                    | failure => rw [preparedCall] at prep; simp at prep
                    | unknown => rw [preparedCall] at prep; simp at prep
                    | ok write =>
                      rw [preparedCall] at prep
                      dsimp only at prep
                      split at prep
                      · simp at prep
                      · simp at prep
                      · rename_i slots' updated
                        simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                        obtain ⟨rfl, rfl⟩ := prep
                        intro item member
                        rw [List.mem_singleton] at member
                        rw [member]
                        exact isLm1Write_eq_false_of_destination_none _
                          (prepareParsedIntegerBarALUWithForwarding_destination_none files oldSlots cycle barAccesses reduced write preparedCall)

                  | none =>
                    cases inputCall : parsedIntegerMaskInputExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
                    | some inputAccesses =>
                      cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
                      | none =>
                        simp [prepareParsedIntegerALUExprCycle, directCall, multipleCall, omrCall,
                          noWriteCall, barCall, inputCall, flushCall] at prep
                      | some flushSelection =>
                        simp only [prepareParsedIntegerALUExprCycle] at prep
                        rw [directCall, multipleCall, omrCall, noWriteCall, barCall,
                          inputCall, flushCall] at prep
                        dsimp only at prep
                        cases preparedCall : prepareParsedIntegerMaskInputALUWriteWithForwarding files oldSlots cycle inputAccesses flushSelection reduced with
                        | failure => rw [preparedCall] at prep; simp at prep
                        | unknown => rw [preparedCall] at prep; simp at prep
                        | ok write =>
                          rw [preparedCall] at prep
                          dsimp only at prep
                          split at prep
                          · simp at prep
                          · simp at prep
                          · rename_i slots' updated
                            simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                            obtain ⟨rfl, rfl⟩ := prep
                            intro item member
                            rw [List.mem_singleton] at member
                            rw [member]
                            exact isLm1Write_eq_false_of_destination_none _
                              (prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none files oldSlots cycle inputAccesses flushSelection reduced write preparedCall)

                    | none =>
                      cases mixedCall : parsedIntegerMaskMemoryThenInputExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
                      | some mixedAccesses =>
                        cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
                        | none =>
                          simp [prepareParsedIntegerALUExprCycle, directCall, multipleCall, omrCall,
                            noWriteCall, barCall, inputCall, mixedCall, flushCall] at prep
                        | some flushSelection =>
                          simp only [prepareParsedIntegerALUExprCycle] at prep
                          rw [directCall, multipleCall, omrCall, noWriteCall, barCall, inputCall,
                            mixedCall, flushCall] at prep
                          dsimp only at prep
                          cases preparedCall : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files oldSlots cycle mixedAccesses flushSelection reduced with
                          | failure => rw [preparedCall] at prep; simp at prep
                          | unknown => rw [preparedCall] at prep; simp at prep
                          | ok result =>
                            rw [preparedCall] at prep
                            dsimp only at prep
                            obtain ⟨memoryWrites, omrWrite⟩ := result
                            split at prep
                            · simp at prep
                            · simp at prep
                            · rename_i slots' updated
                              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                              obtain ⟨rfl, rfl⟩ := prep
                              have memoryBank : mixedAccesses.memory.bank ≠ PEMemory.Bank.lm1 := by
                                obtain ⟨destination, resolved, destinationMem⟩ :=
                                  parsedIntegerMaskMemoryThenInputExprAccessesInLine?_memory_resolution ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
                                    files control.directive hasSingleLineMask control.context.group
                                    control.context.l2b control.context.l1b control.context.mab
                                    control.context.pe cycle control.context.bar0 control.context.bar1
                                    control.context.tWord name parsedPrecision unsigned arg rfl
                                    mixedAccesses mixedCall
                                exact destination_bank_ne_of_static destination control.context.pe cycle
                                  control.context.bar0 control.context.bar1 control.context.tWord
                                  mixedAccesses.memory
                                  (noLm1 destination destinationMem) resolved
                              intro item member
                              exact prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_lm1_free
                                files oldSlots cycle mixedAccesses flushSelection reduced
                                memoryWrites omrWrite memoryBank preparedCall item member
                      | none =>
                        cases reverseCall : parsedIntegerMaskInputThenMemoryExprAccessesInLine? ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
                        | some reverseAccesses =>
                          cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
                          | none =>
                            simp [prepareParsedIntegerALUExprCycle, directCall, multipleCall, omrCall,
                              noWriteCall, barCall, inputCall, mixedCall, reverseCall, flushCall] at prep
                          | some flushSelection =>
                            simp only [prepareParsedIntegerALUExprCycle] at prep
                            rw [directCall, multipleCall, omrCall, noWriteCall, barCall, inputCall,
                              mixedCall, reverseCall, flushCall] at prep
                            dsimp only at prep
                            cases preparedCall : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files oldSlots cycle reverseAccesses control.directive hasSingleLineMask flushSelection reduced with
                            | failure => rw [preparedCall] at prep; simp at prep
                            | unknown => rw [preparedCall] at prep; simp at prep
                            | ok result =>
                              rw [preparedCall] at prep
                              dsimp only at prep
                              obtain ⟨memoryWrites, omrWrite⟩ := result
                              split at prep
                              · simp at prep
                              · simp at prep
                              · rename_i slots' updated
                                simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                obtain ⟨rfl, rfl⟩ := prep
                                have memoryBank : reverseAccesses.memory.bank ≠ PEMemory.Bank.lm1 := by
                                  have memoryResolution :=
                                    parsedIntegerMaskInputThenMemoryExprAccessesInLine?_memory_resolution ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
                                      files control.directive hasSingleLineMask control.context.group
                                      control.context.l2b control.context.l1b control.context.mab
                                      control.context.pe cycle control.context.bar0 control.context.bar1
                                      control.context.tWord name parsedPrecision unsigned arg rfl
                                      reverseAccesses reverseCall
                                  exact destination_bank_ne_of_static reverseAccesses.memoryOperand
                                    control.context.pe cycle control.context.bar0 control.context.bar1
                                    control.context.tWord reverseAccesses.memory
                                    (noLm1 reverseAccesses.memoryOperand memoryResolution.2)
                                    memoryResolution.1
                                intro item member
                                exact prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_lm1_free
                                  files oldSlots cycle reverseAccesses control.directive
                                  hasSingleLineMask flushSelection reduced memoryWrites omrWrite
                                  memoryBank preparedCall item (List.mem_append_left _ member)
                        | none =>
                          unfold prepareParsedIntegerALUExprCycle at prep
                          dsimp only at prep
                          rw [directCall, multipleCall, omrCall, noWriteCall, barCall, inputCall,
                            mixedCall, reverseCall] at prep
                          dsimp only at prep
                          cases destinations with
                          | nil => simp at prep
                          | cons destination rest =>
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
  | zero =>
      cases loweredCall : ParsedExpr.toDirectMaskedConstantWrites? ⟨.zero, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
      | none => simp [prepareParsedIntegerALUExprCycle, loweredCall] at prep
      | some targets =>
          cases preparedCall : prepareParsedMaskedConstantWrites files cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, loweredCall, preparedCall] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, loweredCall, preparedCall] at prep
          | ok destinationWrites =>
              cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
              | none =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [loweredCall] at prep
                  dsimp only at prep
                  rw [preparedCall, zero_has_execution_request, flushCall] at prep
                  dsimp only at prep
                  simp at prep
              | some flushSelection =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [loweredCall] at prep
                  dsimp only at prep
                  rw [preparedCall, zero_has_execution_request, flushCall] at prep
                  dsimp only at prep
                  split at prep
                  · simp at prep
                  · simp at prep
                  · rename_i slots' updated
                    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                    obtain ⟨rfl, rfl⟩ := prep
                    intro item member
                    rcases List.mem_append.mp member with earlier | later
                    · exact prepareParsedMaskedConstantWrites_lm1_free files cycle targets
                        destinationWrites preparedCall (fun target targetMem accesses isMemory => by
                          obtain ⟨destination, destinationMem, destinationLowered⟩ :=
                            toDirectMaskedConstantWrites?_mem_provenance
                              ⟨.zero, sources, destinations, flush, text⟩
                              files.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord targets loweredCall target
                              targetMem
                          rw [isMemory] at destinationLowered
                          exact destination_bank_ne_of_static destination control.context.pe cycle
                            control.context.bar0 control.context.bar1 control.context.tWord
                            accesses.destination (noLm1 destination destinationMem)
                            (toDirectMaskedConstantDestination?_memory_resolution
                              ⟨.zero, sources, destinations, flush, text⟩
                              files.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord destination accesses
                              destinationLowered)) item earlier
                    · rw [List.mem_singleton] at later
                      rw [later]
                      exact isLm1Write_eq_false_of_destination_none _ (by simp)
  | immediate payload sparse =>
      cases loweredCall : ParsedExpr.toDirectMaskedConstantWrites? ⟨.immediate payload sparse, sources, destinations, flush, text⟩ files.maskRegisters control.directive hasSingleLineMask control.context.group control.context.l2b control.context.l1b control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord with
      | none => simp [prepareParsedIntegerALUExprCycle, loweredCall] at prep
      | some targets =>
          cases preparedCall : prepareParsedMaskedConstantWrites files cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, loweredCall, preparedCall] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, loweredCall, preparedCall] at prep
          | ok destinationWrites =>
              cases flushCall : resolveFlushSelection? flush files.maskRegisters cycle with
              | none =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [loweredCall] at prep
                  dsimp only at prep
                  rw [preparedCall, immediate_has_execution_request, flushCall] at prep
                  dsimp only at prep
                  simp at prep
              | some flushSelection =>
                  simp only [prepareParsedIntegerALUExprCycle] at prep
                  rw [loweredCall] at prep
                  dsimp only at prep
                  rw [preparedCall, immediate_has_execution_request, flushCall] at prep
                  dsimp only at prep
                  split at prep
                  · simp at prep
                  · simp at prep
                  · rename_i slots' updated
                    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                    obtain ⟨rfl, rfl⟩ := prep
                    intro item member
                    rcases List.mem_append.mp member with earlier | later
                    · exact prepareParsedMaskedConstantWrites_lm1_free files cycle targets
                        destinationWrites preparedCall (fun target targetMem accesses isMemory => by
                          obtain ⟨destination, destinationMem, destinationLowered⟩ :=
                            toDirectMaskedConstantWrites?_mem_provenance
                              ⟨.immediate payload sparse, sources, destinations, flush, text⟩
                              files.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord targets loweredCall target
                              targetMem
                          rw [isMemory] at destinationLowered
                          exact destination_bank_ne_of_static destination control.context.pe cycle
                            control.context.bar0 control.context.bar1 control.context.tWord
                            accesses.destination (noLm1 destination destinationMem)
                            (toDirectMaskedConstantDestination?_memory_resolution
                              ⟨.immediate payload sparse, sources, destinations, flush, text⟩
                              files.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord destination accesses
                              destinationLowered)) item earlier
                    · rw [List.mem_singleton] at later
                      rw [later]
                      exact isLm1Write_eq_false_of_destination_none _ (by simp)
  | mau precision matrix kind half round =>
      simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixWrite precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixRead precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | wait tag => simp [prepareParsedIntegerALUExprCycle] at prep
  | noforward => simp [prepareParsedIntegerALUExprCycle] at prep
  | l1bm operation => simp [prepareParsedIntegerALUExprCycle] at prep
  | l2bm operation => simp [prepareParsedIntegerALUExprCycle] at prep

theorem prepareParsedIntegerALUCycles_lm1_free
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (cycles : List (Fin 4)) (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
      (finalWrites : List PreparedParsedMaskedWrite)
      (finalSlots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUCycles files oldSlots expression control hasSingleLineMask
        noForward reduced cycles writes nextSlots = .ok (finalWrites, finalSlots) →
      (∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false) →
      ∀ write ∈ finalWrites, PreparedParsedMaskedWrite.isLm1Write write = false := by
  intro cycles
  induction cycles with
  | nil =>
      intro writes nextSlots finalWrites finalSlots executed prior
      simp only [prepareParsedIntegerALUCycles, StepResult.ok.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact prior
  | cons cycle rest ih =>
      intro writes nextSlots finalWrites finalSlots executed prior
      simp only [prepareParsedIntegerALUCycles] at executed
      cases result : prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression
          control hasSingleLineMask noForward reduced cycle with
      | failure => rw [result] at executed; simp at executed
      | unknown => rw [result] at executed; simp at executed
      | ok cycleResult =>
          rw [result] at executed
          dsimp only at executed
          obtain ⟨cycleWrites, cycleSlots⟩ := cycleResult
          have cycleFree := prepareParsedIntegerALUExprCycle_lm1_free files oldSlots nextSlots
            expression control hasSingleLineMask noForward reduced cycle cycleWrites cycleSlots
            result noLm1
          exact ih (writes ++ cycleWrites) cycleSlots finalWrites finalSlots executed
            (fun write member =>
              (List.mem_append.mp member).elim (prior write) (cycleFree write))

theorem prepareParsedIntegerALUExprCycles_lm1_free
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (prepared : prepareParsedIntegerALUExprCycles files oldSlots initialSlots expression control
      hasSingleLineMask noForward reduced = .ok (writes, nextSlots)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  unfold prepareParsedIntegerALUExprCycles at prepared
  exact prepareParsedIntegerALUCycles_lm1_free files oldSlots expression control
    hasSingleLineMask noForward reduced noLm1 [0, 1, 2, 3] [] initialSlots writes nextSlots
    prepared (fun write member => by simp at member)


theorem prepareParsedMatrixReadCycle_lm1_free
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (accesses : ParsedMatrixReadAccesses) (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (lowered : ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters directive
      hasSingleLineMask context = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters context.cycle =
      some flushSelection)
    (prepared : prepareParsedMatrixReadCycle files slots store expression directive
      hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  have targetsMapped : expression.destinations.mapM (fun target =>
      parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask context target) =
        some accesses.targets := by
    have bridge := (toDirectMatrixReadAccesses?_eq expression precision sideY width row op
      sources files.maskRegisters directive hasSingleLineMask context).symm
    rw [lowered] at bridge
    have bridge' : Option.bind
        (expression.destinations.mapM (fun target => parsedMatrixReadTargetAt? files.maskRegisters
          directive hasSingleLineMask context target))
        (fun targets => some (⟨precision, sideY, row.val, targets⟩ :
          ParsedMatrixReadAccesses)) = some accesses := bridge
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at bridge'
    obtain ⟨targets, targetsMapped, accessesEq⟩ := bridge'
    rw [← accessesEq]
    exact targetsMapped
  have targetFree := prepareParsedMatrixReadTargets_lm1_free_of_expression expression
    files directive hasSingleLineMask noForward context accesses
    (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context))
    noLm1 targetsMapped
  unfold prepareParsedMatrixReadCycle at prepared
  rw [lowered, flushResolved] at prepared
  dsimp only at prepared
  cases targetCall : prepareParsedMatrixReadTargets accesses.targets
      (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context)) with
  | failure => rw [targetCall] at prepared; simp at prepared
  | unknown => rw [targetCall] at prepared; simp at prepared
  | ok result =>
      obtain ⟨doneWrites, doneBars⟩ := result
      rw [targetCall] at prepared
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      exact prepareParsedMatrixReadTargets_lm1_free accesses.targets _ targetFree
        doneWrites doneBars targetCall

theorem prepareParsedMatrixReadCycles_lm1_free
    (files : IntegerRegisterFiles) (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (cycles : List (Fin 4)) (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdates : List (Bool × BitVec 12))
      (finalWrites : List PreparedParsedMaskedWrite)
      (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
      (finalBars : List (Bool × BitVec 12)),
      prepareParsedMatrixReadCycles files store expression directive hasSingleLineMask
        noForward context cycles writes nextSlots barUpdates =
          .ok (finalWrites, finalSlots, finalBars) →
      (∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false) →
      ∀ write ∈ finalWrites, PreparedParsedMaskedWrite.isLm1Write write = false := by
  intro cycles
  induction cycles with
  | nil =>
      intro writes nextSlots barUpdates finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedMatrixReadCycles, StepResult.ok.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      exact prior
  | cons cycle rest ih =>
      intro writes nextSlots barUpdates finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedMatrixReadCycles] at executed
      cases result : prepareParsedMatrixReadCycle files nextSlots store expression directive
          hasSingleLineMask noForward { context with cycle := cycle } with
      | failure => rw [result] at executed; simp at executed
      | unknown => rw [result] at executed; simp at executed
      | ok cycleResult =>
          rw [result] at executed
          dsimp only at executed
          obtain ⟨cycleWrites, cycleSlots, cycleBars⟩ := cycleResult
          cases accessesCall : ParsedExpr.toDirectMatrixReadAccesses? expression
              files.maskRegisters directive hasSingleLineMask { context with cycle := cycle } with
          | none =>
              unfold prepareParsedMatrixReadCycle at result
              rw [accessesCall] at result
              simp at result
          | some accesses =>
              obtain ⟨flushSelection, flushResolved⟩ :=
                resolveFlushSelection?_always_resolves expression.flush files.maskRegisters cycle
              have cycleFree := prepareParsedMatrixReadCycle_lm1_free files nextSlots store
                expression directive hasSingleLineMask noForward { context with cycle := cycle }
                precision sideY width row op sources accesses flushSelection cycleWrites
                cycleSlots cycleBars noLm1 accessesCall flushResolved result
              exact ih (writes ++ cycleWrites) cycleSlots (barUpdates ++ cycleBars)
                finalWrites finalSlots finalBars executed
                (fun write member =>
                  (List.mem_append.mp member).elim (prior write) (cycleFree write))

theorem prepareParsedMatrixReadExprCycles_lm1_free
    (files : IntegerRegisterFiles) (initialSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (prepared : prepareParsedMatrixReadExprCycles files initialSlots store expression directive
      hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  unfold prepareParsedMatrixReadExprCycles at prepared
  exact prepareParsedMatrixReadCycles_lm1_free files store expression directive hasSingleLineMask
    noForward context precision sideY width row op sources noLm1 parsedMatrixReadCycles []
    initialSlots [] writes nextSlots bars prepared (fun write member => by simp at member)

theorem prepareParsedMatrixReadLineExpression_lm1_free
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (prepared : prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
      expression control hasSingleLineMask noForward reduced = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  unfold prepareParsedIntegerMatrixReadLineExpression at prepared
  rw [op] at prepared
  dsimp only at prepared
  cases result : prepareParsedMatrixReadExprCycles files nextSlots store expression
      control.directive hasSingleLineMask noForward control.context with
  | failure => rw [result] at prepared; simp at prepared
  | unknown => rw [result] at prepared; simp at prepared
  | ok cycleResult =>
      obtain ⟨matrixWrites, matrixSlots, matrixBars⟩ := cycleResult
      rw [result] at prepared
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      exact prepareParsedMatrixReadExprCycles_lm1_free files nextSlots store expression
        control.directive hasSingleLineMask noForward control.context precision sideY width row
        op sources matrixWrites matrixSlots matrixBars noLm1 result


theorem prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (precision : ParsedPrecision) (op : expression.op = .matrixRead precision)
    (loweredNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses? expression
      files.maskRegisters control.directive hasSingleLineMask
      { control.context with cycle := cycle } = none) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store expression
      control hasSingleLineMask noForward reduced = .unknown := by
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [op]
  dsimp only
  have cycleUnknown : prepareParsedMatrixReadCycle files nextSlots store expression
      control.directive hasSingleLineMask noForward { control.context with cycle := 0 } =
        .unknown := by
    unfold prepareParsedMatrixReadCycle
    rw [loweredNone 0]
  have cyclesUnknown : prepareParsedMatrixReadCycles files store expression control.directive
      hasSingleLineMask noForward control.context [0, 1, 2, 3] [] nextSlots [] = .unknown := by
    simp only [prepareParsedMatrixReadCycles]
    rw [cycleUnknown]
  unfold prepareParsedMatrixReadExprCycles
  rw [show parsedMatrixReadCycles = [0, 1, 2, 3] from rfl]
  rw [cyclesUnknown]

theorem prepareParsedIntegerMatrixReadLineExpression_lm1_free
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (prepared : prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
      expression control hasSingleLineMask noForward reduced = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | wait tag =>
      simp only [prepareParsedIntegerMatrixReadLineExpression, StepResult.ok.injEq,
        Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      intro write member
      simp at member
  | noforward =>
      simp only [prepareParsedIntegerMatrixReadLineExpression, StepResult.ok.injEq,
        Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      intro write member
      simp at member
  | alu name precision unsigned arg =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prepared
      dsimp only at prepared
      cases cyclesCall : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ control
          hasSingleLineMask noForward reduced with
      | failure => rw [cyclesCall] at prepared; simp at prepared
      | unknown => rw [cyclesCall] at prepared; simp at prepared
      | ok result =>
          obtain ⟨cycleWrites, cycleSlots⟩ := result
          rw [cyclesCall] at prepared
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
          obtain ⟨rfl, rfl, rfl⟩ := prepared
          exact prepareParsedIntegerALUExprCycles_lm1_free files oldSlots
            ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ control
            hasSingleLineMask noForward reduced nextSlots cycleWrites cycleSlots noLm1 cyclesCall
  | zero =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prepared
      dsimp only at prepared
      cases cyclesCall : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.zero, sources, destinations, flush, text⟩ control hasSingleLineMask noForward
          reduced with
      | failure => rw [cyclesCall] at prepared; simp at prepared
      | unknown => rw [cyclesCall] at prepared; simp at prepared
      | ok result =>
          obtain ⟨cycleWrites, cycleSlots⟩ := result
          rw [cyclesCall] at prepared
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
          obtain ⟨rfl, rfl, rfl⟩ := prepared
          exact prepareParsedIntegerALUExprCycles_lm1_free files oldSlots
            ⟨.zero, sources, destinations, flush, text⟩ control hasSingleLineMask noForward
            reduced nextSlots cycleWrites cycleSlots noLm1 cyclesCall
  | immediate payload sparse =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prepared
      dsimp only at prepared
      cases cyclesCall : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control
          hasSingleLineMask noForward reduced with
      | failure => rw [cyclesCall] at prepared; simp at prepared
      | unknown => rw [cyclesCall] at prepared; simp at prepared
      | ok result =>
          obtain ⟨cycleWrites, cycleSlots⟩ := result
          rw [cyclesCall] at prepared
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
          obtain ⟨rfl, rfl, rfl⟩ := prepared
          exact prepareParsedIntegerALUExprCycles_lm1_free files oldSlots
            ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control
            hasSingleLineMask noForward reduced nextSlots cycleWrites cycleSlots noLm1 cyclesCall
  | matrixRead precision =>
      cases sources with
      | nil =>
          have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
              ⟨.matrixRead precision, [], destinations, flush, text⟩ files.maskRegisters
              control.directive hasSingleLineMask { control.context with cycle := cycle } =
                none := by
            intro cycle
            simp [ParsedExpr.toDirectMatrixReadAccesses?]
          rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files oldSlots
            nextSlots store ⟨.matrixRead precision, [], destinations, flush, text⟩ control
            hasSingleLineMask noForward reduced precision rfl lowerNone] at prepared
          simp at prepared
      | cons source rest =>
          cases rest with
          | nil =>
              cases source with
              | matrix sideY width row =>
                  cases row with
                  | none =>
                      have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                          ⟨.matrixRead precision,
                            [.matrix sideY width none], destinations, flush, text⟩
                          files.maskRegisters control.directive hasSingleLineMask
                          { control.context with cycle := cycle } = none := by
                        intro cycle
                        simp [ParsedExpr.toDirectMatrixReadAccesses?]
                      rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown
                        files oldSlots nextSlots store
                        ⟨.matrixRead precision, [.matrix sideY width none], destinations,
                          flush, text⟩ control hasSingleLineMask noForward reduced precision
                        rfl lowerNone] at prepared
                      simp at prepared
                  | some rowValue =>
                      unfold prepareParsedIntegerMatrixReadLineExpression at prepared
                      dsimp only at prepared
                      cases matrixCall : prepareParsedMatrixReadExprCycles files nextSlots
                          store ⟨.matrixRead precision, [.matrix sideY width (some rowValue)],
                            destinations, flush, text⟩ control.directive hasSingleLineMask
                          noForward control.context with
                      | failure => rw [matrixCall] at prepared; simp at prepared
                      | unknown => rw [matrixCall] at prepared; simp at prepared
                      | ok result =>
                          obtain ⟨matrixWrites, matrixSlots, matrixBars⟩ := result
                          rw [matrixCall] at prepared
                          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
                          obtain ⟨rfl, rfl, rfl⟩ := prepared
                          exact prepareParsedMatrixReadExprCycles_lm1_free files nextSlots store
                            ⟨.matrixRead precision, [.matrix sideY width (some rowValue)],
                              destinations, flush, text⟩ control.directive hasSingleLineMask
                            noForward control.context precision sideY width rowValue rfl rfl
                            matrixWrites matrixSlots matrixBars noLm1 matrixCall
              | mem access negated extended rounded mask =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision,
                        [.mem access negated extended rounded mask], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision,
                      [.mem access negated extended rounded mask], destinations, flush, text⟩
                    control hasSingleLineMask noForward reduced precision rfl lowerNone] at prepared
                  simp at prepared
              | bar lm1 width mask =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.bar lm1 width mask], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.bar lm1 width mask],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
              | forward kind negated extended rounded =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.forward kind negated extended rounded],
                        destinations, flush, text⟩ files.maskRegisters control.directive
                      hasSingleLineMask { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision,
                      [.forward kind negated extended rounded], destinations, flush, text⟩
                    control hasSingleLineMask noForward reduced precision rfl lowerNone] at prepared
                  simp at prepared
              | fixed kind =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.fixed kind], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.fixed kind],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
              | omr entry mask =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.omr entry mask], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.omr entry mask],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
              | nowrite =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.nowrite], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.nowrite], destinations,
                      flush, text⟩ control hasSingleLineMask noForward reduced precision rfl
                    lowerNone] at prepared
                  simp at prepared
              | l1bm width address =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.l1bm width address], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.l1bm width address],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
              | l2bm address l2b =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.l2bm address l2b], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.l2bm address l2b],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
              | dar address =>
                  have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                      ⟨.matrixRead precision, [.dar address], destinations, flush, text⟩
                      files.maskRegisters control.directive hasSingleLineMask
                      { control.context with cycle := cycle } = none := by
                    intro cycle
                    simp [ParsedExpr.toDirectMatrixReadAccesses?]
                  rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files
                    oldSlots nextSlots store ⟨.matrixRead precision, [.dar address],
                      destinations, flush, text⟩ control hasSingleLineMask noForward reduced
                    precision rfl lowerNone] at prepared
                  simp at prepared
          | cons second tail =>
              have lowerNone : ∀ cycle : Fin 4, ParsedExpr.toDirectMatrixReadAccesses?
                  ⟨.matrixRead precision, source :: second :: tail, destinations, flush, text⟩
                  files.maskRegisters control.directive hasSingleLineMask
                  { control.context with cycle := cycle } = none := by
                intro cycle
                simp [ParsedExpr.toDirectMatrixReadAccesses?]
              rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead_unknown files oldSlots
                nextSlots store ⟨.matrixRead precision, source :: second :: tail, destinations,
                  flush, text⟩ control hasSingleLineMask noForward reduced precision rfl
                lowerNone] at prepared
              simp at prepared
  | mau precision matrix kind half round =>
      simp [prepareParsedIntegerMatrixReadLineExpression] at prepared
  | matrixWrite precision =>
      simp [prepareParsedIntegerMatrixReadLineExpression] at prepared
  | l1bm operation =>
      simp [prepareParsedIntegerMatrixReadLineExpression] at prepared
  | l2bm operation =>
      simp [prepareParsedIntegerMatrixReadLineExpression] at prepared


theorem prepareParsedIntegerMatrixReadLineExpressions_lm1_free
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (expressions : List ParsedExpr)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) :
    ∀ (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdates : List (Bool × BitVec 12))
      (finalWrites : List PreparedParsedMaskedWrite)
      (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
      (finalBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        hasSingleLineMask noForward reduced expressions writes nextSlots barUpdates =
          .ok (finalWrites, finalSlots, finalBars) →
      (∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false) →
      ∀ write ∈ finalWrites, PreparedParsedMaskedWrite.isLm1Write write = false := by
  induction expressions with
  | nil =>
      intro writes nextSlots barUpdates finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      exact prior
  | cons expression rest ih =>
      intro writes nextSlots barUpdates finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at executed
      cases result : prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
          expression control hasSingleLineMask noForward reduced with
      | failure => rw [result] at executed; simp at executed
      | unknown => rw [result] at executed; simp at executed
      | ok expressionResult =>
          rw [result] at executed
          dsimp only at executed
          obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := expressionResult
          have headFree := prepareParsedIntegerMatrixReadLineExpression_lm1_free files oldSlots
            nextSlots store expression control hasSingleLineMask noForward reduced
            expressionWrites expressionSlots expressionBars
            (noLm1 expression (by simp)) result
          exact ih (fun item member => noLm1 item (List.mem_cons_of_mem _ member))
            (writes ++ expressionWrites) expressionSlots (barUpdates ++ expressionBars)
            finalWrites finalSlots finalBars executed
            (fun write member =>
              (List.mem_append.mp member).elim (prior write) (headFree write))

theorem prepareParsedIntegerMatrixReadLineCycles_lm1_free
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots store expressions
      control reduced = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false := by
  unfold prepareParsedIntegerMatrixReadLineCycles at prepared
  exact prepareParsedIntegerMatrixReadLineExpressions_lm1_free files oldSlots store control
    _ _ reduced expressions noLm1 [] oldSlots [] writes nextSlots bars prepared
    (fun write member => by simp at member)

theorem welcomePEIntegerStageLm1Provenance : WelcomePEIntegerStageLm1Provenance := by
  intro expressions state pe writes slots bars prepared noLm1 write member
  unfold welcomeIntegerPrep at prepared
  exact prepareParsedIntegerMatrixReadLineCycles_lm1_free (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl state pe) false noLm1 writes slots bars prepared write member


end ProofsLean.MNCore
