import ProofsLean.ParsedIntegerStep
import ProofsLean.WelcomePlainShape

/-! # Request provenance and destination projection for the plain integer-ALU cycle

## The obstruction this module removes

`prepareParsedIntegerALUExprCycle` (and the in-line lowering
`ParsedExpr.toDirectMaskedIntegerAccessesInLine?` it calls first) contains the
dependent match

```
match hRequest : expression.op.executionRequest with
| .ok (.integer precision aluOp) => ...
| _ => none
```

The result of that match is the *only* source of the prepared write list and its
destinations.  When `expression.op`'s `ParsedAluName`/`ParsedPrecision` are
symbolic, `rw` cannot rewrite the scrutinee (the motive mentions `hRequest`, as
in the standard dependent-`match` rewriting failure), so no projection of the
destination list out of a successful run is available.

## The route

1. **Per-`(name, precision)` request provenance.**  `executionRequest` is a
   two-step reduction: `ParsedOp.integerRequest` checks
   `ParsedAluName.supportsIntegerAt` and then applies
   `ParsedAluName.toIntegerOp`; `ParsedOp.executionRequest` lifts the integer
   request.  For the 29 `(name, precision)` pairs that the answers in
   `problems/challenge/*/answer.vsm` and `problems/*/answer.vsm` actually use
   *and* that support integer execution, both steps are definitional, so
   `alu_<name>_<precision>_executionRequest` is proved by `rfl`.  (The mnemonic
   set was mapped through `viz/core/src/vsm.rs`, not by grepping Lean: e.g.
   `dvpassa` is a MAU op, `msl`/`msr` are untyped and never integer requests,
   and `hbfe` is BFE, not an integer ALU op.)
2. **Branch provenance.**  `toDirectMaskedIntegerAccessesInLine?_alu_unary` and
   `..._binary` take the concrete request equation as a hypothesis, eliminate
   the structure/`op` equality by `cases`, then reduce the dependent match with
   the request equation; they return the lowered accesses together with the
   source/destination projections.
3. **Destination projection.**  `prepareParsedIntegerALUExprCycle_alu_destination_of_lowered`
   projects a successful cycle to exactly one prepared write whose destination
   is the lowered destination, and `prepareParsedIntegerALUExprCycles_destination_map`
   composes the four cycles into the destination list
   `[d 0, d 1, d 2, d 3]` (a function of the control, in particular of
   `control.context.bar1` through `toDirectMemoryAccessMode?`).

The statements are independent of any machine, problem, input or state: the
only hypotheses are an op-shape equation, one of the request lemmas, and the
lowering successes.  A problem track supplies the last pieces for its concrete
rows (typically by `simp` on the operand constructors), exactly as
`ProofsLean/PlusTwoSuffixFrame.lean` does for the four `2.plus-two` suffix lines.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Request provenance for the pairs the answers use -/

/-- The `inc` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_inc_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .inc (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.arith .inc unsigned)) := rfl

/-- The `inc` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_inc_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .inc (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.arith .inc unsigned)) := rfl

/-- The `dec` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_dec_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .dec (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.arith .dec unsigned)) := rfl

/-- The `not` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_not_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .not (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.bitNot)) := rfl

/-- The `and` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_and_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .and (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.bitAnd)) := rfl

/-- The `and` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_and_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .and (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.bitAnd)) := rfl

/-- The `and` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_and_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .and (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.bitAnd)) := rfl

/-- The `or` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_or_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .or (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.bitOr)) := rfl

/-- The `or` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_or_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .or (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.bitOr)) := rfl

/-- The `xor` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_xor_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .xor (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.bitXor)) := rfl

/-- The `add` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_add_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .add (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.arith .add unsigned)) := rfl

/-- The `add` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_add_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .add (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.arith .add unsigned)) := rfl

/-- The `add` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_add_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .add (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.arith .add unsigned)) := rfl

/-- The `sub` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_sub_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .sub (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.arith .sub unsigned)) := rfl

/-- The `sub` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_sub_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .sub (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.arith .sub unsigned)) := rfl

/-- The `max` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_max_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .max (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.maximum unsigned)) := rfl

/-- The `packbit` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_packbit_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .packbit (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.packbit)) := rfl

/-- The `packbit` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_packbit_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .packbit (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.packbit)) := rfl

/-- The `passa` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_passa_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .passa (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.passa)) := rfl

/-- The `passa` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_passa_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .passa (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.passa)) := rfl

/-- The `passa` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_passa_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .passa (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.passa)) := rfl

/-- The `lsl` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_lsl_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .lsl (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.shift .left)) := rfl

/-- The `lsl` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_lsl_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .lsl (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.shift .left)) := rfl

/-- The `lsl` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_lsl_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .lsl (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.shift .left)) := rfl

/-- The `lsr` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_lsr_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .lsr (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.shift (.right unsigned))) := rfl

/-- The `lsr` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_lsr_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .lsr (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.shift (.right unsigned))) := rfl

/-- The `bsl` request at precision `.i` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_bsl_i_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .bsl (some .i) unsigned arg).executionRequest =
      .ok (.integer .word (.shift .rotateLeft)) := rfl

/-- The `bsl` request at precision `.l` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_bsl_l_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .bsl (some .l) unsigned arg).executionRequest =
      .ok (.integer .long (.shift .rotateLeft)) := rfl

/-- The `bsl` request at precision `.s` reduces structurally: the
`supportsIntegerAt` guard is `true` and `toIntegerOp` is the displayed op. -/
theorem alu_bsl_s_executionRequest (unsigned : Bool) (arg : Option (Fin 256)) :
    (ParsedOp.alu .bsl (some .s) unsigned arg).executionRequest =
      .ok (.integer .half (.shift .rotateLeft)) := rfl

/-! ## 2. Branch provenance of the in-line lowering

Both lemmas eliminate the expression structure first, so that `cases` on the
op-shape equation replaces the `ParsedOp` by its constructor; the dependent
match can then be rewritten with the request equation, which is the step that
`rw`/`simp` cannot perform while the name and precision are symbolic. -/

/-- **Unary branch provenance.**  A one-source integer ALU row whose request is
`(.integer p aluOp)` lowers to the accesses built from the given source,
destination, write selection and flush selection. -/
theorem toDirectMaskedIntegerAccessesInLine?_alu_unary
    (expression : ParsedExpr) (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (p : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : expression.op.executionRequest = .ok (.integer p aluOp))
    (inputCount : name.inputCount = 1)
    (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (source destination : ParsedOperand)
    (sourcesShape : expression.sources = [source])
    (destinationsShape : expression.destinations = [destination])
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (sourceAccess : ParsedIntegerInput) (destinationAccess : DirectMemoryAccess)
    (writeSelection : PEWordSelection) (flushSelection : Option PEWordSelection)
    (sourceEq : ParsedOperand.toParsedIntegerInput? source precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some sourceAccess)
    (destinationEq : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord
      = some destinationAccess)
    (selectionEq : ParsedOperand.resolveMemoryWriteSelection? destination destinationAccess.bank
      registers cycle directive hasSingleLineMask = some writeSelection)
    (flushEq : resolveFlushSelection? expression.flush registers cycle = some flushSelection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      accesses.sourceX = sourceAccess ∧
      accesses.sourceY = sourceAccess ∧
      accesses.destination = destinationAccess ∧
      accesses.writeSelection = writeSelection ∧
      accesses.flushSelection = flushSelection := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape request sourcesShape destinationsShape flushEq
  cases opShape
  subst sourcesShape
  subst destinationsShape
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  dsimp only
  split
  · rename_i precision' aluOp' heq
    rw [request] at heq
    cases heq
    simp only [inputCount, ParsedAluName.integerInputCount, sourceEq, destinationEq,
      selectionEq, flushEq]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i bad
    rw [request] at bad
    simp at bad

/-- **Binary branch provenance.**  The two-source counterpart of the unary
lemma; the destination and selections are those of the single destination
operand. -/
theorem toDirectMaskedIntegerAccessesInLine?_alu_binary
    (expression : ParsedExpr) (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (p : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : expression.op.executionRequest = .ok (.integer p aluOp))
    (inputCount : name.inputCount = 2)
    (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (sourceX sourceY destination : ParsedOperand)
    (sourcesShape : expression.sources = [sourceX, sourceY])
    (destinationsShape : expression.destinations = [destination])
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (xAccess yAccess : ParsedIntegerInput) (destinationAccess : DirectMemoryAccess)
    (writeSelection : PEWordSelection) (flushSelection : Option PEWordSelection)
    (sourceXEq : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some xAccess)
    (sourceYEq : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some yAccess)
    (destinationEq : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord
      = some destinationAccess)
    (selectionEq : ParsedOperand.resolveMemoryWriteSelection? destination destinationAccess.bank
      registers cycle directive hasSingleLineMask = some writeSelection)
    (flushEq : resolveFlushSelection? expression.flush registers cycle = some flushSelection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      accesses.sourceX = xAccess ∧
      accesses.sourceY = yAccess ∧
      accesses.destination = destinationAccess ∧
      accesses.writeSelection = writeSelection ∧
      accesses.flushSelection = flushSelection := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape request sourcesShape destinationsShape flushEq
  cases opShape
  subst sourcesShape
  subst destinationsShape
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  dsimp only
  split
  · rename_i precision' aluOp' heq
    rw [request] at heq
    cases heq
    simp only [inputCount, ParsedAluName.integerInputCount, sourceXEq, sourceYEq,
      destinationEq, selectionEq, flushEq]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i bad
    rw [request] at bad
    simp at bad

/-- **Unary branch provenance, destination-triple form.**  Same as
`toDirectMaskedIntegerAccessesInLine?_alu_unary`, but the destination is given
by its `(bank, width, word)` triple, which avoids constructing the `Fin`
address proof in clients. -/
theorem toDirectMaskedIntegerAccessesInLine?_alu_unary_triple
    (expression : ParsedExpr) (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (p : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : expression.op.executionRequest = .ok (.integer p aluOp))
    (inputCount : name.inputCount = 1)
    (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (source destination : ParsedOperand)
    (sourcesShape : expression.sources = [source])
    (destinationsShape : expression.destinations = [destination])
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (sourceAccess : ParsedIntegerInput)
    (destTriple : PEMemory.Bank × PEMemory.Width × Nat)
    (writeSelection : PEWordSelection) (flushSelection : Option PEWordSelection)
    (sourceEq : ParsedOperand.toParsedIntegerInput? source precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some sourceAccess)
    (destinationEq : (ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1
      tWord).map (fun d => (d.bank, d.width, d.address.val)) = some destTriple)
    (selectionEq : ParsedOperand.resolveMemoryWriteSelection? destination destTriple.1
      registers cycle directive hasSingleLineMask = some writeSelection)
    (flushEq : resolveFlushSelection? expression.flush registers cycle = some flushSelection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      (accesses.destination.bank, accesses.destination.width,
        accesses.destination.address.val) = destTriple := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape request sourcesShape destinationsShape flushEq
  cases opShape
  subst sourcesShape
  subst destinationsShape
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  dsimp only
  split
  · rename_i precision' aluOp' heq
    rw [request] at heq
    cases heq
    cases dm : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
    | none =>
        rw [dm] at destinationEq
        simp at destinationEq
    | some destinationAccess =>
        rw [dm] at destinationEq
        simp only [Option.map_some, Option.some.injEq] at destinationEq
        obtain ⟨bank, width, address⟩ := destinationAccess
        rw [← destinationEq] at selectionEq
        exact ⟨⟨.alu name (some precision) unsigned arg, sourceAccess, sourceAccess,
          ⟨bank, width, address⟩, writeSelection, flushSelection,
          ⟨.integer p aluOp, request⟩⟩, by
            simp [inputCount, ParsedAluName.integerInputCount, sourceEq, dm, selectionEq,
              flushEq], by
            rw [← destinationEq]⟩
  · rename_i bad
    rw [request] at bad
    simp at bad

/-- **Binary branch provenance, destination-triple form.** -/
theorem toDirectMaskedIntegerAccessesInLine?_alu_binary_triple
    (expression : ParsedExpr) (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (p : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : expression.op.executionRequest = .ok (.integer p aluOp))
    (inputCount : name.inputCount = 2)
    (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (sourceX sourceY destination : ParsedOperand)
    (sourcesShape : expression.sources = [sourceX, sourceY])
    (destinationsShape : expression.destinations = [destination])
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (xAccess yAccess : ParsedIntegerInput)
    (destTriple : PEMemory.Bank × PEMemory.Width × Nat)
    (writeSelection : PEWordSelection) (flushSelection : Option PEWordSelection)
    (sourceXEq : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some xAccess)
    (sourceYEq : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      group l2b l1b mab pe cycle bar0 bar1 tWord = some yAccess)
    (destinationEq : (ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1
      tWord).map (fun d => (d.bank, d.width, d.address.val)) = some destTriple)
    (selectionEq : ParsedOperand.resolveMemoryWriteSelection? destination destTriple.1
      registers cycle directive hasSingleLineMask = some writeSelection)
    (flushEq : resolveFlushSelection? expression.flush registers cycle = some flushSelection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      (accesses.destination.bank, accesses.destination.width,
        accesses.destination.address.val) = destTriple := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape request sourcesShape destinationsShape flushEq
  cases opShape
  subst sourcesShape
  subst destinationsShape
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  dsimp only
  split
  · rename_i precision' aluOp' heq
    rw [request] at heq
    cases heq
    cases dm : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
    | none =>
        rw [dm] at destinationEq
        simp at destinationEq
    | some destinationAccess =>
        rw [dm] at destinationEq
        simp only [Option.map_some, Option.some.injEq] at destinationEq
        obtain ⟨bank, width, address⟩ := destinationAccess
        rw [← destinationEq] at selectionEq
        exact ⟨⟨.alu name (some precision) unsigned arg, xAccess, yAccess,
          ⟨bank, width, address⟩, writeSelection, flushSelection,
          ⟨.integer p aluOp, request⟩⟩, by
            simp [inputCount, ParsedAluName.integerInputCount, sourceXEq, sourceYEq, dm,
              selectionEq, flushEq], by
            rw [← destinationEq]⟩
  · rename_i bad
    rw [request] at bad
    simp at bad

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue
open PEMemory

/-! ## 3. Projecting the destination out of a successful cycle -/

/-- **Single-cycle destination projection.**  If the in-line lowering of an
integer ALU row succeeds (with some op shape `.alu name (some precision) ...`),
then every successful `prepareParsedIntegerALUExprCycle` prepares exactly one
write and its destination is the lowered destination.  The data of the write
and the forwarding slots are not inspected. -/
theorem prepareParsedIntegerALUExprCycle_alu_destination_of_lowered
    (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (h : prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle = .ok (writes, slots)) :
    writes.map (fun w => w.destination) = [some accesses.destination] := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape lowered h
  cases opShape
  unfold prepareParsedIntegerALUExprCycle at h
  dsimp only at h
  rw [lowered] at h
  dsimp only at h
  cases p : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced with
  | failure => simp [p] at h
  | unknown => simp [p] at h
  | ok write =>
      rw [p] at h
      dsimp only at h
      cases u : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward with
      | failure => simp [u] at h
      | unknown => simp [u] at h
      | ok slots' =>
          rw [u] at h
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          simp only [List.map_cons, List.map_nil]
          rw [prepareParsedMaskedWriteWithForwarding_destination files oldSlots cycle
            accesses reduced write p]

/-- **Single-cycle write projection.**  The successful cycle prepares exactly
one write, whose destination is the lowered destination.  This is the
existential-write-list form of
`prepareParsedIntegerALUExprCycle_alu_destination_of_lowered`. -/
theorem prepareParsedIntegerALUExprCycle_alu_write_of_lowered
    (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (h : prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle = .ok (writes, slots)) :
    ∃ write, writes = [write] ∧ write.destination = some accesses.destination := by
  obtain ⟨opField, sources, destinations, flush, text⟩ := expression
  simp only at opShape lowered h
  cases opShape
  unfold prepareParsedIntegerALUExprCycle at h
  dsimp only at h
  rw [lowered] at h
  dsimp only at h
  cases p : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced with
  | failure => simp [p] at h
  | unknown => simp [p] at h
  | ok write =>
      rw [p] at h
      dsimp only at h
      cases u : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward with
      | failure => simp [u] at h
      | unknown => simp [u] at h
      | ok slots' =>
          rw [u] at h
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at h
          exact ⟨write, h.1.symm, prepareParsedMaskedWriteWithForwarding_destination files
            oldSlots cycle accesses reduced write p⟩

/-- **Four-cycle destination projection.**  The four-cycle preparation of an
integer ALU row appends one singleton write list per cycle, so its prepared
writes have exactly the four lowered destinations, in cycle order.  The
destination function `accesses` is arbitrary; it may read the whole control,
including `control.context.bar1`. -/
theorem prepareParsedIntegerALUExprCycles_destination_map
    (files : IntegerRegisterFiles)
    (oldSlots initialOutputSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (accesses : Fin 4 → ParsedMaskedIntegerAccesses)
    (lowered : ∀ cycle : Fin 4,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord = some (accesses cycle))
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (h : prepareParsedIntegerALUExprCycles files oldSlots initialOutputSlots expression control
      hasSingleLineMask noForward reduced = .ok (writes, slots)) :
    writes.map (fun w => w.destination) =
      [some (accesses 0).destination, some (accesses 1).destination,
        some (accesses 2).destination, some (accesses 3).destination] := by
  have single : ∀ (cycle : Fin 4) (writes' : List PreparedParsedMaskedWrite)
      (inSlots outSlots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycle files oldSlots inSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok (writes', outSlots) →
      writes'.map (fun w => w.destination) = [some (accesses cycle).destination] := by
    intro cycle writes' inSlots outSlots cycleEq
    exact prepareParsedIntegerALUExprCycle_alu_destination_of_lowered files oldSlots inSlots
      expression control hasSingleLineMask noForward reduced cycle name precision unsigned arg
      opShape (accesses cycle) (lowered cycle) writes' outSlots cycleEq
  unfold prepareParsedIntegerALUExprCycles at h
  simp only [parsedIntegerALUCycles] at h
  rw [prepareParsedIntegerALUCycles.eq_2] at h
  cases h0 : prepareParsedIntegerALUExprCycle files oldSlots initialOutputSlots expression control
      hasSingleLineMask noForward reduced 0 with
  | failure => simp [h0] at h
  | unknown => simp [h0] at h
  | ok result0 =>
      obtain ⟨writes0, slots0⟩ := result0
      simp only [h0] at h
      rw [prepareParsedIntegerALUCycles.eq_2] at h
      cases h1 : prepareParsedIntegerALUExprCycle files oldSlots slots0 expression control
          hasSingleLineMask noForward reduced 1 with
      | failure => simp [h1] at h
      | unknown => simp [h1] at h
      | ok result1 =>
          obtain ⟨writes1, slots1⟩ := result1
          simp only [h1] at h
          rw [prepareParsedIntegerALUCycles.eq_2] at h
          cases h2 : prepareParsedIntegerALUExprCycle files oldSlots slots1 expression control
              hasSingleLineMask noForward reduced 2 with
          | failure => simp [h2] at h
          | unknown => simp [h2] at h
          | ok result2 =>
              obtain ⟨writes2, slots2⟩ := result2
              simp only [h2] at h
              rw [prepareParsedIntegerALUCycles.eq_2] at h
              cases h3 : prepareParsedIntegerALUExprCycle files oldSlots slots2 expression control
                  hasSingleLineMask noForward reduced 3 with
              | failure => simp [h3] at h
              | unknown => simp [h3] at h
              | ok result3 =>
                  obtain ⟨writes3, slots3⟩ := result3
                  simp only [h3] at h
                  rw [prepareParsedIntegerALUCycles.eq_1] at h
                  simp only [StepResult.ok.injEq, Prod.mk.injEq] at h
                  rw [← h.1]
                  simp only [List.map_append, single 0 writes0 initialOutputSlots slots0 h0,
                    single 1 writes1 slots0 slots1 h1, single 2 writes2 slots1 slots2 h2,
                    single 3 writes3 slots2 slots3 h3, List.cons_append, List.nil_append]

/-- Mapping a function over the destinations of a write list is the same as
mapping it over the destination list of the writes. -/
theorem List.map_optionMap_destination {β : Type}
    (writes : List PreparedParsedMaskedWrite) (g : DirectMemoryAccess → β) :
    writes.map (fun w => Option.map g w.destination) =
      (writes.map (fun w => w.destination)).map (Option.map g) := by
  induction writes with
  | nil => rfl
  | cons write rest ih => simp only [List.map_cons, ih]

/-- **Four-cycle destination triples**, the form used by a value argument: if
each cycle's lowered destination has the triple `dest cycle`, the prepared
writes' destination triples are exactly `dest 0, dest 1, dest 2, dest 3`. -/
theorem prepareParsedIntegerALUExprCycles_destination_triples
    (files : IntegerRegisterFiles)
    (oldSlots initialOutputSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (dest : Fin 4 → PEMemory.Bank × PEMemory.Width × Nat)
    (lowered : ∀ cycle : Fin 4,
      ∃ accesses,
        ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
          control.directive hasSingleLineMask control.context.group control.context.l2b
          control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
          control.context.bar1 control.context.tWord = some accesses ∧
        (accesses.destination.bank, accesses.destination.width,
          accesses.destination.address.val) = dest cycle)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (h : prepareParsedIntegerALUExprCycles files oldSlots initialOutputSlots expression control
      hasSingleLineMask noForward reduced = .ok (writes, slots)) :
    writes.map (fun w => w.destination.map
        (fun d => (d.bank, d.width, d.address.val))) =
      [some (dest 0), some (dest 1), some (dest 2), some (dest 3)] := by
  choose accesses loweredEq tripleEq using lowered
  have hcycle := prepareParsedIntegerALUExprCycles_destination_map files oldSlots
    initialOutputSlots expression control hasSingleLineMask noForward reduced name precision
    unsigned arg opShape accesses loweredEq writes slots h
  rw [List.map_optionMap_destination]
  rw [hcycle]
  simp only [List.map_cons, List.map_nil, Option.map_some, tripleEq]

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
