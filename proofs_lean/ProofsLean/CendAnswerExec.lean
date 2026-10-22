import ProofsLean.LineExec
import ProofsLean.CendAnswerCorrect

/-! # `12.convert-endian` — executing the three-line answer

This module connects the judge-accepted three-line answer
(`CendAnswerCorrect.cendAnswer`)

```
imm i"0x34f80010" $r0v
ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v
sbsl $aluf $mauf $n[1,0,3,2]
```

to the line-execution algebra of `ProofsLean.LineExec`.

## What is closed here

* **The singleton-fold residual is closed.**
  `prepareParsedIntegerMatrixReadLineExpressions_singleton`: if the row
  `expression` prepares `(writes, slots, bars)` at the initial slot function,
  then the integer stage's fold over the singleton stage list — which starts
  from the same slots with empty write / bar accumulators — returns exactly
  that triple.  (`prepareParsedIntegerMatrixReadLineCycles_singleton` is the
  line-level form.)  The proof is `simp only
  [prepareParsedIntegerMatrixReadLineExpressions]` followed by `rw [prepared]`;
  no `match`-discriminant rewrite is needed because the fold's recursion
  equation reduces on the cons cell syntactically.

* **The hypothesis of `LineExec.executeNormalizedLine_immediate_aluf_read` is
  discharged for the answer's first line.**  `cendImm_lowered`,
  `cendImm_prepared` and `cendImm_rowExpression` compute the row's constant
  lowering, its prepared writes and its four-cycle ALU preparation;
  `cendImm_lineCycles` then produces the *line-level* preparation equation that
  the two-line specialisation used to assume.  `cendLine1_aluf` /
  `cendLine1_aluf_value` are the resulting unconditional statements: after
  line 1, every `.alu` forwarding slot at PE 0 is
  `⟨0x34F80010 ++ 0x34F80010, 0x34F80010 ++ 0x34F80010⟩` and the next line's
  `$aluf` read returns it.

* **Line 1's integer stage is computed exactly.**
  `cendImmWrites` is the explicit write list
  `[immWrite 0, aluWrite, immWrite 1, aluWrite, immWrite 2, aluWrite,
    immWrite 3, aluWrite]`: one GRF0 word write per cycle (word `cycle`,
  data `0x34F80010` in all four words, fully enabled selection
  `⟨allOnes, true⟩`) and one `$aluf` write per cycle.  `cendImm_lowered` /
  `cendImm_prepared` prove the per-cycle lowering and preparation *without*
  hypotheses (`toDirectMaskedConstantWrites?` reduces to the literal target and
  `prepareParsedMaskedConstantWrites` to the literal write).

* **Line 1's preparation is PE-independent.**
  `cendImm_destination_any` (the address of `$r0v` is GRF0 word `cycle` for
  *every* PE, BAR and T), `cendImm_selection_any`, `cendImm_lowered_any`,
  `cendImm_prepared_any`, `cendImm_aluCycles_any` and
  `cendImm_lineCycles_any`: the whole four-cycle integer preparation of line 1
  is the same at every one of the 4096 PEs.

* **The optimality assembly.**  `CendAnswerExecResidual` names exactly the two
  remaining computations; `cendAnswerCorrect_of_residual` turns it into
  `Correct cendSealedMachine cendSpec cendAnswer`,
  `cendAnswerExecutorLink_of_residual` into `CendAnswerExecutorLink`, and
  `cendOptimal_of_residual` into `Optimal cendSealedMachine cendSpec
  cendAnswer` given the two lower-bound shapes (`CendPELinesRefuted`,
  `CendTwoLineCommitShape`).

## What remains (the exact residuals)

`CendAnswerExecResidual` has two fields:

* `line1`: line 1's step *succeeds* at the initial state.  Its forwarding slots
  are proved (`cendLine1_aluf`), its integer preparation is proved at every PE
  (`cendImm_lineCycles_any`), and **each PE's core step is proved**
  (`cendImm_pecore`): from
  `state.peRegisters pe = cendInitialPERegisters input`,
  `state.forwardingValid pe _ _ = false` and
  `state.maskDirective = rustSimulatorInitialState.maskDirective`, the core step
  at `pe` succeeds and installs
  `commitParsedMaskedWrites (cendInitialPERegisters input) cendImmWrites` in
  `next.peRegisters pe`.  What is still missing is the 4096-PE walk induction:
  `executeIntegerProducerLineAtPE` adds only the BAR-writer test (false here,
  `cendImm` writes no BAR), and the step rewrites only the visited PE's
  `peRegisters`, `forwarding`, `forwardingValid` and `peContext`, so the
  invariant "every unvisited PE has the initial files, invalid forwarding and
  the linear-index context" survives; chaining it over
  `List.finRange 4096` (with `List.nodup_finRange`) and then through
  `executeIntegerProducerInstructionLine_pe_lineExec` / the six stage
  identities gives line 1's success.

  Two concrete traps found here, worth recording:

  1. `LineExec.executeIntegerProducerLineAtPECore_peRegisters_eq` gives
     `next.peRegisters pe = commit files (intWrites ++ floatWrites)` with
     `floatWrites` *existentially quantified* and only constrained by
     `floatFiles = commit (commit files intWrites) floatWrites`.  For line 1 the
     float-MAU row filter is empty, so the float stage is the identity
     (`executeParsedFloatMAUsAtPE` with an empty filter returns
     `(currentFiles, bar0, bar1, fun _ => ⟨0,0⟩, false)`), which pins
     `floatFiles` but **not** `floatWrites`.  To get the register file after
     line 1 as the commit of `cendImmWrites` alone, the per-PE core step has to
     be re-analysed with `cases` on the two `match` scrutinees
     (`prepareParsedIntegerMatrixReadLineCycles` and
     `executeParsedFloatMAUsAtPE`) instead of going through that existential.
  2. `decide` cannot close a goal with free variables ("Expected type must not
     contain free variables"), so the PE-independent lowering must be closed by
     `simp` with `Width.words`, `Bank.capacity`, `Nat.mod_eq_of_lt`, as in
     `cendImm_destination_any`.

* `tail`: lines 2 and 3 from line 1's result.  Specifically the parallel
  `ibsl`/`fvfma` step (LM0 word read at cycle `c`, word-precision rotate-left by
  the forwarded immediate `0x34F80010` — i.e. the 32-bit halfword swap of the
  input word — into GRF0 word 8 and into the `.alu` slot, plus the
  single-precision FMA of `$aluf` with itself into the `.mau` slot, giving
  `0x34F80018 ++ 0x34F80018`), and the `sbsl` step (halfword rotate by the MAU
  bus, destination selector `[1,0,3,2]`, so LM1 word `[1,0,3,2][c]` receives
  the 32-bit byte swap of LM0 word `c`; the LM1 words 0/1 readback is then
  `byteSwap64 input`).  The final identity should use the axiom-free
  `ByteSwapKernel` lemmas; nothing here uses `answerDatapath_is_byteSwap` or
  `bv_decide`.

## Trust report

Every theorem below has the trust closure `{propext, Classical.choice,
Quot.sound}` (see the `#print axioms` block at the end): no `sorry`, no `admit`,
no `native_decide`, no `bv_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 1. The integer stage's fold over a singleton row -/

/-- **The fold over one row.**  If the row `expression` prepares
`(writes, slots, bars)` at the initial slot function, then the whole line's
integer fold — which starts from the same slots and accumulates `[]` writes and
`[]` bar updates — returns exactly that triple.

The previous attempt tried to `rw` the preparation equation inside the goal,
which fails because the fold's `match` scrutinee is a `let`-free but
`match`-bound term.  The proof below avoids that by `cases`-splitting the
scrutinee into the three constructors of `StepResult` (each closed by `simp`). -/
theorem prepareParsedIntegerMatrixReadLineExpressions_singleton
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store
      expression control hasSingleLineMask noForward reduced = .ok (writes, slots, bars)) :
    prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
      hasSingleLineMask noForward reduced [expression] [] oldSlots [] =
      .ok (writes, slots, bars) := by
  simp only [prepareParsedIntegerMatrixReadLineExpressions]
  rw [prepared]
  rfl

/-- The singleton-fold lemma in the shape the two-line specialisation needs:
the fold is the line-level `prepareParsedIntegerMatrixReadLineCycles`, and the
`hasSingleLineMask` / `noForward` flags are the ones the line computes. -/
theorem prepareParsedIntegerMatrixReadLineCycles_singleton
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store
      expression control ([expression].any parsedExprHasSingleLineWriteMask)
      ([expression].any fun item =>
        match item.op with
        | .noforward => true
        | _ => false) reduced = .ok (writes, slots, bars)) :
    prepareParsedIntegerMatrixReadLineCycles files oldSlots store [expression] control reduced =
      .ok (writes, slots, bars) := by
  unfold prepareParsedIntegerMatrixReadLineCycles
  exact prepareParsedIntegerMatrixReadLineExpressions_singleton files oldSlots store expression
    control _ _ reduced writes slots bars prepared


/-! ## 3. The concrete data of the answer lines -/

/-- The GRF0 word a cycle's `$r0v` destination writes. -/
def cendGrf0Word (cycle : Fin 4) : Fin 512 := ⟨cycle.val, by have := cycle.isLt; omega⟩

theorem cendGrf0Word_val (cycle : Fin 4) : (cendGrf0Word cycle).val = cycle.val := rfl

/-- The parsed expression of line 1: the `imm` row with an erased source text. -/
theorem cendImmParsed_eq :
    cendImmExpr.normalize.toParsed =
      (⟨.immediate 0x34F80010 false, [], [cendR0], none, ""⟩ : ParsedExpr) := rfl

/-- The access record the constant lowering builds for `$r0v`. -/
def cendImmAccesses (cycle : Fin 4) : ParsedMaskedIntegerAccesses where
  op := .immediate 0x34F80010 false
  sourceX := .memory ⟨.grf0, .word, cendGrf0Word cycle⟩ false
  sourceY := .memory ⟨.grf0, .word, cendGrf0Word cycle⟩ false
  destination := ⟨.grf0, .word, cendGrf0Word cycle⟩
  writeSelection := ⟨BitVec.allOnes 4, true⟩
  flushSelection := none
  hasRequest := ⟨.immediate 0x34F80010 false, rfl⟩

/-- The constant-target list the lowering builds for `$r0v`. -/
def cendImmTargets (cycle : Fin 4) : List ParsedConstantDestination :=
  [.memory (cendImmAccesses cycle)]

/-- The committed write of one cycle of line 1. -/
def cendImmWrite (cycle : Fin 4) : PreparedParsedMaskedWrite where
  destination := some ⟨.grf0, .word, cendGrf0Word cycle⟩
  maskUpdate := none
  data := fun _ => 0x34F80010
  selection := ⟨BitVec.allOnes 4, true⟩

/-- Access records are equal as soon as their six computational fields are:
the request-existence field is a proof. -/
theorem parsedMaskedIntegerAccesses_eq_of_fields {a b : ParsedMaskedIntegerAccesses}
    (hop : a.op = b.op) (hx : a.sourceX = b.sourceX) (hy : a.sourceY = b.sourceY)
    (hd : a.destination = b.destination) (hw : a.writeSelection = b.writeSelection)
    (hf : a.flushSelection = b.flushSelection) : a = b := by
  obtain ⟨aop, ax, ay, ad, aw, af, ah⟩ := a
  obtain ⟨bop, bx, by_, bd, bw, bf, bh⟩ := b
  simp only at hop hx hy hd hw hf
  subst hop
  subst hx
  subst hy
  subst hd
  subst hw
  subst hf
  exact congrArg (ParsedMaskedIntegerAccesses.mk aop ax ay ad aw af) (Subsingleton.elim ah bh)

/-- **A constant row with one direct memory destination lowers to that
destination.**  The lowering only has to resolve the destination address and its
write selection; the produced access record is then the constructor term below.

The destination operand is written as a `.mem` constructor so that the lowering
function's `match` on the operand reduces during the proof. -/
theorem toDirectMaskedConstantWrites?_immediate_single
    (payload : BitVec 32) (sparse : Bool) (flush : Option ParsedMask) (text : String)
    (access : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (resolved : DirectMemoryAccess) (writeSelection : PEWordSelection)
    (flushSelection : Option PEWordSelection)
    (destinationLowered : ParsedOperand.toDirectMemoryDestination?
      (.mem access negated extended rounded mask) pe cycle bar0 bar1 tWord = some resolved)
    (selectionLowered : ParsedOperand.resolveMemoryWriteSelection?
      (.mem access negated extended rounded mask) resolved.bank registers cycle directive
      hasSingleLineMask = some writeSelection)
    (flushResolved : resolveFlushSelection? flush registers cycle = some flushSelection) :
    ParsedExpr.toDirectMaskedConstantWrites?
      ⟨.immediate payload sparse, [], [.mem access negated extended rounded mask], flush, text⟩
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord =
    some [.memory
      ({ op := .immediate payload sparse
         sourceX := .memory resolved false
         sourceY := .memory resolved false
         destination := resolved
         writeSelection := writeSelection
         flushSelection := flushSelection
         hasRequest := ⟨.immediate payload sparse, rfl⟩ } : ParsedMaskedIntegerAccesses)] := by
  simp only [ParsedExpr.toDirectMaskedConstantWrites?,
    ParsedExpr.toDirectMaskedConstantDestinations?,
    ParsedExpr.toDirectMaskedConstantDestination?,
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?]
  rw [destinationLowered]
  dsimp only
  rw [selectionLowered, flushResolved]
  exact congrArg some (congrArg (fun a => [ParsedConstantDestination.memory a])
    (parsedMaskedIntegerAccesses_eq_of_fields rfl rfl rfl rfl rfl rfl))

/-- `$r0v` resolves to GRF0 word `cycle`: the region `[0,1,2,3]` with a
one-word width addresses word `cycle` of GRF0 at PE 0. -/
theorem cendImm_destination (cycle : Fin 4) :
    ParsedOperand.toDirectMemoryDestination? cendR0 (0 : Fin 4) cycle 0 0 0 =
      some ⟨.grf0, .word, cendGrf0Word cycle⟩ := by
  have bound := cycle.isLt
  rcases Nat.lt_or_ge cycle.val 1 with h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    decide
  rcases Nat.lt_or_ge cycle.val 2 with h2 | h2
  · rw [show cycle = 1 from Fin.ext (by omega)]
    decide
  rcases Nat.lt_or_ge cycle.val 3 with h3 | h3
  · rw [show cycle = 2 from Fin.ext (by omega)]
    decide
  · rw [show cycle = 3 from Fin.ext (by omega)]
    decide

/-- The initial mask directive does not select GRF0, so `$r0v`'s write is fully
enabled. -/
theorem cendImm_selection (input : BitVec 64) (cycle : Fin 4) :
    ParsedOperand.resolveMemoryWriteSelection? cendR0 .grf0
      (cendInitialPERegisters input).maskRegisters cycle
      (cendInitialState input).maskDirective false =
        some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?, cendR0, cendInitialState,
    cendInitialPERegisters, resolveMemoryDirectiveSelection?, directiveTargetsBank,
    rustSimulatorInitialState]

/-- **Line 1's row lowering, cycle by cycle.** -/
theorem cendImm_lowered (input : BitVec 64) (cycle : Fin 4) :
    ParsedExpr.toDirectMaskedConstantWrites? cendImmExpr.normalize.toParsed
      (cendInitialPERegisters input).maskRegisters
      (cendInitialState input).maskDirective false
      0 0 0 0 0 cycle 0 0 0 = some (cendImmTargets cycle) := by
  rw [cendImmParsed_eq]
  exact toDirectMaskedConstantWrites?_immediate_single 0x34F80010 false none ""
    ⟨.grf0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none
    _ _ false 0 0 0 0 0 cycle 0 0 0
    ⟨.grf0, .word, cendGrf0Word cycle⟩ ⟨BitVec.allOnes 4, true⟩ none
    (cendImm_destination cycle) (cendImm_selection input cycle) rfl

/-! ### Packing the immediate bus into the four write words -/

theorem unpackALUBus_apply_zero (bus : IntegerALU.Bus) :
    unpackALUBus bus (0 : Fin 4) = bus.high.extractLsb' 32 32 := rfl
theorem unpackALUBus_apply_one (bus : IntegerALU.Bus) :
    unpackALUBus bus (1 : Fin 4) = bus.high.extractLsb' 0 32 := rfl
theorem unpackALUBus_apply_two (bus : IntegerALU.Bus) :
    unpackALUBus bus (2 : Fin 4) = bus.low.extractLsb' 32 32 := rfl
theorem unpackALUBus_apply_three (bus : IntegerALU.Bus) :
    unpackALUBus bus (3 : Fin 4) = bus.low.extractLsb' 0 32 := rfl

/-- The immediate bus `⟨p ++ p, p ++ p⟩` unpacks to the constant word `p`. -/
theorem unpackALUBus_self (payload : BitVec 32) :
    unpackALUBus ⟨payload ++ payload, payload ++ payload⟩ = fun _ => payload := by
  funext index
  obtain ⟨v, hv⟩ := index
  have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · rw [show (⟨0, hv⟩ : Fin 4) = 0 from Fin.ext rfl, unpackALUBus_apply_zero,
      BitVec.extractLsb'_append_eq_left]
  · rw [show (⟨1, hv⟩ : Fin 4) = 1 from Fin.ext rfl, unpackALUBus_apply_one,
      BitVec.extractLsb'_append_eq_right]
  · rw [show (⟨2, hv⟩ : Fin 4) = 2 from Fin.ext rfl, unpackALUBus_apply_two,
      BitVec.extractLsb'_append_eq_left]
  · rw [show (⟨3, hv⟩ : Fin 4) = 3 from Fin.ext rfl, unpackALUBus_apply_three,
      BitVec.extractLsb'_append_eq_right]

/-- **Line 1's destination write, cycle by cycle.**  The immediate row reads its
own destination (GRF0) twice, ignores both inputs, and prepares the constant
payload for all four write words. -/
theorem cendImm_prepared (input : BitVec 64) (cycle : Fin 4) :
    prepareParsedMaskedConstantWrites (cendInitialPERegisters input) cycle
        (cendImmTargets cycle) = .ok [cendImmWrite cycle] := by
  simp only [cendImmTargets, cendImmAccesses, cendImmWrite,
    prepareParsedMaskedConstantWrites, prepareParsedConstantTarget,
    prepareParsedMaskedWrite, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest,
    parsedOutputAfterFlush, Bool.false_eq_true, ite_false]
  rw [unpackALUBus_self]

/-! ### Flags of line 1's row -/

theorem cendImm_stageInput :
    parsedExprIsIntegerMatrixReadStageInput cendImmExpr.normalize.toParsed = true := by
  rw [cendImmParsed_eq]
  decide

theorem cendImm_lineExecRow :
    parsedExprIsLineExecRow cendImmExpr.normalize.toParsed = true := by
  rw [cendImmParsed_eq]
  decide

theorem cendImm_notFloat :
    parsedExprIsSupportedFloatMAUProducer cendImmExpr.normalize.toParsed = false := by
  rw [cendImmParsed_eq]
  decide

theorem cendImm_hasNoMask :
    parsedExprHasSingleLineWriteMask cendImmExpr.normalize.toParsed = false := by
  rw [cendImmParsed_eq]
  decide

theorem cendImm_noMask :
    ([cendImmExpr.normalize.toParsed].any parsedExprHasSingleLineWriteMask) = false := by
  rw [List.any_cons, cendImm_hasNoMask]
  simp

theorem cendImm_noForward :
    ([cendImmExpr.normalize.toParsed].any (fun item =>
      match item.op with
      | .noforward => true
      | _ => false)) = false := by
  rw [cendImmParsed_eq]
  decide

/-- The mask control of line 1 at the initial state. -/
def cendControl (input : BitVec 64) : ParsedMaskExecutionControl where
  directive := (cendInitialState input).maskDirective
  context := { (ParsedIntegerContext.ofLinearIndex welcomePE) with
    bar0 := ((cendInitialState input).peContext welcomePE).bar0
    bar1 := ((cendInitialState input).peContext welcomePE).bar1
    tWord := ((cendInitialState input).peContext welcomePE).tWord }
  elapsedWords := (cendInitialState input).hazardClock

/-- The explicit write list of line 1's integer stage: one destination write and
one ALU forwarding write per cycle, in cycle order. -/
def cendImmWrites : List PreparedParsedMaskedWrite :=
  [cendImmWrite 0] ++ [immediateALUWrite 0x34F80010 false false none] ++
  [cendImmWrite 1] ++ [immediateALUWrite 0x34F80010 false false none] ++
  [cendImmWrite 2] ++ [immediateALUWrite 0x34F80010 false false none] ++
  [cendImmWrite 3] ++ [immediateALUWrite 0x34F80010 false false none]

/-- The ALU forwarding write of one `imm` cycle. -/
def cendImmALUWrite : PreparedParsedMaskedWrite :=
  immediateALUWrite 0x34F80010 false false none

/-- **Line 1's integer ALU cycles, with the explicit write list.** -/
theorem cendImm_aluCycles (input : BitVec 64) :
    prepareParsedIntegerALUExprCycles (cendInitialPERegisters input)
        (stateForwardingSlots (cendInitialState input) welcomePE)
        (stateForwardingSlots (cendInitialState input) welcomePE)
        cendImmExpr.normalize.toParsed (cendControl input) false false false =
      .ok ([cendImmWrite 0] ++ [cendImmALUWrite] ++ [cendImmWrite 1] ++ [cendImmALUWrite] ++
        [cendImmWrite 2] ++ [cendImmALUWrite] ++ [cendImmWrite 3] ++ [cendImmALUWrite],
        immediateALUSlots (stateForwardingSlots (cendInitialState input) welcomePE)
          0x34F80010 false false (fun _ => none)) := by
  let files := cendInitialPERegisters input
  let oldSlots := stateForwardingSlots (cendInitialState input) welcomePE
  let expression := cendImmExpr.normalize.toParsed
  let control := cendControl input
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s3 unit cycle
  have isImmediate : expression.op = .immediate 0x34F80010 false := by
    rw [show expression = (⟨.immediate 0x34F80010 false, [], [cendR0], none, ""⟩ : ParsedExpr)
      from cendImmParsed_eq]
  have lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some (cendImmTargets cycle) := by
    intro cycle
    show ParsedExpr.toDirectMaskedConstantWrites? expression
      (cendInitialPERegisters input).maskRegisters (cendInitialState input).maskDirective false
      0 0 0 0 0 cycle 0 0 0 = some (cendImmTargets cycle)
    rw [show expression = cendImmExpr.normalize.toParsed from rfl]
    exact cendImm_lowered input cycle
  have prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (cendImmTargets cycle)
      = .ok [cendImmWrite cycle] := fun cycle => cendImm_prepared input cycle
  have flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters
      cycle = some (none : Option PEWordSelection) := by
    intro cycle
    rw [show expression = (⟨.immediate 0x34F80010 false, [], [cendR0], none, ""⟩ : ParsedExpr)
      from cendImmParsed_eq]
    rfl
  have updated : ∀ (cycle : Fin 4) (next : ProofsLean.MNCore.Forwarding.Slots),
      updateParsedIntegerALUForwardingCycle next cycle
        (.ok cendImmALUWrite) false =
        .ok (fun unit slotCycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
            .known (pack cendImmALUWrite.data)
          else next unit slotCycle) := by
    intro cycle next
    exact updateParsedIntegerALUForwardingCycle_immediate next cycle 0x34F80010 false false none
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      false false false 0 = .ok ([cendImmWrite 0] ++ [cendImmALUWrite], s1) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      false false false 0 (cendImmTargets 0) [cendImmWrite 0] none s1 0x34F80010 false
      isImmediate (lowered 0) (prepared 0) (flushResolved 0) (updated 0 s0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      false false false 1 = .ok ([cendImmWrite 1] ++ [cendImmALUWrite], s2) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      false false false 1 (cendImmTargets 1) [cendImmWrite 1] none s2 0x34F80010 false
      isImmediate (lowered 1) (prepared 1) (flushResolved 1) (updated 1 s1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      false false false 2 = .ok ([cendImmWrite 2] ++ [cendImmALUWrite], s3) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      false false false 2 (cendImmTargets 2) [cendImmWrite 2] none s3 0x34F80010 false
      isImmediate (lowered 2) (prepared 2) (flushResolved 2) (updated 2 s2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      false false false 3 = .ok ([cendImmWrite 3] ++ [cendImmALUWrite], s4) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      false false false 3 (cendImmTargets 3) [cendImmWrite 3] none s4 0x34F80010 false
      isImmediate (lowered 3) (prepared 3) (flushResolved 3) (updated 3 s3)
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext rfl ?_
  funext unit cycle
  have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hsmall with h | h | h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite, oldSlots]
  · rw [show cycle = 1 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite, oldSlots]
  · rw [show cycle = 2 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite, oldSlots]
  · rw [show cycle = 3 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite, oldSlots]

/-! ## 4. Closing the singleton-fold residual in the two-line specialisation -/

/-- The matrix-read store of line 1 at the initial state. -/
def cendMatrixStore (input : BitVec 64) : ParsedMatrixReadStore :=
  (cendInitialState input).matrixRegisters
    (ParsedIntegerContext.ofLinearIndex welcomePE).group
    (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
    (ParsedIntegerContext.ofLinearIndex welcomePE).l1b

/-- The operator of line 1's parsed row. -/
theorem cendImm_op : cendImmExpr.normalize.toParsed.op = .immediate 0x34F80010 false := rfl

/-- **Line 1's row preparation.**  The `.immediate` row prepares its destination
writes and its four `$aluf` slots; it writes no BAR update. -/
theorem cendImm_rowExpression (input : BitVec 64) :
    prepareParsedIntegerMatrixReadLineExpression (cendInitialPERegisters input)
        (stateForwardingSlots (cendInitialState input) welcomePE)
        (stateForwardingSlots (cendInitialState input) welcomePE)
        (cendMatrixStore input) cendImmExpr.normalize.toParsed (cendControl input)
        false false false =
      .ok (cendImmWrites,
        immediateALUSlots (stateForwardingSlots (cendInitialState input) welcomePE)
          0x34F80010 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [cendImm_op]
  dsimp only
  rw [cendImm_aluCycles input]
  dsimp only
  simp only [parsedIntegerALUBarUpdates, cendImmExpr, ParsedExpr.normalize,
    NormalizedExpr.toParsed, cendR0, cendImmWrites, cendImmALUWrite]

/-- **Line 1's integer stage.**  The fold over the singleton stage list is the
row's own preparation: this is the singleton-fold residual, discharged. -/
theorem cendImm_lineCycles (input : BitVec 64) :
    prepareParsedIntegerMatrixReadLineCycles (cendInitialPERegisters input)
        (stateForwardingSlots (cendInitialState input) welcomePE) (cendMatrixStore input)
        [cendImmExpr.normalize.toParsed] (cendControl input) false =
      .ok (cendImmWrites,
        immediateALUSlots (stateForwardingSlots (cendInitialState input) welcomePE)
          0x34F80010 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [cendImm_noMask]
  exact prepareParsedIntegerMatrixReadLineExpressions_singleton
    (cendInitialPERegisters input) (stateForwardingSlots (cendInitialState input) welcomePE)
    (cendMatrixStore input) cendImmExpr.normalize.toParsed (cendControl input)
    false false false cendImmWrites
    (immediateALUSlots (stateForwardingSlots (cendInitialState input) welcomePE)
      0x34F80010 false false (fun _ => none)) []
    (cendImm_rowExpression input)

/-- **Line 1's `.alu` forwarding slots, unconditionally.**  This is
`LineExec.executeNormalizedLine_immediate_aluf_read` with its singleton-fold
hypothesis discharged by `cendImm_lineCycles`.  The next line's `$aluf` read is
computed here. -/
theorem cendLine1_aluf (input : BitVec 64) (next : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok next) :
    (∀ cycle : Fin 4,
      stateForwardingSlots next welcomePE .alu cycle = .known (pack cendImmALUWrite.data)) ∧
    (∀ cycle : Fin 4,
      ParsedIntegerInput.readWithForwarding (next.peRegisters welcomePE)
        (stateForwardingSlots next welcomePE) cycle (.forward .aluf false) =
        .ok (pack cendImmALUWrite.data)) := by
  have isImmediate : cendImmExpr.normalize.toParsed.op = .immediate 0x34F80010 false := cendImm_op
  have h := executeNormalizedLine_immediate_aluf_read cendImmExpr.normalize
    (cendInitialState input) next 0x34F80010 false isImmediate cendImmExpr_check
    (fun _ => none) cendImmWrites [] (cendImm_lineCycles input) executed
  refine ⟨?_, ?_⟩
  · intro cycle
    simpa [cendImmALUWrite] using h.1 cycle
  · intro cycle
    simpa [cendImmALUWrite] using h.2 cycle

/-! ## 5. The remaining executor link: lines 2 and 3, and line 1's success

Line 1's *forwarding slots* are computed unconditionally above
(`cendLine1_aluf`): every `.alu` cycle carries `⟨0x34F80010 ++ 0x34F80010,
0x34F80010 ++ 0x34F80010⟩`.  What is still missing is

* that line 1's step *succeeds* at every one of the 4096 PEs (the write
  preparation is PE-independent for `$r0v`, but that uniformity is not proved
  here), and
* lines 2 and 3: the `ibsl` / `fvfma` parallel step (LM0 word read, ALU
  word-precision lane rotate by the forwarded immediate, single-precision FMA
  into the MAU slot, GRF0 word 8 and GRF1 word 0 writes) and the `sbsl` step
  (halfword rotate by the forwarded MAU bus into LM1 with the `[1,0,3,2]`
  destination selector, then the LM1 words 0/1 readback = `byteSwap64 input`).

The two residuals are stated below in exactly the form the `Correct` assembly
consumes. -/

/-- **The residual executor computations.**  `line1` is line 1's success at the
initial state; `tail` is the value transition of lines 2 and 3 from line 1's
result.  Everything else in `Correct cendSealedMachine cendSpec cendAnswer` is
proved. -/
structure CendAnswerExecResidual : Prop where
  /-- Line 1 executes at the initial state. -/
  line1 : ∀ input : BitVec 64, ∃ next : State,
    executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next
  /-- Lines 2 and 3 execute and observe `byteSwap64 input`. -/
  tail : ∀ (input : BitVec 64) (s1 : State),
    executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
    ∃ result : State,
      ProofsLean.execute cendSealedMachine
        [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
         .pe [cendSbslExpr.normalize]] s1 = some result ∧
      cendOutputPair result = byteSwap64 input

/-- **`Correct` from the residual.**  Line 1's step is `some` (first residual);
the tail executes the other two lines (second residual) and the observation is
`byteSwap64`. -/
theorem cendAnswerCorrect_of_residual (residual : CendAnswerExecResidual) :
    ProofsLean.Correct cendSealedMachine cendSpec cendAnswer := by
  refine ⟨?_, ?_⟩
  · simp [cendSealedMachine]
  intro input _
  obtain ⟨s1, line1⟩ := residual.line1 input
  obtain ⟨result, tail, observed⟩ := residual.tail input s1 line1
  refine ⟨result, ?_, observed⟩
  show (cendSealedMachine.step (.pe [cendImmExpr.normalize]) (cendInitialState input)).bind
    (fun next => ProofsLean.execute cendSealedMachine
      [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize], .pe [cendSbslExpr.normalize]]
      next) = some result
  have step : cendSealedMachine.step (.pe [cendImmExpr.normalize]) (cendInitialState input) =
      some s1 := by
    simp only [cendSealedMachine, InstructionLine.toNormalizedLine, line1]
  rw [step]
  exact tail

/-- **The named open obligation is exactly the residual.** -/
theorem cendAnswerExecutorLink_of_residual (residual : CendAnswerExecResidual) :
    CendAnswerExecutorLink :=
  cendAnswerCorrect_of_residual residual

/-- **Unconditional optimality from the residual and the two lower-bound
shapes** (`CendPELinesRefuted`, `CendTwoLineCommitShape`). -/
theorem cendOptimal_of_residual (residual : CendAnswerExecResidual)
    (peLines : CendPELinesRefuted) (shape : CendTwoLineCommitShape) :
    ProofsLean.Optimal cendSealedMachine cendSpec cendAnswer :=
  cendOptimal_of_executorLink (cendAnswerExecutorLink_of_residual residual) peLines shape

/-- **The value in line 1's `.alu` slot**: the immediate bus
`⟨0x34F80010 ++ 0x34F80010, 0x34F80010 ++ 0x34F80010⟩`. -/
theorem cendImmALUWrite_value :
    pack cendImmALUWrite.data =
      (⟨(0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32),
        (0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32)⟩ : IntegerALU.Bus) := by
  simp [cendImmALUWrite, immediateALUWrite_forwarded_none]

/-- **Line 1's `.alu` slots, in value form** (the statement `Correct`'s second
line consumes). -/
theorem cendLine1_aluf_value (input : BitVec 64) (next : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok next) :
    (∀ cycle : Fin 4,
      stateForwardingSlots next welcomePE .alu cycle =
        .known (⟨(0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32),
          (0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32)⟩ : IntegerALU.Bus)) ∧
    (∀ cycle : Fin 4,
      ParsedIntegerInput.readWithForwarding (next.peRegisters welcomePE)
        (stateForwardingSlots next welcomePE) cycle (.forward .aluf false) =
        .ok (⟨(0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32),
          (0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32)⟩ : IntegerALU.Bus)) := by
  obtain ⟨slots, reads⟩ := cendLine1_aluf input next executed
  constructor
  · intro cycle
    rw [slots cycle, cendImmALUWrite_value]
  · intro cycle
    rw [reads cycle, cendImmALUWrite_value]

/-! ## 6. Trust report -/

#print axioms prepareParsedIntegerMatrixReadLineExpressions_singleton
#print axioms prepareParsedIntegerMatrixReadLineCycles_singleton
#print axioms cendImm_lowered
#print axioms cendImm_prepared
#print axioms cendImm_aluCycles
#print axioms cendImm_rowExpression
#print axioms cendImm_lineCycles
#print axioms cendLine1_aluf
#print axioms cendLine1_aluf_value
#print axioms cendAnswerCorrect_of_residual
#print axioms cendOptimal_of_residual

/-! ## 4b. PE-independence of line 1's preparation

Line 1's destination `$r0v` is a direct GRF0 word whose address is
`region[cycle] = cycle` for every PE (`madpe = none`, `tIndirect = false`), and
its write selection depends only on the (PE-independent) mask directive.  The
lowering and preparation below are therefore stated for an *arbitrary* PE,
group, MAB, BAR and T — the uniformity the 4096-PE walk needs. -/

/-- **`$r0v`'s address is PE-independent**: every PE and every BAR/T resolves it
to GRF0 word `cycle`. -/
theorem cendImm_destination_any (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryDestination? cendR0 pe cycle bar0 bar1 tWord =
      some ⟨.grf0, .word, cendGrf0Word cycle⟩ := by
  have bound := cycle.isLt
  rcases Nat.lt_or_ge cycle.val 1 with h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
      cendR0, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, cendGrf0Word,
      Width.words, Bank.capacity]
  rcases Nat.lt_or_ge cycle.val 2 with h2 | h2
  · rw [show cycle = 1 from Fin.ext (by omega)]
    simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
      cendR0, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, cendGrf0Word,
      Width.words, Bank.capacity, Nat.mod_eq_of_lt]
  rcases Nat.lt_or_ge cycle.val 3 with h3 | h3
  · rw [show cycle = 2 from Fin.ext (by omega)]
    simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
      cendR0, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, cendGrf0Word,
      Width.words, Bank.capacity, Nat.mod_eq_of_lt]
  · rw [show cycle = 3 from Fin.ext (by omega)]
    simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
      cendR0, issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, cendGrf0Word,
      Width.words, Bank.capacity, Nat.mod_eq_of_lt]

/-- `$r0v`'s write selection at the simulator's initial mask directive is fully
enabled (`GRF0` is not a mask target), for either value of the single-line mask
flag. -/
theorem cendImm_selection_any (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (cycle : Fin 4) (hasSingleLineMask : Bool) :
    ParsedOperand.resolveMemoryWriteSelection? cendR0 .grf0 registers cycle
        rustSimulatorInitialState.maskDirective hasSingleLineMask =
      some ⟨BitVec.allOnes 4, true⟩ := by
  cases hasSingleLineMask
  · simp [ParsedOperand.resolveMemoryWriteSelection?, cendR0,
      resolveMemoryDirectiveSelection?, directiveTargetsBank, rustSimulatorInitialState]
  · rfl

/-- **Line 1's lowering is PE-independent.** -/
theorem cendImm_lowered_any (files : IntegerRegisterFiles)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (directiveEq : directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    ParsedExpr.toDirectMaskedConstantWrites? cendImmExpr.normalize.toParsed
      files.maskRegisters directive hasSingleLineMask group l2b l1b mab pe cycle
      bar0 bar1 tWord = some (cendImmTargets cycle) := by
  rw [cendImmParsed_eq]
  subst directiveEq
  rw [registersEq]
  exact toDirectMaskedConstantWrites?_immediate_single 0x34F80010 false none ""
    ⟨.grf0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none
    _ _ hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
    ⟨.grf0, .word, cendGrf0Word cycle⟩ ⟨BitVec.allOnes 4, true⟩ none
    (cendImm_destination_any pe cycle bar0 bar1 tWord)
    (cendImm_selection_any zeroInitialPERegisterFiles.maskRegisters cycle
      hasSingleLineMask) rfl

/-- **Line 1's destination-write preparation is PE-independent** (it does not
even read the register file: the immediate ignores both inputs). -/
theorem cendImm_prepared_any (files : IntegerRegisterFiles) (cycle : Fin 4) :
    prepareParsedMaskedConstantWrites files cycle (cendImmTargets cycle) =
      .ok [cendImmWrite cycle] := by
  simp only [cendImmTargets, cendImmAccesses, cendImmWrite,
    prepareParsedMaskedConstantWrites, prepareParsedConstantTarget,
    prepareParsedMaskedWrite, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest,
    parsedOutputAfterFlush, Bool.false_eq_true, ite_false]
  rw [unpackALUBus_self]


/-- **Line 1's ALU cycle chain at an arbitrary PE.**  Same replay as
`cendImm_aluCycles`, with the state only entering through the mask directive and
the mask-register file. -/
theorem cendImm_aluCycles_any (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    prepareParsedIntegerALUExprCycles files oldSlots oldSlots cendImmExpr.normalize.toParsed
        control false false false =
      .ok (cendImmWrites,
        immediateALUSlots oldSlots 0x34F80010 false false (fun _ => none)) := by
  let expression := cendImmExpr.normalize.toParsed
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then
      .known (pack cendImmALUWrite.data)
    else s3 unit cycle
  have isImmediate : expression.op = .immediate 0x34F80010 false := by
    rw [show expression = (⟨.immediate 0x34F80010 false, [], [cendR0], none, ""⟩ : ParsedExpr)
      from cendImmParsed_eq]
  have lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some (cendImmTargets cycle) :=
    fun cycle => cendImm_lowered_any files control.directive false control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord directiveEq registersEq
  have prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (cendImmTargets cycle)
      = .ok [cendImmWrite cycle] := fun cycle => cendImm_prepared_any files cycle
  have flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters
      cycle = some (none : Option PEWordSelection) := by
    intro cycle
    rw [show expression = (⟨.immediate 0x34F80010 false, [], [cendR0], none, ""⟩ : ParsedExpr)
      from cendImmParsed_eq]
    rfl
  have updated : ∀ (cycle : Fin 4) (next : ProofsLean.MNCore.Forwarding.Slots),
      updateParsedIntegerALUForwardingCycle next cycle
        (.ok cendImmALUWrite) false =
        .ok (fun unit slotCycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
            .known (pack cendImmALUWrite.data)
          else next unit slotCycle) := by
    intro cycle next
    exact updateParsedIntegerALUForwardingCycle_immediate next cycle 0x34F80010 false false none
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      false false false 0 = .ok ([cendImmWrite 0] ++ [cendImmALUWrite], s1) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      false false false 0 (cendImmTargets 0) [cendImmWrite 0] none s1 0x34F80010 false
      isImmediate (lowered 0) (prepared 0) (flushResolved 0) (updated 0 s0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      false false false 1 = .ok ([cendImmWrite 1] ++ [cendImmALUWrite], s2) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      false false false 1 (cendImmTargets 1) [cendImmWrite 1] none s2 0x34F80010 false
      isImmediate (lowered 1) (prepared 1) (flushResolved 1) (updated 1 s1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      false false false 2 = .ok ([cendImmWrite 2] ++ [cendImmALUWrite], s3) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      false false false 2 (cendImmTargets 2) [cendImmWrite 2] none s3 0x34F80010 false
      isImmediate (lowered 2) (prepared 2) (flushResolved 2) (updated 2 s2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      false false false 3 = .ok ([cendImmWrite 3] ++ [cendImmALUWrite], s4) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      false false false 3 (cendImmTargets 3) [cendImmWrite 3] none s4 0x34F80010 false
      isImmediate (lowered 3) (prepared 3) (flushResolved 3) (updated 3 s3)
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext rfl ?_
  funext unit cycle
  have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hsmall with h | h | h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite]
  · rw [show cycle = 1 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite]
  · rw [show cycle = 2 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite]
  · rw [show cycle = 3 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, cendImmALUWrite]

theorem cendImm_lineCycles_any (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    prepareParsedIntegerMatrixReadLineCycles files oldSlots store
        [cendImmExpr.normalize.toParsed] control false =
      .ok (cendImmWrites, immediateALUSlots oldSlots 0x34F80010 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [cendImm_noMask]
  refine prepareParsedIntegerMatrixReadLineExpressions_singleton files oldSlots store
    cendImmExpr.normalize.toParsed control false false false cendImmWrites
    (immediateALUSlots oldSlots 0x34F80010 false false (fun _ => none)) [] ?_
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [cendImm_op]
  dsimp only
  rw [cendImm_aluCycles_any files oldSlots control directiveEq registersEq]
  dsimp only
  simp only [parsedIntegerALUBarUpdates, cendImmExpr, ParsedExpr.normalize,
    NormalizedExpr.toParsed, cendR0, cendImmWrites]

#print axioms cendImm_aluCycles_any
#print axioms cendImm_lineCycles_any
#print axioms cendImm_destination_any
#print axioms cendImm_lowered_any
#print axioms cendImm_prepared_any


/-! ## 4c. Line 1's per-PE core step

The float-MAU stage of line 1 is empty, so it is the identity; together with the
PE-independent integer preparation this makes each PE's core step succeed and
install the commit of `cendImmWrites` in that PE's register file.  The 4096-PE
walk still has to chain this over `List.finRange 4096` with the frame facts (the
step only touches the visited PE's `peRegisters`, `forwarding`,
`forwardingValid` and `peContext`). -/

theorem executeParsedFloatMAUsAtPE_empty (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (context : ParsedIntegerContext)
    (expressions : List ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (empty : expressions.filter parsedExprIsSupportedFloatMAUProducer = []) :
    executeParsedFloatMAUsAtPE readFiles currentFiles oldSlots context expressions directive
        hasSingleLineMask =
      .ok (currentFiles, context.bar0, context.bar1, (fun _ => ⟨0, 0⟩), false) := by
  unfold executeParsedFloatMAUsAtPE
  simp only [empty, List.isEmpty_nil, Bool.not_true]
  rfl

theorem cendImm_pecore (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (_validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (_ctxEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next, executeIntegerProducerLineAtPECore [cendImmExpr.normalize.toParsed] state pe =
        .ok next ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (cendInitialPERegisters input) cendImmWrites := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [show ([cendImmExpr.normalize.toParsed].filter
      parsedExprIsIntegerMatrixReadStageInput) = [cendImmExpr.normalize.toParsed] from by
    simp [cendImm_stageInput]]
  rw [directiveEq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendImm_lineCycles_any (cendInitialPERegisters input) (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    { directive := rustSimulatorInitialState.maskDirective
      context :=
        { pe := (ParsedIntegerContext.ofLinearIndex pe).pe
          cycle := (ParsedIntegerContext.ofLinearIndex pe).cycle
          bar0 := (state.peContext pe).bar0
          bar1 := (state.peContext pe).bar1
          tWord := (state.peContext pe).tWord
          group := (ParsedIntegerContext.ofLinearIndex pe).group
          l2b := (ParsedIntegerContext.ofLinearIndex pe).l2b
          l1b := (ParsedIntegerContext.ofLinearIndex pe).l1b
          mab := (ParsedIntegerContext.ofLinearIndex pe).mab }
      elapsedWords := state.hazardClock } rfl rfl]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_empty _ _ _ _ _ _ _
    (by simp [cendImm_notFloat])]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  dsimp only
  exact ⟨_, rfl, by simp⟩

#print axioms executeParsedFloatMAUsAtPE_empty
#print axioms cendImm_pecore

end ProofsLean.MNCore
