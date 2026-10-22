import ProofsLean.ConvertEndianLowerBound
import ProofsLean.CendTwoLinesJoint

/-! # `12.convert-endian` — the judge-accepted three-line answer

This module names the public answer

```
imm i"0x34f80010" $r0v
ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v
sbsl $aluf $mauf $n[1,0,3,2]
```

as a `ProofsLean.Program cendSealedMachine`, proves that it is exactly the
normalization of the public answer's parsed expression groups
(`answerExpressionLines?`), that it has three unit-cost lines (score three),
and states the optimality conclusion `Optimal cendSealedMachine cendSpec
cendAnswer` from the two residuals of `CendTwoLinesJoint` **plus** the answer's
`Correct` statement.

## Status of the upper bound (read this before quoting any theorem)

`Correct cendSealedMachine cendSpec cendAnswer` is **not proved here and is not
proved anywhere in this tree**.  It is carried as an explicit hypothesis of
`cendOptimal` (`cendAnswerCorrect`).  The reason is the executor link, not the
datapath:

* the datapath of the three lines is proved (`ConvertEndian.answerDatapath`,
  `answerDatapath_is_byteSwap`, `answerProgram_parsed_second_line_readback`,
  `answerMemoryCycle_byteSwap`), but that is a *hand-written* value model
  (`ibsl`, `packedSingleFma`, `sbslWithShift`, `selector2103`), not a reduction
  of `executeNormalizedLine`;
* `Correct` needs the *whole-machine* value transition
  `executeNormalizedLine line.toNormalizedLine` (i.e.
  `executeIntegerProducerInstructionLine`) to be symbolically executed on these
  three lines for an arbitrary input word: the issue checks, the 4096-PE walk
  (`executeIntegerProducerLineAtPEs`), the integer four-cycle preparation
  (`prepareParsedIntegerMatrixReadLineCycles`), the float-MAU stage
  (`executeParsedFloatMAUsAtPE`), the forwarding update
  (`updateSupportedPELineForwarding`) and the masked commit
  (`commitParsedMaskedWrites`) with the `[1,0,3,2]` LM1 destination selector;
* no theorem in this tree computes that transition for the answer's lines.
  `CendTwoLines.lean` records the same gap ("The official three-line answer has
  not been connected to `executeNormalizedLine` in this module, so its `Correct`
  is an explicit hypothesis"), and every `Cend*` module spends its effort on the
  converse direction (refuting one- and two-line programs).

What is proved here is therefore:

* the answer's shape and its agreement with the repository's own restricted
  parser (`cendAnswer_parsed`, `cendAnswerGroups_normalized`);
* the score (`cendAnswer_score : score ... = 3`);
* **the issue checker accepts all three lines**
  (`cendImmExpr_legal`, `cendParallelExpr_legal`, `cendSbslExpr_legal`, hence
  `cendImmExpr_check`, `cendParallelExpr_check`, `cendSbslExpr_check`), and all
  four pre-checks the executor runs before the PE walk
  (`cendAnswer_prechecks`: accepted, no pending wait tag, no Rust-unsupported
  ALU row, every producer supported) — so a failed execution cannot be blamed
  on the issue or wait tests;
* the optimality assembly from the two residuals plus the open `Correct`.

What is *not* proved is the PE walk, the forwarding update and the commit, i.e.
the value transition itself.  The missing statement is isolated as
`CendAnswerExecutorLink`.

## Trust report

`answerDatapath_is_byteSwap` (and everything built on it:
`answerProgram_eq_answerDatapath`, `answerProgram_parsed_second_line_readback`,
`answerMemoryCycle_readback`, `answerMemoryCycle_byteSwap`,
`answerDatapath_involutive`, `abstractConvertEndian_is_byteSwap`) depends on the
native axiom `ConvertEndian.answerDatapath_is_byteSwap._native.bv_decide.ax_1_5`.
`integerAlu_ibsl_matches` / `integerAlu_sbsl_matches` carry their own native
`bv_decide` axioms.  The axiom-free replacements in `ByteSwapKernel.lean`
(`byteSwap64_involutive_kernel`, `byteSwap64_injective_kernel`) are **not**
sufficient here: they only replace the `byteSwap64` facts, not the datapath
identity.  The optimality assembly below (`cendOptimal_of_commitShape`,
`cendLowerBound_three_of_commitShape`) is itself native-axiom-free.

Nothing in *this* module uses the datapath identity or any `bv_decide` lemma:
`cendAnswer_parsed`, the legality/acceptance theorems, the score and the
conditional `cendOptimal` all have the trust closure
`{propext, Classical.choice, Quot.sound}` only (see the `#print axioms` block at
the end of the file).  A future proof of `CendAnswerExecutorLink` will need the
byte-swap identity at the end; if it closes that step with
`answerDatapath_is_byteSwap`, the resulting `Correct` (and every `Optimal`
built on it) will inherit
`ConvertEndian.answerDatapath_is_byteSwap._native.bv_decide.ax_1_5`.  To avoid
that, the final identity has to be re-proved structurally against
`ByteSwapKernel.byteSwap64Kernel` (the kernel lemmas alone replace only the
`byteSwap64` side, not `answerDatapath`).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory
open ProofsLean.MNCore.ConvertEndian

/-! ## 1. The three answer lines

The operands are the exact `ParsedOperand` values produced by the repository's
operand parser (`ConvertEndian.answer_operands_parse`):

* `$r0v`  — GRF0 word 0 (region `[0,1,2,3]`),
* `$r8v`  — GRF0 word 8 (region `[8,9,10,11]`),
* `$m0v`  — LM0 word 0 (region `[0,1,2,3]`),
* `$s0v`  — GRF1 word 0 (region `[0,1,2,3]`),
* `$n[1,0,3,2]` — LM1 word with the permuted region `[1,0,3,2]`,
* `$aluf`, `$mauf` — the ALU / MAU forwarding reads. -/

/-- `$r0v`: GRF0 word 0. -/
def cendR0 : ParsedOperand :=
  .mem ⟨.grf0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none

/-- `$r8v`: GRF0 word 8. -/
def cendR8 : ParsedOperand :=
  .mem ⟨.grf0, ⟨1, 8, 9, 10, 11, false, none⟩⟩ false false false none

/-- `$m0v`: LM0 word 0. -/
def cendM0 : ParsedOperand :=
  .mem ⟨.lm0, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none

/-- `$s0v`: GRF1 word 0. -/
def cendS0 : ParsedOperand :=
  .mem ⟨.grf1, ⟨1, 0, 1, 2, 3, false, none⟩⟩ false false false none

/-- `$n[1,0,3,2]`: LM1 word with the permuted destination region. -/
def cendN2103 : ParsedOperand :=
  .mem ⟨.lm1, ⟨1, 1, 0, 3, 2, false, none⟩⟩ false false false none

/-- `$aluf`: the ALU forwarding read. -/
def cendAluf : ParsedOperand := .forward .aluf false false false

/-- `$mauf`: the MAU forwarding read. -/
def cendMauf : ParsedOperand := .forward .mauf false false false

/-- `imm i"0x34f80010" $r0v`. -/
def cendImmExpr : ParsedExpr :=
  ⟨.immediate 0x34F80010 false, [], [cendR0], none, "imm i\"0x34f80010\" $r0v"⟩

/-- `ibsl $m0v $aluf $r8v` (word-precision rotate-left by the forwarded
immediate bus). -/
def cendIbslExpr : ParsedExpr :=
  ⟨.alu .bsl (some .i) false none, [cendM0, cendAluf], [cendR8], none,
    "ibsl $m0v $aluf $r8v"⟩

/-- `fvfma $aluf $aluf $aluf $s0v` (single-precision FMA of the forwarded bus
with itself three times). -/
def cendFmaExpr : ParsedExpr :=
  ⟨.mau .f false .fma none false, [cendAluf, cendAluf, cendAluf], [cendS0], none,
    "fvfma $aluf $aluf $aluf $s0v"⟩

/-- `sbsl $aluf $mauf $n[1,0,3,2]` (half-precision rotate-left by the forwarded
MAU bus, permuted LM1 destination). -/
def cendSbslExpr : ParsedExpr :=
  ⟨.alu .bsl (some .s) false none, [cendAluf, cendMauf], [cendN2103], none,
    "sbsl $aluf $mauf $n[1,0,3,2]"⟩

/-- The parsed expression groups of the answer, line by line.  The middle line
carries two expressions (the parallel issue). -/
def cendAnswerParsedGroups : List (List ParsedExpr) :=
  [[cendImmExpr], [cendIbslExpr, cendFmaExpr], [cendSbslExpr]]

/-- The normalized expression groups of the answer. -/
def cendAnswerGroups : List (List NormalizedExpr) :=
  [[cendImmExpr.normalize], [cendIbslExpr.normalize, cendFmaExpr.normalize],
    [cendSbslExpr.normalize]]

/-- **The answer program**: the three issue lines of the judge-accepted
`12.convert-endian` answer. -/
def cendAnswer : ProofsLean.Program cendSealedMachine :=
  [.pe [cendImmExpr.normalize],
   .pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
   .pe [cendSbslExpr.normalize]]

/-! ## 2. The answer is the parsed public answer

`ConvertEndian.answerExpressionLines?` is the repository's own restricted
parser for the public three-line answer.  It returns exactly the expression
groups above, and normalization lands on `cendAnswerGroups`. -/

/-- The repository parser's result for the answer is the group list above. -/
theorem cendAnswer_parsed : answerExpressionLines? = some cendAnswerParsedGroups := by
  decide

/-- Normalizing the parsed groups gives the normalized groups of the answer. -/
theorem cendAnswerGroups_normalized :
    (answerExpressionLines?).map
        (List.map (List.map (fun expression : ParsedExpr => expression.normalize))) =
      some cendAnswerGroups := by
  rw [cendAnswer_parsed]
  rfl

/-- The parsed groups have the expected line shapes `[1, 2, 1]`. -/
theorem cendAnswerParsedGroups_shapes :
    cendAnswerParsedGroups.map List.length = [1, 2, 1] := rfl

/-- The answer is the normalization of the parsed public answer, line by line. -/
theorem cendAnswer_eq_normalized :
    cendAnswer =
      (cendAnswerGroups.map fun group => InstructionLine.pe group) := by
  rfl

/-! ## 2b. The three lines pass the issue checker

The sealed step is `executeNormalizedLine`, which first runs
`checkParsedTopLine`.  A line that fails the checker can never take a step, so
acceptance is a prerequisite for `Correct`.  It is proved here for all three
answer lines by unfolding the concrete `Legal` conjunction. -/

/-- Unfold the concrete legality conjunction of a `12.convert-endian` answer
line and discharge it by evaluation.  Same shape as
`PlusTwoLowerBound.plusTwoLine1_check`. -/
macro "cend_legal" : tactic =>
  `(tactic|
    (unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
      ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
      ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
      ParsedExpr.maskApplications ParsedOperand.writeMask?
      ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
      ParsedExpr.barWrites ParsedOperand.barWriteBank?
      ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
     simp [cendR0, cendR8, cendM0, cendS0, cendN2103, cendAluf, cendMauf,
       cendImmExpr, cendIbslExpr, cendFmaExpr, cendSbslExpr,
       ParsedExpr.toIssueExpr, List.filterMap, List.map, List.filter,
       ParsedOperand.matrixUseCount, ParsedOperand.accesses,
       ParsedOperand.writeMask?, ParsedOperand.maskRegisterWrite?,
       ParsedOperand.barWriteBank?, ParsedExpr.issueGroup, ParsedExpr.issueMau,
       ParsedExpr.hasTurnaround, ParsedExpr.maskApplications,
       ParsedExpr.maskRegisterWrites, ParsedExpr.barWrites, ParsedExpr.writesLbf,
       ParsedExpr.nowriteOutputValid, Legal, idsUnique, groupsUnique,
       mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
       matrixRegistersUnique, writesUnique, Expr.writeBanks, barWritesExcludeReads,
       readsAgree, localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique,
       maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique,
       maskRegisterWritesUnique, projectFrom]))

/-- `imm i"0x34f80010" $r0v` is a legal issue line. -/
theorem cendImmExpr_legal : LegalParsedLine [cendImmExpr] := by cend_legal

/-- `ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v` is a legal parallel
issue line (one integer ALU row and one float MAU row). -/
theorem cendParallelExpr_legal :
    LegalParsedLine [cendIbslExpr, cendFmaExpr] := by cend_legal

/-- `sbsl $aluf $mauf $n[1,0,3,2]` is a legal issue line. -/
theorem cendSbslExpr_legal : LegalParsedLine [cendSbslExpr] := by cend_legal

/-- Acceptance of a normalized line from the legality of its parsed form. -/
theorem check_of_legal (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) :
    checkParsedLine (expressions.map (fun expression => expression.normalize.toParsed)) = true := by
  rw [Issue.parsed_check_unchanged_by_normalization]
  exact Issue.parsed_check_complete expressions legal

theorem cendImmExpr_check :
    checkParsedTopLine (InstructionLine.pe [cendImmExpr.normalize]).toParsed = true := by
  show checkParsedLine [cendImmExpr.normalize.toParsed] = true
  simpa using check_of_legal [cendImmExpr] cendImmExpr_legal

theorem cendParallelExpr_check :
    checkParsedTopLine
      (InstructionLine.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]).toParsed = true := by
  show checkParsedLine
    [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] = true
  simpa using check_of_legal [cendIbslExpr, cendFmaExpr] cendParallelExpr_legal

theorem cendSbslExpr_check :
    checkParsedTopLine (InstructionLine.pe [cendSbslExpr.normalize]).toParsed = true := by
  show checkParsedLine [cendSbslExpr.normalize.toParsed] = true
  simpa using check_of_legal [cendSbslExpr] cendSbslExpr_legal

/-- No answer expression carries a wait tag, so the wait pre-check of the
executor is `false` at every state. -/
theorem cendImmExpr_waitPending (state : State) :
    parsedExprWaitPending state cendImmExpr = false := by
  unfold parsedExprWaitPending
  simp [cendImmExpr, parsedExprWaitTag?]

theorem cendIbslExpr_waitPending (state : State) :
    parsedExprWaitPending state cendIbslExpr = false := by
  unfold parsedExprWaitPending
  simp [cendIbslExpr, parsedExprWaitTag?]

theorem cendFmaExpr_waitPending (state : State) :
    parsedExprWaitPending state cendFmaExpr = false := by
  unfold parsedExprWaitPending
  simp [cendFmaExpr, parsedExprWaitTag?]

theorem cendSbslExpr_waitPending (state : State) :
    parsedExprWaitPending state cendSbslExpr = false := by
  unfold parsedExprWaitPending
  simp [cendSbslExpr, parsedExprWaitTag?]

/-- The same fact in the exact form the executor sees it (normalized line:
`NormalizedExpr.toParsed` erases the source text but not the operator). -/
theorem cendNormalized_waitPending (state : State) (expression : ParsedExpr)
    (noTag : parsedExprWaitTag? expression = none) :
    parsedExprWaitPending state expression.normalize.toParsed = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op <;>
    simp_all [NormalizedExpr.toParsed, ParsedExpr.normalize, parsedExprWaitPending,
      parsedExprWaitTag?]

theorem cendImmExpr_waitTag : parsedExprWaitTag? cendImmExpr = none := by
  simp [cendImmExpr, parsedExprWaitTag?]

theorem cendIbslExpr_waitTag : parsedExprWaitTag? cendIbslExpr = none := by
  simp [cendIbslExpr, parsedExprWaitTag?]

theorem cendFmaExpr_waitTag : parsedExprWaitTag? cendFmaExpr = none := by
  simp [cendFmaExpr, parsedExprWaitTag?]

theorem cendSbslExpr_waitTag : parsedExprWaitTag? cendSbslExpr = none := by
  simp [cendSbslExpr, parsedExprWaitTag?]

theorem cendImmExprNormalized_waitPending (state : State) :
    parsedExprWaitPending state cendImmExpr.normalize.toParsed = false :=
  cendNormalized_waitPending state cendImmExpr cendImmExpr_waitTag

theorem cendIbslExprNormalized_waitPending (state : State) :
    parsedExprWaitPending state cendIbslExpr.normalize.toParsed = false :=
  cendNormalized_waitPending state cendIbslExpr cendIbslExpr_waitTag

theorem cendFmaExprNormalized_waitPending (state : State) :
    parsedExprWaitPending state cendFmaExpr.normalize.toParsed = false :=
  cendNormalized_waitPending state cendFmaExpr cendFmaExpr_waitTag

theorem cendSbslExprNormalized_waitPending (state : State) :
    parsedExprWaitPending state cendSbslExpr.normalize.toParsed = false :=
  cendNormalized_waitPending state cendSbslExpr cendSbslExpr_waitTag

theorem cendParallelNormalized_waitPending (state : State) :
    ([cendIbslExpr.normalize, cendFmaExpr.normalize].map NormalizedExpr.toParsed).any
        (parsedExprWaitPending state) = false := by
  simp [cendIbslExprNormalized_waitPending, cendFmaExprNormalized_waitPending]

/-- **The four pre-checks of `executeIntegerProducerInstructionLine` all pass**
for each answer line: accepted issue line, no pending wait tag, no
Rust-unsupported ALU row, every producer supported.  These are the tests the
executor runs before it walks the PEs, so a future executor-link proof only has
to deal with the walk, the forwarding update and the commit. -/
theorem cendAnswer_prechecks (input : BitVec 64) :
    checkParsedTopLine (InstructionLine.pe [cendImmExpr.normalize]).toParsed = true ∧
    ([cendImmExpr.normalize].map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (cendInitialState input)) = false ∧
    ([cendImmExpr.normalize].map NormalizedExpr.toParsed).any
        parsedExprIsUnsupportedRustAlu = false ∧
    ([cendImmExpr.normalize].map NormalizedExpr.toParsed).all
        parsedExprIsSupportedPELineProducer = true ∧
    checkParsedTopLine
        (InstructionLine.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]).toParsed = true ∧
    ([cendIbslExpr.normalize, cendFmaExpr.normalize].map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (cendInitialState input)) = false ∧
    ([cendIbslExpr.normalize, cendFmaExpr.normalize].map NormalizedExpr.toParsed).any
        parsedExprIsUnsupportedRustAlu = false ∧
    ([cendIbslExpr.normalize, cendFmaExpr.normalize].map NormalizedExpr.toParsed).all
        parsedExprIsSupportedPELineProducer = true ∧
    checkParsedTopLine (InstructionLine.pe [cendSbslExpr.normalize]).toParsed = true ∧
    ([cendSbslExpr.normalize].map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (cendInitialState input)) = false ∧
    ([cendSbslExpr.normalize].map NormalizedExpr.toParsed).any
        parsedExprIsUnsupportedRustAlu = false ∧
    ([cendSbslExpr.normalize].map NormalizedExpr.toParsed).all
        parsedExprIsSupportedPELineProducer = true := by
  refine ⟨cendImmExpr_check, ?_, ?_, ?_, cendParallelExpr_check, ?_, ?_, ?_,
    cendSbslExpr_check, ?_, ?_, ?_⟩
  · simpa [cendImmExpr] using cendImmExprNormalized_waitPending (cendInitialState input)
  · decide
  · decide
  · simpa [cendIbslExpr, cendFmaExpr] using
      cendParallelNormalized_waitPending (cendInitialState input)
  · decide
  · decide
  · simpa [cendSbslExpr] using cendSbslExprNormalized_waitPending (cendInitialState input)
  · decide
  · decide

/-! ## 3. Score

The answer has three lines, each of cost one, so its score is three.  This is
`CendTwoLines.cendAnswer_score_three` at the concrete answer. -/

theorem cendAnswer_length : cendAnswer.length = 3 := rfl

theorem cendAnswer_unitCost :
    ∀ line ∈ cendAnswer, InstructionLine.cost line = 1 := by
  intro line member
  have shape : line = .pe [cendImmExpr.normalize] ∨
      line = .pe [cendIbslExpr.normalize, cendFmaExpr.normalize] ∨
      line = .pe [cendSbslExpr.normalize] := by
    rcases List.mem_cons.mp member with head | rest
    · exact Or.inl head
    rcases List.mem_cons.mp rest with second | rest
    · exact Or.inr (Or.inl second)
    rcases List.mem_cons.mp rest with third | empty
    · exact Or.inr (Or.inr third)
    · simp at empty
  rcases shape with rfl | rfl | rfl <;> rfl

/-- **The official answer scores three.** -/
theorem cendAnswer_score : ProofsLean.score cendSealedMachine cendAnswer = 3 :=
  cendAnswer_score_three cendAnswer cendAnswer_length cendAnswer_unitCost

/-! ## 4. The missing upper bound

`Correct cendSealedMachine cendSpec cendAnswer` is the whole-machine statement
that the three steps succeed for every input and that the observed LM1 long
word `0` is `byteSwap64 input`.  It is *not* proved in this tree: see the module
header.  It is isolated here so that (a) it is a named obligation rather than an
anonymous hypothesis, and (b) every theorem below records it explicitly. -/

/-- **The open upper bound.**  The three-line answer is correct on the sealed
whole-machine value model.  This is the statement that still has to be proved by
symbolically executing `executeNormalizedLine` on the three lines; nothing in
this module (or in the tree) establishes it. -/
def CendAnswerExecutorLink : Prop :=
  ProofsLean.Correct cendSealedMachine cendSpec cendAnswer

/-- `cendOptimal` from the two lower-bound residuals and the (open) correctness
of the answer.  The commit-shape residual `CendTwoLineCommitShape` and the
one-line residual `CendPELinesRefuted` stay hypotheses, as does
`cendAnswerCorrect`. -/
theorem cendOptimal (cendAnswerCorrect : ProofsLean.Correct cendSealedMachine
      cendSpec cendAnswer)
    (peLines : CendPELinesRefuted) (shape : CendTwoLineCommitShape) :
    ProofsLean.Optimal cendSealedMachine cendSpec cendAnswer :=
  cendOptimal_of_commitShape peLines shape cendAnswer cendAnswerCorrect
    cendAnswer_length cendAnswer_unitCost

/-- The same assembly with the open obligation named: from
`CendAnswerExecutorLink` (and the two residuals) the answer is optimal. -/
theorem cendOptimal_of_executorLink (link : CendAnswerExecutorLink)
    (peLines : CendPELinesRefuted) (shape : CendTwoLineCommitShape) :
    ProofsLean.Optimal cendSealedMachine cendSpec cendAnswer :=
  cendOptimal link peLines shape

/-- The lower bound at three, unconditionally in the answer: the answer's
optimality reduces to its correctness plus the two residuals. -/
theorem cendAnswer_optimal_iff (peLines : CendPELinesRefuted)
    (shape : CendTwoLineCommitShape) :
    CendAnswerExecutorLink → ProofsLean.Optimal cendSealedMachine cendSpec cendAnswer :=
  fun link => cendOptimal_of_executorLink link peLines shape

/-! ## 5. Trust report -/

#print axioms cendImmExpr_legal
#print axioms cendParallelExpr_legal
#print axioms cendSbslExpr_legal
#print axioms cendImmExpr_check
#print axioms cendParallelExpr_check
#print axioms cendSbslExpr_check
#print axioms cendImmExpr_waitPending
#print axioms cendAnswer_prechecks
#print axioms cendAnswer_parsed
#print axioms cendAnswerGroups_normalized
#print axioms cendAnswerParsedGroups_shapes
#print axioms cendAnswer_eq_normalized
#print axioms cendAnswer_length
#print axioms cendAnswer_unitCost
#print axioms cendAnswer_score
#print axioms cendOptimal
#print axioms cendOptimal_of_executorLink
#print axioms cendAnswer_optimal_iff

end ProofsLean.MNCore
