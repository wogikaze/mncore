import ProofsLean.WelcomePublicSpec
import ProofsLean.FloatRelu

/-! # `4.relu-grad` — specification, the three-line answer, and the lower-bound gap

`problems/4.relu-grad` asks for `C = 1.0` where `A >= 0` and `C = -0.0` where
`A < 0`, on `16` float words per PE.  The judge-accepted answer is three issue
lines:

```
imm ui"0x3F800000" $t
frelu $lm0v $aluf $ln0v
frelu $lm8v $t $ln8v
```

This module fixes the formal object:

* `reluGradSpec` — the PE-0 half of the public specification.  PE 0 alone is a
  *weaker* postcondition than the official 256-PE readout, hence a lower bound
  for it is a lower bound for the official specification (a stronger statement
  about a larger set of correct programs).
* `reluGradAnswer` — the three lines, with the exact `ParsedOperand` shapes of
  the answer (`$t` is the parser's width-4 T operand, `$ln0v`/`$ln8v` are
  width-2 regions `[0,2,4,6]` / `[8,10,12,14]`).
* `reluGradAnswer_score = 3` and the three line-level issue checks.
* Two model-gap lemmas: two `relu` expressions in one line are rejected by the
  issue checker, and so are an `imm` and a `relu` in one line.  Together they
  rule out the only syntactic shape that could write 16 words in one line.
* `ReluGradLineExecResidual` — the two remaining obligations: the executor
  link for the three-line answer (`answer`), and the refutation of every
  one-line and two-line program (`oneLine`, `twoLine`).  The fields are
  sufficient for `LowerBound 3`; `reluGradLowerBound_three_of_residual` and
  `reluGradOptimal_of_residual` assemble the bound and `Optimal`.
* The empty program is refuted unconditionally (`reluGrad_empty_not_correct`),
  so only the one- and two-line cases remain in the residual.

The three-line answer's value chain is already proved at the abstract level in
`FloatRelu.gradAnswer` / `twoLineGradResult`; what is missing is the connection
from `executeNormalizedLine` to those words (the relu executor link).  No
`sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-! ## 1. The input, initial state, and target -/

/-- PE 0's sixteen input floats.  The public problem broadcasts the input over
the L2B; observing one PE is the weaker specification used for the lower bound. -/
abbrev ReluGradInput := Fin 16 → BitVec 32

theorem reluGradLm0Capacity : PEMemory.Bank.lm0.capacity = 4096 := by
  simp [PEMemory.Bank.capacity]

theorem reluGradLm1Capacity : PEMemory.Bank.lm1.capacity = 4096 := by
  simp [PEMemory.Bank.capacity]

theorem reluGradLm0Index (word : Fin 16) : word.val < PEMemory.Bank.lm0.capacity := by
  rw [reluGradLm0Capacity]
  omega

theorem reluGradLm1Index (index : Fin 16) : index.val < PEMemory.Bank.lm1.capacity := by
  rw [reluGradLm1Capacity]
  omega

/-- PE 0's initial register file: the input in LM0 words `0..15`, everything
else zero. -/
def reluGradInitialPERegisters (input : ReluGradInput) (pe : PEId) :
    IntegerRegisterFiles :=
  if pe.val = 0 then
    { zeroInitialPERegisterFiles with
      lm0 := fun address =>
        if h : address.val < 16 then input ⟨address.val, h⟩ else 0 }
  else zeroInitialPERegisterFiles

/-- The sealed whole-machine initial state. -/
def reluGradInitialState (input : ReluGradInput) : State :=
  { rustSimulatorInitialState with peRegisters := reluGradInitialPERegisters input }

theorem reluGradInitialState_peRegisters (input : ReluGradInput) (pe : PEId) :
    (reluGradInitialState input).peRegisters pe = reluGradInitialPERegisters input pe :=
  rfl

theorem reluGradInitialState_lm1_zero (input : ReluGradInput) (pe : PEId)
    (address : Fin PEMemory.Bank.lm1.capacity) :
    ((reluGradInitialState input).peRegisters pe).lm1 address = 0 := by
  rw [reluGradInitialState_peRegisters]
  unfold reluGradInitialPERegisters
  split <;> simp [zeroInitialPERegisterFiles]

theorem reluGradInitialState_t_zero (input : ReluGradInput) (pe : PEId)
    (address : Fin PEMemory.Bank.t.capacity) :
    ((reluGradInitialState input).peRegisters pe).t address = 0 := by
  rw [reluGradInitialState_peRegisters]
  unfold reluGradInitialPERegisters
  split <;> simp [zeroInitialPERegisterFiles]

theorem reluGradInitialState_lm0 (input : ReluGradInput) (word : Fin 16) :
    ((reluGradInitialState input).peRegisters 0).lm0
      ⟨word.val, reluGradLm0Index word⟩ = input word := by
  rw [reluGradInitialState_peRegisters]
  simp [reluGradInitialPERegisters, zeroInitialPERegisterFiles, dif_pos word.isLt]

/-- The exact value the model's `frelu` produces. -/
def reluGradTarget (input : ReluGradInput) (index : Fin 16) : BitVec 32 :=
  FloatRelu.relu (input index) 0x3F800000

/-- The sealed value model, exactly as `welcomeSealedMachine`. -/
noncomputable def reluGradSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := ReluGradInput
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- PE 0's LM1 words `0..15` must be the ReLU-grad value. -/
noncomputable def reluGradSpec : ProofsLean.Problem reluGradSealedMachine where
  admissible := fun _ => True
  initial := reluGradInitialState
  post := fun input state => ∀ index : Fin 16,
    (state.peRegisters 0).lm1
      ⟨index.val, reluGradLm1Index index⟩ =
      reluGradTarget input index

theorem reluGradSpec_initial (input : ReluGradInput) :
    reluGradSpec.initial input = reluGradInitialState input := rfl

theorem reluGradSpec_admissible (input : ReluGradInput) :
    reluGradSpec.admissible input := trivial

def reluGradZeroInput : ReluGradInput := fun _ => 0

/-- At the all-zero input every target word is `1.0`. -/
theorem reluGradTarget_zero (index : Fin 16) :
    reluGradTarget reluGradZeroInput index = 0x3F800000 := by
  unfold reluGradTarget reluGradZeroInput FloatRelu.relu FloatRelu.negativeZero
  decide


/-! ## 2. The three-line answer -/

/-- The answer's operand shapes: `$lm0v` / `$ln0v` / `$ln8v` are width-2
regions stepping by two long words (four cycles at `base, base+2, base+4,
base+6`), matching the judge's readout at long addresses `0,2,...,14`. -/
def reluGradLongRegion (base : Nat) : Region :=
  ⟨2, base, base + 2, base + 4, base + 6, false, none⟩

def reluGradLm0 (base : Nat) : ParsedOperand :=
  .mem ⟨.lm0, reluGradLongRegion base⟩ false false false none

def reluGradLm1 (base : Nat) : ParsedOperand :=
  .mem ⟨.lm1, reluGradLongRegion base⟩ false false false none

/-- `$t` has the parser's width-4 region at address `0` (the scalar T word is
always read/written as four words by `PEMemory.count`). -/
def reluGradT : ParsedOperand :=
  .mem ⟨.t, ⟨4, 0, 0, 0, 0, false, none⟩⟩ false false false none

/-- `$aluf`: the ALU forwarding read. -/
def reluGradAluf : ParsedOperand := .forward .aluf false false false

/-- `imm ui"0x3F800000" $t`. -/
def reluGradImmParsed : ParsedExpr :=
  ⟨.immediate 0x3F800000 false, [], [reluGradT], none, ""⟩

/-- `frelu $lm<base>v <second> $ln<base>v`. -/
def reluGradReluParsed (base : Nat) (second : ParsedOperand) : ParsedExpr :=
  ⟨.alu .relu (some .f) false none,
    [reluGradLm0 base, second],
    [reluGradLm1 base],
    none, ""⟩

/-- The canonical (text-erased) version used by `InstructionLine`. -/
def reluGradImmExpr : NormalizedExpr :=
  { op := .immediate 0x3F800000 false,
    sources := [],
    destinations := [reluGradT],
    flush := none }

def reluGradReluExpr (base : Nat) (second : ParsedOperand) : NormalizedExpr :=
  { op := .alu .relu (some .f) false none,
    sources := [reluGradLm0 base, second],
    destinations := [reluGradLm1 base],
    flush := none }

theorem reluGradImmExpr_toParsed :
    reluGradImmExpr.toParsed = reluGradImmParsed := rfl

theorem reluGradReluExpr_toParsed (base : Nat) (second : ParsedOperand) :
    (reluGradReluExpr base second).toParsed = reluGradReluParsed base second := rfl

/-- The judge-accepted three-line answer. -/
def reluGradAnswer : ProofsLean.Program reluGradSealedMachine :=
  [.pe [reluGradImmExpr],
   .pe [reluGradReluExpr 0 reluGradAluf],
   .pe [reluGradReluExpr 8 reluGradT]]

theorem reluGradAnswer_length : reluGradAnswer.length = 3 := rfl

theorem reluGradAnswer_score :
    ProofsLean.score reluGradSealedMachine reluGradAnswer = 3 := rfl

/-! ## 3. Line-level issue checks -/

macro "reluGrad_legal" : tactic =>
  `(tactic|
    (unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
      ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
      ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
      ParsedExpr.maskApplications ParsedOperand.writeMask?
      ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
      ParsedExpr.barWrites ParsedOperand.barWriteBank?
      ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
     simp [reluGradImmParsed, reluGradReluParsed, reluGradLm0, reluGradLm1,
       reluGradLongRegion, reluGradT, reluGradAluf,
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

theorem reluGradImmParsed_legal : LegalParsedLine [reluGradImmParsed] := by
  reluGrad_legal

theorem reluGradReluAlufParsed_legal :
    LegalParsedLine [reluGradReluParsed 0 reluGradAluf] := by
  reluGrad_legal

theorem reluGradReluTParsed_legal :
    LegalParsedLine [reluGradReluParsed 8 reluGradT] := by
  reluGrad_legal

theorem reluGradImm_check :
    checkParsedTopLine (InstructionLine.pe [reluGradImmExpr]).toParsed = true := by
  show checkParsedLine [reluGradImmExpr.toParsed] = true
  rw [reluGradImmExpr_toParsed]
  exact parsed_check_complete [reluGradImmParsed] reluGradImmParsed_legal

theorem reluGradReluAluf_check :
    checkParsedTopLine
      (InstructionLine.pe [reluGradReluExpr 0 reluGradAluf]).toParsed = true := by
  show checkParsedLine [(reluGradReluExpr 0 reluGradAluf).toParsed] = true
  rw [reluGradReluExpr_toParsed]
  exact parsed_check_complete [reluGradReluParsed 0 reluGradAluf]
    reluGradReluAlufParsed_legal

theorem reluGradReluT_check :
    checkParsedTopLine
      (InstructionLine.pe [reluGradReluExpr 8 reluGradT]).toParsed = true := by
  show checkParsedLine [(reluGradReluExpr 8 reluGradT).toParsed] = true
  rw [reluGradReluExpr_toParsed]
  exact parsed_check_complete [reluGradReluParsed 8 reluGradT]
    reluGradReluTParsed_legal


/-! ## 4. Model-gap check: one line cannot write sixteen words

The official judge (`judge/judge-py/judge.py` via `problems/run_problem.py`)
was run on the short candidates:

| candidate | result |
| --- | --- |
| one `frelu`, `$ln0v` | half the words mismatch (only 8 of 16 written) |
| one `frelu`, two destinations | `assemble3` rejects with `PEInstError` |
| `imm` + one `frelu` | words 16.. mismatch (only 8 written) |
| `imm` + `frelu` on one line, second `frelu` next line | `assemble3` rejects |
| `imm`, then two `frelu` on one line | `assemble3` rejects |

Thus the judge's minimum is three lines, matching `Top: 3`.  The two model-gap
lemmas below explain the corresponding two shapes in the Lean model.

Two `relu` expressions share the `.alu` issue group, so the issue checker
rejects them in one line.  Likewise an `imm` and a `relu` share `.alu`.  These
are the two syntactic shapes that could otherwise cover the sixteen observed
words (or supply `1.0` and eight outputs) in a single line. -/

/-- Two parsed expressions that share an issue group are rejected by the local
issue checker.  This is the `groupsUnique` component of `Legal`. -/
theorem reluGrad_checkParsedLine_pair_same_group_rejected
    (e f : ParsedExpr) (group : Group)
    (eGroup : e.issueGroup = some group) (fGroup : f.issueGroup = some group) :
    checkParsedLine [e, f] = false := by
  have notLegal : ¬ LegalParsedLine [e, f] := by
    intro legal
    have groups : groupsUnique (projectLine [e, f]) := legal.2.1
    have memoryE : e.toIssueExpr 0 ∈ projectLine [e, f] := by
      simp [projectLine, projectFrom]
    have memoryF : f.toIssueExpr 1 ∈ projectLine [e, f] := by
      simp [projectLine, projectFrom]
    have ids : (e.toIssueExpr 0).id ≠ (f.toIssueExpr 1).id := by
      simp [ParsedExpr.toIssueExpr]
    have sameGroup : (e.toIssueExpr 0).group = some group := by
      simpa [ParsedExpr.toIssueExpr] using eGroup
    have otherGroup : (f.toIssueExpr 1).group = some group := by
      simpa [ParsedExpr.toIssueExpr] using fGroup
    exact (groups (e.toIssueExpr 0) memoryE (f.toIssueExpr 1) memoryF ids group sameGroup)
      otherGroup
  cases checked : checkParsedLine [e, f] with
  | false => rfl
  | true => exact False.elim (notLegal (parsed_check_sound [e, f] checked))

/-- Two `relu` expressions in one line are rejected (both are `.alu`). -/
theorem reluGrad_two_relu_check_false :
    checkParsedTopLine
      (InstructionLine.pe
        [reluGradReluExpr 0 reluGradAluf, reluGradReluExpr 8 reluGradT]).toParsed = false := by
  show checkParsedLine
    [(reluGradReluExpr 0 reluGradAluf).toParsed,
      (reluGradReluExpr 8 reluGradT).toParsed] = false
  exact reluGrad_checkParsedLine_pair_same_group_rejected _ _ .alu rfl rfl

/-- Consequently the sixteen-word relu line fails at every state. -/
theorem reluGrad_two_relu_step_failure (state : State) :
    executeNormalizedLine
      (.pe [reluGradReluExpr 0 reluGradAluf, reluGradReluExpr 8 reluGradT]) state =
      .failure := by
  have checked : checkParsedTopLine
      (InstructionLine.pe
        [reluGradReluExpr 0 reluGradAluf, reluGradReluExpr 8 reluGradT]).toParsed = false :=
    reluGrad_two_relu_check_false
  unfold executeNormalizedLine
  simp only [NormalizedLine.toInstruction?]
  unfold executeIntegerProducerInstructionLine
  rw [checked]
  rfl

/-- An `imm` and a `relu` in one line are rejected (both are `.alu`), so the
same-line `1.0` source cannot feed the relu stage. -/
theorem reluGrad_imm_relu_check_false :
    checkParsedTopLine
      (InstructionLine.pe [reluGradImmExpr, reluGradReluExpr 0 reluGradAluf]).toParsed = false := by
  show checkParsedLine
    [reluGradImmExpr.toParsed, (reluGradReluExpr 0 reluGradAluf).toParsed] = false
  exact reluGrad_checkParsedLine_pair_same_group_rejected _ _ .alu rfl rfl

theorem reluGrad_imm_relu_step_failure (state : State) :
    executeNormalizedLine
      (.pe [reluGradImmExpr, reluGradReluExpr 0 reluGradAluf]) state = .failure := by
  have checked : checkParsedTopLine
      (InstructionLine.pe
        [reluGradImmExpr, reluGradReluExpr 0 reluGradAluf]).toParsed = false :=
    reluGrad_imm_relu_check_false
  unfold executeNormalizedLine
  simp only [NormalizedLine.toInstruction?]
  unfold executeIntegerProducerInstructionLine
  rw [checked]
  rfl

/-- The empty program is incorrect: at the all-zero input PE 0's LM1 word 0 is
still `0`, while the specification demands `1.0`. -/
theorem reluGrad_empty_not_correct :
    ¬ ProofsLean.Correct reluGradSealedMachine reluGradSpec [] := by
  intro correct
  obtain ⟨result, executed, post⟩ :=
    correct.2 reluGradZeroInput (reluGradSpec_admissible reluGradZeroInput)
  have hsome : some (reluGradSpec.initial reluGradZeroInput) = some result := by
    simpa [ProofsLean.execute] using executed
  have hinit : reluGradSpec.initial reluGradZeroInput = result := Option.some.inj hsome
  subst result
  rw [reluGradSpec_initial] at post
  have atZero := post ⟨0, by decide⟩
  rw [reluGradInitialState_lm1_zero] at atZero
  rw [reluGradTarget_zero] at atZero
  exact absurd atZero (by decide)


/-! ## 5. The residual and the reduction to `Optimal`

The lower-bound gap is exactly the refutation of every one- and two-line
program; the empty program is already refuted above.  The executor link for
the answer is kept separate so that it can be replaced by the generic `frelu`
line execution once that lands. -/

/-- The remaining obligations for `4.relu-grad`.

* `answer` — the executor link for the three-line answer.  This is the piece
  the relu executor (`executeParsedFloatReluAtPE` readback plus the 4096-PE
  walk) will supply.
* `oneLine`, `twoLine` — the lower-bound value/count argument: no single line
  and no pair of lines is correct at PE 0.  The model-gap lemmas above rule out
  the only two syntactic shapes that could cover all sixteen words in one
  line; what remains is the general per-line write bound (at most eight words
  for a `.f` relu row) and the absence of `1.0` from the initial state. -/
structure ReluGradLineExecResidual : Prop where
  answer : ProofsLean.Correct reluGradSealedMachine reluGradSpec reluGradAnswer
  oneLine : ∀ line : reluGradSealedMachine.Line,
    ¬ ProofsLean.Correct reluGradSealedMachine reluGradSpec [line]
  twoLine : ∀ first second : reluGradSealedMachine.Line,
    ¬ ProofsLean.Correct reluGradSealedMachine reluGradSpec [first, second]

/-- `LowerBound 3` from the one- and two-line refutations. -/
theorem reluGradLowerBound_three_of_residual (residual : ReluGradLineExecResidual) :
    ProofsLean.LowerBound reluGradSealedMachine reluGradSpec 3 := by
  intro p correct
  by_contra notBound
  have short : ProofsLean.score reluGradSealedMachine p < 3 := by omega
  have len : p.length ≤ ProofsLean.score reluGradSealedMachine p :=
    ProofsLean.length_le_score reluGradSealedMachine p
  rcases p with _ | ⟨line, rest⟩
  · exact reluGrad_empty_not_correct correct
  · rcases rest with _ | ⟨second, rest⟩
    · exact residual.oneLine line correct
    · rcases rest with _ | ⟨third, rest⟩
      · exact residual.twoLine line second correct
      · simp only [List.length_cons] at len
        omega

/-- `Optimal` from the residual and the answer's score. -/
theorem reluGradOptimal_of_residual (residual : ReluGradLineExecResidual) :
    ProofsLean.Optimal reluGradSealedMachine reluGradSpec reluGradAnswer := by
  refine ⟨residual.answer, ?_⟩
  rw [reluGradAnswer_score]
  exact reluGradLowerBound_three_of_residual residual

/-- The same assembly with the executor link supplied separately. -/
theorem reluGradOptimal_of_answer_and_short
    (answer : ProofsLean.Correct reluGradSealedMachine reluGradSpec reluGradAnswer)
    (oneLine : ∀ line : reluGradSealedMachine.Line,
      ¬ ProofsLean.Correct reluGradSealedMachine reluGradSpec [line])
    (twoLine : ∀ first second : reluGradSealedMachine.Line,
      ¬ ProofsLean.Correct reluGradSealedMachine reluGradSpec [first, second]) :
    ProofsLean.Optimal reluGradSealedMachine reluGradSpec reluGradAnswer :=
  reluGradOptimal_of_residual ⟨answer, oneLine, twoLine⟩

/-! Trust report: the partial module uses only the standard three axioms. -/
#print axioms reluGradAnswer_score
#print axioms reluGrad_two_relu_step_failure
#print axioms reluGrad_imm_relu_step_failure
#print axioms reluGrad_empty_not_correct
#print axioms reluGradLowerBound_three_of_residual
#print axioms reluGradOptimal_of_residual

end ProofsLean.MNCore
