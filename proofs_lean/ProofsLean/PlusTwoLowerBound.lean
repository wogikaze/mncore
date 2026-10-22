import ProofsLean.WelcomeOptimal
import ProofsLean.WelcomeBoundTwo
import ProofsLean.WelcomeProvenance

/-! # `2.plus-two` on the sealed whole-machine value model

This module states the challenge problem `2.plus-two` (add `2` to each of the
twenty `Long` inputs) on the same sealed value model as
`ProofsLean/WelcomeOptimal.lean`.

## What is established

* `plusTwoSealedMachine`, `plusTwoSpec`, `plusTwoInitialState` — the machine,
  the universal specification (`∀ k, 0 ≤ input k ≤ 99`), and the initial state.
* `plusTwoRecordedAnswer` — the five normalized lines of
  `problems/challenge/2.plus-two/answer.vsm`.
* `plusTwoLine1_perPE_value` — the first line's **closed** per-PE computation
  on the all-zero input writes `0xFFFFFFFF` into the low word of output long 9.
  The computation is discharged by `decide`; no `native_decide` is used.
* `plusTwoLine1_step_value` — the same fact for the whole-machine step, by
  lifting the per-PE result along `List.finRange 4096` (`PE 0` is the head and
  the tail does not revisit it).
* `plusTwoRecorded_not_correct_of_suffixFrame` — if the four-line suffix
  preserves the witness word, the recorded five-line answer is **not correct**
  on the sealed machine.  The suffix-frame statement is
  `PlusTwoSuffixPreservesWitness`, a `Prop` (not an axiom): the four remaining
  lines must be shown not to write `LM1` word `19`.
* `plusTwo_execute_coverage` — counting propagation: if every line changes at
  most four of the twenty observed output words, a program of `n` lines changes
  at most `4 * n` of them.
* `plusTwoLowerBound_five_of_coverage` — from the per-line coverage obligation
  `PlusTwoLineCoverage`, `LowerBound plusTwoSealedMachine plusTwoSpec 5`.

## What is NOT proved here

The two semantic obligations are stated, not assumed:

* `PlusTwoSuffixPreservesWitness` — the destination analysis of the four
  suffix lines at an arbitrary state.  The suffix lines write `LM1` words
  `5,7,29,13`, `31,21,35,17`, `3,1,9,25`, `37,23,15,27`; none is word `19`.
  The missing step is the general "a successful line writes only its resolved
  destination regions" provenance for the plain integer-ALU cycle.
* `PlusTwoLineCoverage` — the same provenance in counting form for an
  arbitrary line, including the non-plain producer families.

## External evidence (not formalized)

The official judge accepts the recorded answer only on the official testcase:
on the all-zero input it reports twenty mismatches (every output is
`0xFFFFFFFF` instead of `2`).  A general seven-line answer
(`imm ui"0x00000002" $s449/1000; nop; ladd $lm0v $ls448 $ln0v; ...`) is
accepted on the official testcase and on all-zero, all-99 and sequential
inputs.  Those judge runs are not Lean theorems.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Input, initial state and specification -/

/-- The twenty `Long` input values, stored as the low 32-bit word of each
even `Long` slot. -/
abbrev PlusTwoWords := Fin 20 → BitVec 32

/-- The observed PE (`n0c0b0m0p0`). -/
abbrev plusTwoPE : PEId := welcomePE

/-- The LM1 long address of output `k`. -/
def plusTwoLongAddress (k : Fin 20) : Fin Bank.lm1.capacity :=
  ⟨k.val, by have := k.isLt; change k.val < 4096; omega⟩

/-- The high (upper) 32-bit word of output long `k`.  The problem writes the
outputs at word offsets `$ln0, $ln2, ..., $ln38`, so output `k` occupies the
words `2k` (high) and `2k+1` (low) of LM1. -/
def plusTwoHighAddress (k : Fin 20) : Fin Bank.lm1.capacity :=
  ⟨2 * k.val, by have := k.isLt; change 2 * k.val < 4096; omega⟩

/-- The low 32-bit word of output long `k`. -/
def plusTwoLowAddress (k : Fin 20) : Fin Bank.lm1.capacity :=
  ⟨2 * k.val + 1, by have := k.isLt; change 2 * k.val + 1 < 4096; omega⟩

/-- LM0 of the initial PE files: the `k`-th input value is the low word of the
`k`-th even `Long` slot, the high word is zero. -/
def plusTwoInitialLm0 (input : PlusTwoWords) (address : Fin Bank.lm0.capacity) :
    BitVec 32 :=
  if h : address.val % 2 = 1 ∧ address.val / 2 < 20 then
    input ⟨address.val / 2, h.2⟩
  else 0

/-- Zero-initialised PE register file carrying the twenty input longs in LM0. -/
def plusTwoInitialPERegisters (input : PlusTwoWords) : IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with lm0 := plusTwoInitialLm0 input }

/-- The initial whole-machine state of `2.plus-two`. -/
def plusTwoInitialState (input : PlusTwoWords) : State :=
  { rustSimulatorInitialState with peRegisters := fun _ => plusTwoInitialPERegisters input }

theorem plusTwoInitialState_peRegisters (input : PlusTwoWords) (pe : PEId) :
    (plusTwoInitialState input).peRegisters pe = plusTwoInitialPERegisters input := rfl

theorem plusTwoInitialState_maskDirective (input : PlusTwoWords) :
    (plusTwoInitialState input).maskDirective = welcomeMaskDirective := rfl

theorem plusTwoInitialState_context (input : PlusTwoWords) (pe : PEId) :
    (plusTwoInitialState input).peContext pe = ParsedIntegerContext.ofLinearIndex pe := rfl

theorem plusTwoInitialPERegisters_lm0_low (input : PlusTwoWords) (k : Fin 20) :
    (plusTwoInitialPERegisters input).lm0 (plusTwoLowAddress k) = input k := by
  unfold plusTwoInitialPERegisters plusTwoInitialLm0 plusTwoLowAddress
  simp only
  have hmod : (2 * k.val + 1) % 2 = 1 := by omega
  have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
  have hlt : (2 * k.val + 1) / 2 < 20 := by omega
  rw [dif_pos ⟨hmod, hlt⟩]
  simp only [hdiv]

theorem plusTwoInitialPERegisters_lm0_high (input : PlusTwoWords) (k : Fin 20) :
    (plusTwoInitialPERegisters input).lm0 (plusTwoHighAddress k) = 0 := by
  unfold plusTwoInitialPERegisters plusTwoInitialLm0 plusTwoHighAddress
  simp only
  have hmod : ¬ (2 * k.val) % 2 = 1 := by omega
  rw [dif_neg (by intro h; exact hmod h.1)]

/-- The sealed whole-machine value model: a step is the value transition
`executeNormalizedLine`, a non-`.ok` transition is `none`, legality is
unrestricted.  This is exactly the Welcome model, re-stated for `2.plus-two`. -/
noncomputable abbrev plusTwoSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := PlusTwoWords
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The problem: the observed PE's `k`-th output long is `input k + 2`, written
as high word `0` and low word `input k + 2` (valid for `0 ≤ input k ≤ 99`). -/
noncomputable def plusTwoSpec : ProofsLean.Problem plusTwoSealedMachine where
  admissible := fun input => ∀ k, (input k).toNat ≤ 99
  initial := plusTwoInitialState
  post := fun input state => ∀ k : Fin 20,
    (state.peRegisters plusTwoPE).lm1 (plusTwoHighAddress k) = 0 ∧
    (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) = input k + 2

theorem plusTwoSpec_initial (input : PlusTwoWords) :
    plusTwoSpec.initial input = plusTwoInitialState input := rfl

theorem plusTwoSpec_admissible (input : PlusTwoWords)
    (bounded : ∀ k, (input k).toNat ≤ 99) : plusTwoSpec.admissible input := bounded

/-! ## 2. The recorded five-line answer -/

/-- A 32-bit gather/scatter region with explicit addresses. -/
def plusTwoWordRegion (a b c d : Nat) : Region := ⟨1, a, b, c, d, false, none⟩

/-- A direct, unmasked 32-bit memory operand. -/
def plusTwoMem (bank : Issue.Bank) (a b c d : Nat) : ParsedOperand :=
  .mem ⟨bank, plusTwoWordRegion a b c d⟩ false false false none

/-- `idec $m[a,b,c,d] $n[e,f,g,h] $r0v` (the GRF vector is words 0..3). -/
def plusTwoIdecWithGrf (a b c d e f g h : Nat) : ParsedExpr where
  op := .alu .dec (some .i) false none
  sources := [plusTwoMem .lm0 a b c d]
  destinations := [plusTwoMem .lm1 e f g h, plusTwoMem .grf0 0 1 2 3]
  flush := none
  text := ""

/-- `idec $m[a,b,c,d] $n[e,f,g,h]`. -/
def plusTwoIdec (a b c d e f g h : Nat) : ParsedExpr where
  op := .alu .dec (some .i) false none
  sources := [plusTwoMem .lm0 a b c d]
  destinations := [plusTwoMem .lm1 e f g h]
  flush := none
  text := ""

/-- `ixor $m[a,b,c,d] $r[e,f,g,h] $n[i,j,k,l]`. -/
def plusTwoIxor (a b c d e f g h i j k l : Nat) : ParsedExpr where
  op := .alu .xor (some .i) false none
  sources := [plusTwoMem .lm0 a b c d, plusTwoMem .grf0 e f g h]
  destinations := [plusTwoMem .lm1 i j k l]
  flush := none
  text := ""

/-- The five normalized expressions of `problems/challenge/2.plus-two/answer.vsm`. -/
def plusTwoAnswerExpressions : List NormalizedExpr :=
  [ (plusTwoIdecWithGrf 35 25 19 31 19 11 33 39).normalize,
    (plusTwoIdec 9 29 13 39 5 7 29 13).normalize,
    (plusTwoIdec 21 23 17 15 31 21 35 17).normalize,
    (plusTwoIxor 11 7 39 27 1 1 0 2 3 1 9 25).normalize,
    (plusTwoIxor 27 5 37 19 0 3 0 1 37 23 15 27).normalize ]

/-- The recorded answer as a program. -/
def plusTwoRecordedAnswer : List InstructionLine :=
  plusTwoAnswerExpressions.map (fun expression => InstructionLine.pe [expression])

theorem plusTwoRecordedAnswer_score :
    ProofsLean.score plusTwoSealedMachine plusTwoRecordedAnswer = 5 := by
  decide

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 3. The all-zero witness and the first line's value -/

/-- The all-zero input. -/
def plusTwoZeroWords : PlusTwoWords := fun _ => 0

theorem plusTwoZeroWords_admissible : plusTwoSpec.admissible plusTwoZeroWords := by
  intro k
  simp [plusTwoZeroWords]

/-- The initial register file at the all-zero input is the zero file. -/
theorem plusTwoInitialPERegisters_zero :
    plusTwoInitialPERegisters plusTwoZeroWords = zeroInitialPERegisterFiles := by
  unfold plusTwoInitialPERegisters plusTwoInitialLm0 plusTwoZeroWords
  simp [zeroInitialPERegisterFiles]

theorem plusTwoInitialState_zero :
    plusTwoInitialState plusTwoZeroWords = rustSimulatorInitialState := by
  unfold plusTwoInitialState
  rw [plusTwoInitialPERegisters_zero]
  rfl

/-- The output long whose low word line 1 writes as `0xFFFFFFFF` on the
all-zero input: output long 9 is the low word `19`. -/
def plusTwoWitnessOutput : Fin 20 := ⟨9, by decide⟩

theorem plusTwoWitnessOutput_low :
    plusTwoLowAddress plusTwoWitnessOutput = ⟨19, by decide⟩ := by
  apply Fin.ext
  simp [plusTwoLowAddress, plusTwoWitnessOutput]

/-- The first recorded line, as a parsed expression. -/
def plusTwoLine1Expr : ParsedExpr :=
  plusTwoIdecWithGrf 35 25 19 31 19 11 33 39

/-- The first recorded line's per-PE execution on the all-zero input writes
`0xFFFFFFFF` into the low word of output long 9.  This is a closed computation:
no machine, spec or input remains. -/
noncomputable def plusTwoLine1WordBool : Bool :=
  match executeIntegerProducerLineAtPE [plusTwoLine1Expr]
      (plusTwoInitialState plusTwoZeroWords) plusTwoPE with
  | .ok next =>
      (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ==
        0xFFFFFFFF
  | _ => false

set_option maxHeartbeats 2000000 in
theorem plusTwoLine1WordBool_eq_true : plusTwoLine1WordBool = true := by
  unfold plusTwoLine1WordBool plusTwoLine1Expr plusTwoIdecWithGrf plusTwoMem
    plusTwoWordRegion plusTwoInitialState plusTwoInitialPERegisters plusTwoInitialLm0
    plusTwoZeroWords
  simp only [executeIntegerProducerLineAtPE, executeIntegerProducerLineAtPECore]
  decide

/-- The first line, executed at PE 0 on the all-zero input, leaves
`0xFFFFFFFF` in the low word of output long 9. -/
theorem plusTwoLine1_perPE_value :
    ∃ next, executeIntegerProducerLineAtPE [plusTwoLine1Expr]
        (plusTwoInitialState plusTwoZeroWords) plusTwoPE = .ok next ∧
      (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
        0xFFFFFFFF := by
  have h := plusTwoLine1WordBool_eq_true
  unfold plusTwoLine1WordBool at h
  split at h
  · rename_i next executed
    refine ⟨next, executed, ?_⟩
    exact of_decide_eq_true h
  · simp at h

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 4. A commit frame: an `.lm1` word outside every written window is kept -/

/-- If every `.lm1` destination in a prepared-write list stays at distance at
least its width from `target`, committing the list leaves `target` unchanged. -/
theorem commitParsedMaskedWrites_lm1_preserves_of_outside
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity)
    (outside : ∀ write ∈ writes, ∀ (width : Width)
        (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨.lm1, width, address⟩ →
        count .lm1 width ≤ distance .lm1 address target) :
    (commitParsedMaskedWrites files writes).lm1 target = files.lm1 target := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      rw [show commitParsedMaskedWrites files (write :: rest) =
          commitParsedMaskedWrites (commitParsedMaskedWrites files [write]) rest from rfl]
      rw [ih (commitParsedMaskedWrites files [write])]
      · unfold commitParsedMaskedWrites
        simp only [List.foldl_cons, List.foldl_nil]
        split
        · -- mask-register update: LM1 untouched
          simp
        · split
          · rename_i access haccess
            cases access with
            | mk bank width address =>
                by_cases h : bank = .lm1
                · subst h
                  rw [writeDirectAccessMasked_lm1_apply]
                  exact writeWordsMasked_preserves_outside .lm1 width files.lm1 address
                    target write.data write.selection.flags write.selection.longLong
                    (outside write List.mem_cons_self width address haccess)
                · rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ h]
          · rfl
      · intro write' member
        exact outside write' (List.mem_cons_of_mem _ member)

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 5. The recorded answer's first line and its suffix -/

/-- The first normalized expression of the recorded answer. -/
def plusTwoLine1NExpr : NormalizedExpr :=
  (plusTwoIdecWithGrf 35 25 19 31 19 11 33 39).normalize

/-- The first recorded line. -/
def plusTwoLine1 : InstructionLine := InstructionLine.pe [plusTwoLine1NExpr]

/-- The four-line suffix of the recorded answer. -/
def plusTwoSuffix : List InstructionLine :=
  plusTwoRecordedAnswer.drop 1

theorem plusTwoLine1_toParsed :
    plusTwoLine1.toParsed = .pe [plusTwoIdecWithGrf 35 25 19 31 19 11 33 39] := by
  rfl

theorem plusTwoRecordedAnswer_eq :
    plusTwoRecordedAnswer = plusTwoLine1 :: plusTwoSuffix := by
  rfl

/-- The first line's issue check succeeds (the expression is a plain ALU row). -/
theorem plusTwoLine1_check : checkParsedTopLine plusTwoLine1.toParsed = true := by
  rw [plusTwoLine1_toParsed]
  have legal : LegalParsedLine [plusTwoIdecWithGrf 35 25 19 31 19 11 33 39] := by
    unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
      ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
      ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
      ParsedExpr.maskApplications ParsedOperand.writeMask?
      ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
      ParsedExpr.barWrites ParsedOperand.barWriteBank?
      ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
    simp [plusTwoIdecWithGrf, plusTwoMem, plusTwoWordRegion, Legal, idsUnique,
      groupsUnique, mauCountBounded, mauExpressions, mauPrecisionsAgree,
      matrixWritePairAgrees, matrixRegistersUnique, writesUnique, Expr.writeBanks,
      barWritesExcludeReads, readsAgree, localReadWriteAgree, immediateExcludesLm0,
      zeroFlushUnique, maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique,
      lbfWritesUnique, maskRegisterWritesUnique, projectFrom]
  apply Issue.parsed_topline_check_complete
  exact legal

/-- The first recorded line is a plain integer-ALU row. -/
theorem plusTwoLine1_plain :
    ([plusTwoLine1NExpr].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
  decide

/-- The integer stage's filter keeps exactly the first expression. -/
theorem plusTwoLine1_filter :
    (([plusTwoLine1NExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)) =
      [plusTwoIdecWithGrf 35 25 19 31 19 11 33 39] := by
  decide

/-- A successful walk has a successful head. -/
theorem executeIntegerProducerLineAtPEs_head_ok
    (expressions : List ParsedExpr) (head : PEId) (rest : List PEId)
    (state next : State)
    (walk : executeIntegerProducerLineAtPEs expressions (head :: rest) state = .ok next) :
    ∃ middle, executeIntegerProducerLineAtPE expressions state head = .ok middle := by
  unfold executeIntegerProducerLineAtPEs at walk
  split at walk
  · simp at walk
  · simp at walk
  · rename_i middle h
    exact ⟨middle, h⟩

/-- **The per-PE walk at its head.**  If PE 0 is the head of the walk and does
not occur in the tail, the walk's PE 0 register file is the head's result. -/
theorem executeIntegerProducerLineAtPEs_head_eq
    (expressions : List ParsedExpr) (head : PEId) (rest : List PEId)
    (state next middle : State)
    (walk : executeIntegerProducerLineAtPEs expressions (head :: rest) state = .ok next)
    (headExec : executeIntegerProducerLineAtPE expressions state head = .ok middle)
    (notMem : head ∉ rest) :
    next.peRegisters head = middle.peRegisters head := by
  simp only [executeIntegerProducerLineAtPEs, headExec] at walk
  exact executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions rest middle next walk
    (fun pe p s n he different =>
      executeIntegerProducerLineAtPE_peRegisters_other expressions s n pe p different he)
    head notMem

/-- The head of `List.finRange 4096` is PE 0 and the tail omits it. -/
theorem plusTwoFinRange_split :
    List.finRange 4096 = plusTwoPE :: (List.finRange 4095).map Fin.succ ∧
      plusTwoPE ∉ (List.finRange 4095).map Fin.succ := by
  constructor
  · have := @List.finRange_succ 4095
    simpa [plusTwoPE, welcomePE] using this
  · intro member
    simp only [List.mem_map] at member
    obtain ⟨i, _, hi⟩ := member
    have := congrArg Fin.val hi
    simp [plusTwoPE, welcomePE] at this

/-- **The first line installs `0xFFFFFFFF` at the witness word.**  The per-PE
computation at PE 0 is lifted to the whole-machine walk; the tail cannot touch
PE 0. -/
theorem plusTwoLine1_step_value (next : State)
    (step : plusTwoSealedMachine.step plusTwoLine1
      (plusTwoInitialState plusTwoZeroWords) = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      0xFFFFFFFF := by
  have executed : executeNormalizedLine plusTwoLine1.toNormalizedLine
      (plusTwoInitialState plusTwoZeroWords) = .ok next := by
    cases h : executeNormalizedLine plusTwoLine1.toNormalizedLine
        (plusTwoInitialState plusTwoZeroWords) with
    | ok state =>
        simp [plusTwoSealedMachine, h] at step
        simpa [← step] using h
    | failure => simp [plusTwoSealedMachine, h] at step
    | unknown => simp [plusTwoSealedMachine, h] at step
  have step' : executeIntegerProducerInstructionLine (.pe [plusTwoLine1NExpr])
      (plusTwoInitialState plusTwoZeroWords) = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [NormalizedLine.toInstruction?] at executed
    exact executed
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok _ _ _ step'
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists [plusTwoLine1NExpr]
      (plusTwoInitialState plusTwoZeroWords) next accepted plusTwoLine1_plain step'
  rw [plusTwoLine1_filter] at walk
  obtain ⟨split, notMem⟩ := plusTwoFinRange_split
  rw [split] at walk
  obtain ⟨middle, headExecEq⟩ :=
    executeIntegerProducerLineAtPEs_head_ok
      [plusTwoIdecWithGrf 35 25 19 31 19 11 33 39]
      plusTwoPE ((List.finRange 4095).map Fin.succ)
      (plusTwoInitialState plusTwoZeroWords) nextPEs walk
  have headValue : (middle.peRegisters plusTwoPE).lm1
      (plusTwoLowAddress plusTwoWitnessOutput) = 0xFFFFFFFF := by
    have perPE := plusTwoLine1_perPE_value
    obtain ⟨middle', perPEEq, value⟩ := perPE
    have same : middle' = middle := by
      rw [show plusTwoLine1Expr = plusTwoIdecWithGrf 35 25 19 31 19 11 33 39 from rfl]
        at perPEEq
      rw [perPEEq] at headExecEq
      exact StepResult.ok.inj headExecEq
    simpa [same] using value
  have walkHead := executeIntegerProducerLineAtPEs_head_eq
    [plusTwoIdecWithGrf 35 25 19 31 19 11 33 39]
    plusTwoPE ((List.finRange 4095).map Fin.succ) (plusTwoInitialState plusTwoZeroWords)
    nextPEs middle walk headExecEq notMem
  rw [nextEq]
  simpa [walkHead] using headValue

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 6. The suffix-frame obligation and the refutation -/

/-- The cons equation of `execute`, definitionally. -/
theorem plusTwoExecute_cons (m : ProofsLean.Machine) (line : m.Line)
    (rest : ProofsLean.Program m) (state : m.State) :
    ProofsLean.execute m ((line :: rest : List m.Line) : ProofsLean.Program m) state =
      (m.step line state).bind (ProofsLean.execute m rest) := rfl

/-- The four remaining lines keep the witness low word (`LM1` word `19`) at
PE 0.  This is the only semantic frame still missing from the refutation; it is
stated as a `Prop` (not an axiom). -/
def PlusTwoSuffixPreservesWitness : Prop :=
  ∀ (state next : State),
    ProofsLean.execute plusTwoSealedMachine plusTwoSuffix state = some next →
      (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
        (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput)

/-- **The recorded answer is refuted by the all-zero input**, assuming the
suffix-frame obligation.  The first line writes `0xFFFFFFFF` into output long
9; the four remaining lines preserve it; the specification demands `2`. -/
theorem plusTwoRecorded_not_correct_of_suffixFrame
    (frame : PlusTwoSuffixPreservesWitness) :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer := by
  intro correct
  obtain ⟨result, executed, post⟩ :=
    correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  rw [plusTwoRecordedAnswer_eq] at executed
  rw [ProofsLean.execute.eq_2] at executed
  rw [plusTwoSpec_initial] at executed
  cases h1 : plusTwoSealedMachine.step plusTwoLine1
      (plusTwoInitialState plusTwoZeroWords) with
  | none =>
      rw [h1] at executed
      simp at executed
  | some state1 =>
      rw [h1] at executed
      simp only [Option.bind_some] at executed
      have restExecuted : ProofsLean.execute plusTwoSealedMachine plusTwoSuffix state1 =
          some result := executed
      have word1 := plusTwoLine1_step_value state1 h1
      have wordSuffix := frame state1 result restExecuted
      have postWord := (post plusTwoWitnessOutput).2
      rw [wordSuffix, word1] at postWord
      simp [plusTwoZeroWords] at postWord

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 7. The counting lower bound from a per-line coverage obligation -/

/-- A line can change at most four of the twenty observed output words. -/
def PlusTwoLineCoverage : Prop :=
  ∀ (line : InstructionLine) (state next : State),
    plusTwoSealedMachine.step line state = some next →
      ∃ S : Finset (Fin 20), S.card ≤ 4 ∧
        ∀ k, k ∉ S →
          (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) =
            (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k)

/-- The initial `LM1` is zero. -/
theorem plusTwoInitialPERegisters_lm1_zero (input : PlusTwoWords)
    (address : Fin Bank.lm1.capacity) :
    (plusTwoInitialPERegisters input).lm1 address = 0 := rfl

theorem plusTwoInitialState_lm1_zero (input : PlusTwoWords)
    (address : Fin Bank.lm1.capacity) :
    ((plusTwoInitialState input).peRegisters plusTwoPE).lm1 address = 0 :=
  plusTwoInitialPERegisters_lm1_zero input address

/-- **Counting propagation.**  Along a program of `p.length` lines, at most
`4 * p.length` output words have changed. -/
theorem plusTwo_execute_coverage (coverage : PlusTwoLineCoverage) :
    ∀ (p : List InstructionLine) (state next : State),
      ProofsLean.execute plusTwoSealedMachine p state = some next →
        ∃ S : Finset (Fin 20), S.card ≤ 4 * p.length ∧
          ∀ k, k ∉ S →
            (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) =
              (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) := by
  intro p
  induction p with
  | nil =>
      intro state next executed
      simp only [ProofsLean.execute, Option.some.injEq] at executed
      subst executed
      exact ⟨∅, by simp, by simp⟩
  | cons line rest ih =>
      intro state next executed
      rw [ProofsLean.execute.eq_2] at executed
      cases hstep : plusTwoSealedMachine.step line state with
      | none =>
          rw [hstep] at executed
          simp at executed
      | some middle =>
          rw [hstep] at executed
          simp only [Option.bind_some] at executed
          obtain ⟨S1, card1, unchanged1⟩ := coverage line state middle hstep
          obtain ⟨S2, card2, unchanged2⟩ := ih middle next executed
          refine ⟨S1 ∪ S2, ?_, ?_⟩
          · have unionLe : (S1 ∪ S2).card ≤ S1.card + S2.card := Finset.card_union_le _ _
            simp only [List.length_cons]
            omega
          · intro k hk
            rw [unchanged2 k (by intro mem; exact hk (Finset.mem_union_right _ mem))]
            rw [unchanged1 k (by intro mem; exact hk (Finset.mem_union_left _ mem))]

/-- **`LowerBound 5` from the per-line coverage obligation.**  A program of at
most four lines changes at most sixteen of the twenty output words, so one
output word remains zero; the target is always nonzero. -/
theorem plusTwoLowerBound_five_of_coverage (coverage : PlusTwoLineCoverage) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 5 := by
  intro p correct
  by_contra notBound
  have scoreLt : ProofsLean.score plusTwoSealedMachine p < 5 := by omega
  have lengthLe : p.length ≤ ProofsLean.score plusTwoSealedMachine p :=
    ProofsLean.length_le_score plusTwoSealedMachine p
  have lengthLt : p.length < 5 := by omega
  obtain ⟨result, executed, post⟩ :=
    correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  obtain ⟨S, cardLe, unchanged⟩ := plusTwo_execute_coverage coverage p
    (plusTwoSpec.initial plusTwoZeroWords) result executed
  have cardLt : S.card < 20 := by
    have : 4 * p.length ≤ 16 := by omega
    omega
  have hex : ∃ k : Fin 20, k ∉ S := by
    by_contra noK
    have allMem : S = Finset.univ := Finset.eq_univ_of_forall (fun k => by
      by_contra hk
      exact noK ⟨k, hk⟩)
    rw [allMem] at cardLt
    simp at cardLt
  obtain ⟨k, hk⟩ := hex
  have initialZero : ((plusTwoSpec.initial plusTwoZeroWords).peRegisters plusTwoPE).lm1
      (plusTwoLowAddress k) = 0 := by
    rw [plusTwoSpec_initial]
    exact plusTwoInitialState_lm1_zero plusTwoZeroWords _
  have finalZero : (result.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) = 0 := by
    rw [unchanged k hk, initialZero]
  have target := (post k).2
  rw [finalZero] at target
  simp [plusTwoZeroWords] at target

/-- The recorded answer is not optimal, assuming the suffix-frame obligation. -/
theorem plusTwoRecorded_not_optimal_of_suffixFrame
    (frame : PlusTwoSuffixPreservesWitness) :
    ¬ ProofsLean.Optimal plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer :=
  fun optimal => plusTwoRecorded_not_correct_of_suffixFrame frame optimal.1

end ProofsLean.MNCore
