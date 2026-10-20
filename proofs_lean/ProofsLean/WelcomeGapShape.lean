import ProofsLean.WelcomeMAUShape
-- `WelcomeL12Shape` supplies `executeParsedSharedBlockProducers_peRegisters` and
-- `executeParsedSharedBlockExpression_peRegisters`, the shared-block stage
-- frames used for the `.l1bm` mwrite/m4write/gather/reduce/reduce4 rows.
import ProofsLean.WelcomeL12Shape

/-! # F5: the exact supported producer set, the PE-inert row classes, and the
corrected aggregate obligation

`WelcomeValueBound.lean` §7 splits every unrefuted `.pe` line into an
all-plain half (`WelcomePEPlainShapeObligation`) and a non-plain half
(`WelcomePEOtherShapeObligation`), and specialises the non-plain half into six
per-family obligations (`WelcomePEMatrixReadShapeObligation`,
`...MatrixMAU...`, `...FloatMAU...`, `...MatrixWrite...`, `...L1ToPE...`,
`...L2BM...`).

That decomposition is **incomplete**, as recorded in
`research/lean-plan-progress.md` round 35 item F5:

* `parsedExprIsSupportedPELineProducer` (`WholeMachineStep.lean`) also accepts
  `.noforward`, `.wait tag`, and the `.l1bm` forms `mwrite`, `m4write`,
  `gather`, `reduce`, `reduce4`.  A line such as `[noforward, alu ... -> lm1]`
  is non-plain, contains no row of any of the six families, and is legal.  The
  six family `Prop`s therefore cannot discharge
  `WelcomePEOtherShapeObligation`.
* Two further classes are missing from the six: the *special ALU* stages
  (`executeParsedMslMsrProducers`, `executeParsedFloatReluProducers`,
  `executeParsedBlockFloatProducer`).  Block float is explicitly in the
  supported set and its stage writes PE register files, but no family `Prop`
  mentions it.
* Conversely, the `.noforward`, non-pending `.wait`, and the five shared-block
  `.l1bm` forms are **PE-inert**: no stage that executes them ever writes a PE
  register file.

## What this module proves

1. `supportedProducer_shape_cases` — the **exhaustive** case split of
   `parsedExprIsSupportedPELineProducer` into eighteen named classes (plain,
   the six families, the three special ALU families, Rust-unsupported ALU,
   `.noforward`, `.wait`, and the five shared-block `.l1bm` ops).  The honest
   split has more cases than the six-family list: `.alu` alone is not plain
   (`bfn`/`bfe` are block float, `msl`/`msr` are their own stage, the float
   relu names are their own stage, and `lrelud`/`lreluo`/`ilrelud` are
   accepted by this predicate but rejected later by the issue checker).
2. `supportedProducer_shape_cases_of_checked` — the fourteen-way split in the
   form F5 states it (with `.matrixWrite` restored, since the predicate accepts
   it and one of the six family `Prop`s is about it), under the four side
   conditions that `WelcomePEAccepted` already supplies (no Rust-unsupported
   ALU row, no MSL/MSR row, no float-relu row, no wait tag).
3. Row-level and stage-level facts for the PE-inert classes: a `.noforward`
   row prepares no write, a `.l1bm` shared-block row is selected by no
   PE-register-writing stage, and the stage that does execute it
   (`executeParsedSharedBlockProducers`) preserves every PE register file.
4. `executeIntegerProducerInstructionLine_pe_peRegisters_of_inert` — a
   successful `.pe` line whose rows are all PE-inert leaves `peRegisters`
   unchanged, hence such a line's `LM1` commit list is empty and
   `WelcomePEWriteShape` holds for it (`welcomePEInertLine_shape`).
5. The corrected aggregate: `WelcomePEGapShapeObligation` (the seventh `Prop`,
   covering exactly the non-plain lines with no six-family row) plus the plain
   `Prop` and the six family `Prop`s imply
   `WelcomePELm1WriteShapeObligation`.  The gap `Prop` is decomposed further
   into the special-ALU obligation and the mixed plain/inert obligation; the
   pure-inert class is discharged here, so those two are the precise
   remainder.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing in this
module assumes the obligations it names, and it does not claim
`LowerBound 2` or `Optimal`.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The exact producer classes

The classes below partition the supported set.  They are named after the
executor stage that selects them, which is what makes the shapes provable. -/

/-- The five `.l1bm` operations that only the shared-block stage
(`executeParsedSharedBlockProducers`) executes.  It rewrites `l1bm`,
`l1bmTurnaround`, `blockMemory` and DAR state and preserves every PE register
file. -/
def parsedExprIsL1SharedBlockProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm (.mwrite _) | .l1bm (.m4write _) | .l1bm (.gather _)
  | .l1bm (.reduce ..) | .l1bm (.reduce4 ..) => true
  | _ => false

/-- Rows that no PE-register-writing stage executes: `.noforward`, a
non-pending `.wait` (a pending wait makes the line `.unknown`, never `.ok`),
and the five shared-block `.l1bm` operations.  A `.noforward` row is prepared
by the integer stage, which produces no write for it; the `.l1bm` rows are
excluded from the integer stage and run only in the shared-block stage. -/
def parsedExprIsPEInertProducer (expression : ParsedExpr) : Bool :=
  parsedExprIsL1SharedBlockProducer expression ||
    (match expression.op with
     | .noforward | .wait _ => true
     | _ => false)

/-- The three special ALU producers omitted by the six-family split.  Each has
its own stage in `executeIntegerProducerInstructionLine`. -/
def parsedExprIsSpecialALUProducer (expression : ParsedExpr) : Bool :=
  parsedExprIsMslMsrProducer expression ||
    (parsedExprIsFloatReluProducer expression || parsedExprIsBlockFloatProducer expression)

/-- The six producer families of `WelcomeValueBound.lean` §7, bundled. -/
def parsedExprIsFamilyProducer (expression : ParsedExpr) : Bool :=
  parsedExprIsMatrixReadProducer expression ||
    (parsedExprIsMatrixMAUProducer expression ||
      (parsedExprIsSupportedFloatMAUProducer expression ||
        (parsedExprIsMatrixWriteProducer expression ||
          (parsedExprIsL1ToPEProducer expression || parsedExprIsL2BMProducer expression))))

/-! ### The `.alu` decomposition

`parsedExprIsPlainIntegerALU` is `integerProducer && !unsupported && !mslMsr &&
!floatRelu && !blockFloat`.  For an `.alu` row the integer-producer test is
`true`, so "not plain" is exactly "one of the four exclusions fires".  This is
the only place where the supported-set analysis needs the definition of
plain. -/

theorem parsedExprIsPlainIntegerALU_alu_cases (expression : ParsedExpr)
    (integer : parsedExprIsIntegerProducer expression = true) :
    parsedExprIsPlainIntegerALU expression = true ∨
      parsedExprIsUnsupportedRustAlu expression = true ∨
      parsedExprIsMslMsrProducer expression = true ∨
      parsedExprIsFloatReluProducer expression = true ∨
      parsedExprIsBlockFloatProducer expression = true := by
  by_cases plain : parsedExprIsPlainIntegerALU expression = true
  · exact Or.inl plain
  by_cases unsupported : parsedExprIsUnsupportedRustAlu expression = true
  · exact Or.inr (Or.inl unsupported)
  by_cases msl : parsedExprIsMslMsrProducer expression = true
  · exact Or.inr (Or.inr (Or.inl msl))
  by_cases relu : parsedExprIsFloatReluProducer expression = true
  · exact Or.inr (Or.inr (Or.inr (Or.inl relu)))
  by_cases block : parsedExprIsBlockFloatProducer expression = true
  · exact Or.inr (Or.inr (Or.inr (Or.inr block)))
  exact absurd (by simp [parsedExprIsPlainIntegerALU, integer, unsupported, msl, relu, block])
    plain

/-! ### Decomposing the bundled classes -/

theorem parsedExprIsL1SharedBlockProducer_cases (expression : ParsedExpr)
    (shared : parsedExprIsL1SharedBlockProducer expression = true) :
    (∃ mab : Fin 256, expression.op = .l1bm (.mwrite mab)) ∨
    (∃ mab : Fin 256, expression.op = .l1bm (.m4write mab)) ∨
    (∃ mabdiff : Int, expression.op = .l1bm (.gather mabdiff)) ∨
    (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce rrn round)) ∨
    (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce4 rrn round)) := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | l1bm l1op =>
          cases l1op with
          | mwrite mab => exact Or.inl ⟨mab, rfl⟩
          | m4write mab => exact Or.inr (Or.inl ⟨mab, rfl⟩)
          | gather mabdiff => exact Or.inr (Or.inr (Or.inl ⟨mabdiff, rfl⟩))
          | reduce rrn round => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rrn, round, rfl⟩)))
          | reduce4 rrn round => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rrn, round, rfl⟩)))
          | pbcast => simp [parsedExprIsL1SharedBlockProducer] at shared
          | mbcast => simp [parsedExprIsL1SharedBlockProducer] at shared
          | m4bcast => simp [parsedExprIsL1SharedBlockProducer] at shared
          | distrib mabdiff => simp [parsedExprIsL1SharedBlockProducer] at shared
      | alu name precision unsigned arg =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | immediate value unsigned => simp [parsedExprIsL1SharedBlockProducer] at shared
      | zero => simp [parsedExprIsL1SharedBlockProducer] at shared
      | mau precision matrix kind half round =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixWrite precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixRead precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | wait tag => simp [parsedExprIsL1SharedBlockProducer] at shared
      | noforward => simp [parsedExprIsL1SharedBlockProducer] at shared
      | l2bm l2op => simp [parsedExprIsL1SharedBlockProducer] at shared

theorem parsedExprIsPEInertProducer_cases (expression : ParsedExpr)
    (inert : parsedExprIsPEInertProducer expression = true) :
    expression.op = .noforward ∨
      (∃ tag : Fin 256, expression.op = .wait tag) ∨
      parsedExprIsL1SharedBlockProducer expression = true := by
  unfold parsedExprIsPEInertProducer at inert
  rcases Bool.or_eq_true_iff.mp inert with shared | forward
  · exact Or.inr (Or.inr shared)
  · cases expression with
    | mk op sources destinations flush text =>
        cases op with
        | noforward => exact Or.inl rfl
        | wait tag => exact Or.inr (Or.inl ⟨tag, rfl⟩)
        | alu name precision unsigned arg =>
            simp at forward
        | immediate value unsigned => simp at forward
        | zero => simp at forward
        | mau precision matrix kind half round => simp at forward
        | matrixWrite precision => simp at forward
        | matrixRead precision => simp at forward
        | l1bm l1op => simp at forward
        | l2bm l2op => simp at forward

theorem parsedExprIsSpecialALUProducer_cases (expression : ParsedExpr)
    (special : parsedExprIsSpecialALUProducer expression = true) :
    parsedExprIsMslMsrProducer expression = true ∨
      parsedExprIsFloatReluProducer expression = true ∨
      parsedExprIsBlockFloatProducer expression = true := by
  unfold parsedExprIsSpecialALUProducer at special
  rcases Bool.or_eq_true_iff.mp special with msl | rest
  · exact Or.inl msl
  · rcases Bool.or_eq_true_iff.mp rest with relu | block
    · exact Or.inr (Or.inl relu)
    · exact Or.inr (Or.inr block)

theorem parsedExprIsFamilyProducer_cases (expression : ParsedExpr)
    (family : parsedExprIsFamilyProducer expression = true) :
    parsedExprIsMatrixReadProducer expression = true ∨
      parsedExprIsMatrixMAUProducer expression = true ∨
      parsedExprIsSupportedFloatMAUProducer expression = true ∨
      parsedExprIsMatrixWriteProducer expression = true ∨
      parsedExprIsL1ToPEProducer expression = true ∨
      parsedExprIsL2BMProducer expression = true := by
  unfold parsedExprIsFamilyProducer at family
  simp only [Bool.or_eq_true] at family
  tauto

/-! ### The exhaustive partition

Every supported row is plain, a six-family row, a special-ALU row, PE-inert, or
a Rust-unsupported ALU row.  This is the complete set: the four cases are
mutually exclusive by construction, and the `.alu` split is the identity
`plain = integerProducer && !unsupported && !msl && !relu && !block`. -/

theorem supportedProducer_partition (expression : ParsedExpr)
    (supported : parsedExprIsSupportedPELineProducer expression = true) :
    parsedExprIsPlainIntegerALU expression = true ∨
      parsedExprIsFamilyProducer expression = true ∨
      parsedExprIsSpecialALUProducer expression = true ∨
      parsedExprIsPEInertProducer expression = true ∨
      parsedExprIsUnsupportedRustAlu expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | alu name precision unsigned arg =>
          have integer : parsedExprIsIntegerProducer
              (⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ :
                ParsedExpr) = true := rfl
          rcases parsedExprIsPlainIntegerALU_alu_cases _ integer with
            plain | unsupported | msl | relu | block
          · exact Or.inl plain
          · exact Or.inr (Or.inr (Or.inr (Or.inr unsupported)))
          · exact Or.inr (Or.inr (Or.inl (by
              simp [parsedExprIsSpecialALUProducer, msl])))
          · exact Or.inr (Or.inr (Or.inl (by
              simp [parsedExprIsSpecialALUProducer, relu])))
          · exact Or.inr (Or.inr (Or.inl (by
              simp [parsedExprIsSpecialALUProducer, block])))
      | zero =>
          exact Or.inl (by
            simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
              parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
              parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer])
      | immediate value unsigned =>
          exact Or.inl (by
            simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
              parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
              parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer])
      | mau precision matrix kind half round =>
          have operation : (⟨.mau precision matrix kind half round, sources,
              destinations, flush, text⟩ : ParsedExpr).op =
              .mau precision matrix kind half round := rfl
          rcases supported_mau_has_known_dispatch_family _ precision matrix kind
            half round operation supported with mau | float | block
          · exact Or.inr (Or.inl (by simp [parsedExprIsFamilyProducer, mau]))
          · exact Or.inr (Or.inl (by simp [parsedExprIsFamilyProducer, float]))
          · exact Or.inr (Or.inr (Or.inl (by
              simp [parsedExprIsSpecialALUProducer, block])))
      | matrixRead precision =>
          exact Or.inr (Or.inl (by
            simp [parsedExprIsFamilyProducer, parsedExprIsMatrixReadProducer]))
      | matrixWrite precision =>
          exact Or.inr (Or.inl (by
            simp [parsedExprIsFamilyProducer, parsedExprIsMatrixWriteProducer]))
      | l2bm l2op =>
          exact Or.inr (Or.inl (by
            simp [parsedExprIsFamilyProducer, parsedExprIsL2BMProducer]))
      | «wait» tag =>
          exact Or.inr (Or.inr (Or.inr (Or.inl (by
            simp [parsedExprIsPEInertProducer]))))
      | noforward =>
          exact Or.inr (Or.inr (Or.inr (Or.inl (by
            simp [parsedExprIsPEInertProducer]))))
      | l1bm l1op =>
          cases l1op with
          | mwrite mab =>
              exact Or.inr (Or.inr (Or.inr (Or.inl (by
                simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer]))))
          | m4write mab =>
              exact Or.inr (Or.inr (Or.inr (Or.inl (by
                simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer]))))
          | gather mabdiff =>
              exact Or.inr (Or.inr (Or.inr (Or.inl (by
                simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer]))))
          | reduce rrn round =>
              exact Or.inr (Or.inr (Or.inr (Or.inl (by
                simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer]))))
          | reduce4 rrn round =>
              exact Or.inr (Or.inr (Or.inr (Or.inl (by
                simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer]))))
          | pbcast =>
              exact Or.inr (Or.inl (by
                simp [parsedExprIsFamilyProducer, parsedExprIsL1ToPEProducer]))
          | mbcast =>
              exact Or.inr (Or.inl (by
                simp [parsedExprIsFamilyProducer, parsedExprIsL1ToPEProducer]))
          | m4bcast =>
              exact Or.inr (Or.inl (by
                simp [parsedExprIsFamilyProducer, parsedExprIsL1ToPEProducer]))
          | distrib mabdiff =>
              exact Or.inr (Or.inl (by
                simp [parsedExprIsFamilyProducer, parsedExprIsL1ToPEProducer]))

/-- **The exhaustive case split of `parsedExprIsSupportedPELineProducer`**
(item F5).  Every supported producer row is one of eighteen classes: plain
integer ALU; the six producer families (including `.matrixWrite`, which the F5
note omits although it is one of the six and is supported); the three special
ALU families (`bfn`/`bfe` block float, the float-relu names, `msl`/`msr`); a
Rust-unsupported ALU name; `.noforward`; `.wait`; or one of the five
shared-block `.l1bm` operations.

The four classes beyond the six-family list are not avoidable: all are accepted
by the predicate, and `.alu` is accepted unconditionally, so a "plain" disjunct
alone cannot cover `bfn`, `relu`, `msl` or `lrelud`. -/
theorem supportedProducer_shape_cases (expression : ParsedExpr)
    (supported : parsedExprIsSupportedPELineProducer expression = true) :
    parsedExprIsPlainIntegerALU expression = true ∨
      parsedExprIsMatrixReadProducer expression = true ∨
      parsedExprIsMatrixMAUProducer expression = true ∨
      parsedExprIsMatrixWriteProducer expression = true ∨
      parsedExprIsSupportedFloatMAUProducer expression = true ∨
      parsedExprIsBlockFloatProducer expression = true ∨
      parsedExprIsFloatReluProducer expression = true ∨
      parsedExprIsMslMsrProducer expression = true ∨
      parsedExprIsUnsupportedRustAlu expression = true ∨
      parsedExprIsL1ToPEProducer expression = true ∨
      parsedExprIsL2BMProducer expression = true ∨
      expression.op = .noforward ∨
      (∃ tag : Fin 256, expression.op = .wait tag) ∨
      (∃ mab : Fin 256, expression.op = .l1bm (.mwrite mab)) ∨
      (∃ mab : Fin 256, expression.op = .l1bm (.m4write mab)) ∨
      (∃ mabdiff : Int, expression.op = .l1bm (.gather mabdiff)) ∨
      (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce rrn round)) ∨
      (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce4 rrn round)) := by
  rcases supportedProducer_partition expression supported with
    plain | family | special | inert | unsupported
  · simp [plain]
  · rcases parsedExprIsFamilyProducer_cases expression family with
      read | mau | float | write | toPE | l2
    · simp [read]
    · simp [mau]
    · simp [float]
    · simp [write]
    · simp [toPE]
    · simp [l2]
  · rcases parsedExprIsSpecialALUProducer_cases expression special with msl | relu | block
    · simp [msl]
    · simp [relu]
    · simp [block]
  · rcases parsedExprIsPEInertProducer_cases expression inert with forward | wait | shared
    · simp [forward]
    · rcases wait with ⟨tag, tagEq⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨tag, tagEq⟩))))))))))))
    · rcases parsedExprIsL1SharedBlockProducer_cases expression shared with mw | m4w | gather | reduce | reduce4
      · rcases mw with ⟨mab, mabEq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mab, mabEq⟩)))))))))))))
      · rcases m4w with ⟨mab, mabEq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mab, mabEq⟩))))))))))))))
      · rcases gather with ⟨mabdiff, diffEq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mabdiff, diffEq⟩)))))))))))))))
      · rcases reduce with ⟨rrn, round, reduceEq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rrn, round, reduceEq⟩))))))))))))))))
      · rcases reduce4 with ⟨rrn, round, reduceEq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rrn, round, reduceEq⟩)))))))))))))))))
  · simp [unsupported]

/-- **The fourteen-way split in the form F5 states it** (with `.matrixWrite`
restored).  The four side conditions are exactly the ones `WelcomePEAccepted`
supplies for an unrefuted line: no Rust-unsupported ALU row, no `msl`/`msr`
row, no float-relu row, and no `.wait` tag anywhere in the line.  Under them
the supported set is precisely plain, the six families, `.noforward` and the
five shared-block `.l1bm` operations. -/
theorem supportedProducer_shape_cases_of_checked (expression : ParsedExpr)
    (supported : parsedExprIsSupportedPELineProducer expression = true)
    (noUnsupported : parsedExprIsUnsupportedRustAlu expression = false)
    (noMslMsr : parsedExprIsMslMsrProducer expression = false)
    (noRelu : parsedExprIsFloatReluProducer expression = false)
    (noWait : parsedExprWaitTag? expression = none) :
    parsedExprIsPlainIntegerALU expression = true ∨
      parsedExprIsMatrixReadProducer expression = true ∨
      parsedExprIsMatrixMAUProducer expression = true ∨
      parsedExprIsMatrixWriteProducer expression = true ∨
      parsedExprIsSupportedFloatMAUProducer expression = true ∨
      parsedExprIsBlockFloatProducer expression = true ∨
      parsedExprIsL1ToPEProducer expression = true ∨
      parsedExprIsL2BMProducer expression = true ∨
      expression.op = .noforward ∨
      (∃ mab : Fin 256, expression.op = .l1bm (.mwrite mab)) ∨
      (∃ mab : Fin 256, expression.op = .l1bm (.m4write mab)) ∨
      (∃ mabdiff : Int, expression.op = .l1bm (.gather mabdiff)) ∨
      (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce rrn round)) ∨
      (∃ (rrn : ParsedRrn) (round : Bool), expression.op = .l1bm (.reduce4 rrn round)) := by
  rcases supportedProducer_shape_cases expression supported with
    plain | read | mau | write | float | block | relu | msl | unsupported | toPE | l2 |
      forward | wait | mw | m4w | gather | reduce | reduce4
  · simp [plain]
  · simp [read]
  · simp [mau]
  · simp [write]
  · simp [float]
  · simp [block]
  · exfalso
    simp [relu] at noRelu
  · exfalso
    simp [msl] at noMslMsr
  · exfalso
    simp [unsupported] at noUnsupported
  · simp [toPE]
  · simp [l2]
  · simp [forward]
  · exfalso
    rcases wait with ⟨tag, tagEq⟩
    simp [parsedExprWaitTag?, tagEq] at noWait
  · rcases mw with ⟨mab, mabEq⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mab, mabEq⟩)))))))))
  · rcases m4w with ⟨mab, mabEq⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mab, mabEq⟩))))))))))
  · rcases gather with ⟨mabdiff, diffEq⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mabdiff, diffEq⟩)))))))))))
  · rcases reduce with ⟨rrn, round, reduceEq⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rrn, round, reduceEq⟩))))))))))))
  · rcases reduce4 with ⟨rrn, round, reduceEq⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rrn, round, reduceEq⟩)))))))))))))

/-! ## 2. What each PE-inert row does at every stage

A `.noforward` row is prepared by the integer stage, and its preparation is the
empty write list (`prepareParsedIntegerMatrixReadLineExpression_noforward`).  A
shared-block `.l1bm` row is excluded from the integer stage by
`parsedExprIsIntegerMatrixReadStageInput` and is executed only by
`executeParsedSharedBlockProducers`, which preserves every PE register file
(`executeParsedSharedBlockProducers_peRegisters`).  A `.wait` row is excluded
from every stage.  This section records those selection facts. -/

theorem parsedExprIsPEInertProducer_facts (expression : ParsedExpr)
    (inert : parsedExprIsPEInertProducer expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsMatrixWriteProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsL2BMProducer expression = false ∧
      parsedExprIsIntegerBARWriter expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | noforward =>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
              parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
              parsedExprIsMatrixWriteProducer, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsL2BMProducer,
              parsedExprIsIntegerBARWriter]
      | «wait» tag =>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
              parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
              parsedExprIsMatrixWriteProducer, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsL2BMProducer,
              parsedExprIsIntegerBARWriter]
      | l1bm l1op =>
          cases l1op <;>
            simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
              parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
              parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
              parsedExprIsMatrixWriteProducer, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsL2BMProducer,
              parsedExprIsIntegerBARWriter] at inert ⊢
      | alu name precision unsigned arg =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | immediate value unsigned =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | zero => simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | mau precision matrix kind half round =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | matrixWrite precision =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | matrixRead precision =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert
      | l2bm l2op =>
          simp [parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer] at inert

/-! ### A `.noforward` row prepares no write -/

theorem noforward_row_prepares_no_writes
    (files : PEMemory.IntegerRegisterFiles)
    (oldSlots nextSlots : Forwarding.Slots) (store : PEMemory.ParsedMatrixReadStore)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (isNoforward : expression.op = .noforward) :
    PEMemory.prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
        expression control hasSingleLineMask noForward reduced =
      .ok ([], nextSlots, []) :=
  prepareParsedIntegerMatrixReadLineExpression_noforward files oldSlots nextSlots store
    expression control hasSingleLineMask noForward reduced isNoforward

/-- A `.noforward` row is selected by the integer / matrix-read stage, so it is
executed there — and, by `noforward_row_prepares_no_writes`, produces no
prepared write: the row writes no PE register. -/
theorem noforward_row_stageInput (expression : ParsedExpr)
    (isNoforward : expression.op = .noforward) :
    parsedExprIsIntegerMatrixReadStageInput expression = true :=
  parsedExprIsIntegerMatrixReadStageInput_noforward expression isNoforward

/-! ### A shared-block `.l1bm` row is selected by the shared-block stage only -/

theorem l1bmShared_stageInput_false (expression : ParsedExpr)
    (shared : parsedExprIsL1SharedBlockProducer expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | l1bm l1op =>
          cases l1op <;>
            simp [parsedExprIsL1SharedBlockProducer,
              parsedExprIsIntegerMatrixReadStageInput, parsedExprIsL1MwriteProducer,
              parsedExprIsL1GatherProducer, parsedExprIsL1ReduceProducer,
              parsedExprWaitTag?] at shared ⊢
      | alu name precision unsigned arg =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | immediate value unsigned => simp [parsedExprIsL1SharedBlockProducer] at shared
      | zero => simp [parsedExprIsL1SharedBlockProducer] at shared
      | mau precision matrix kind half round =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixWrite precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixRead precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | «wait» tag => simp [parsedExprIsL1SharedBlockProducer] at shared
      | noforward => simp [parsedExprIsL1SharedBlockProducer] at shared
      | l2bm l2op => simp [parsedExprIsL1SharedBlockProducer] at shared

theorem parsedExprIsPEInertProducer_stageInput_noforward (expression : ParsedExpr)
    (inert : parsedExprIsPEInertProducer expression = true)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    expression.op = .noforward := by
  rcases parsedExprIsPEInertProducer_cases expression inert with forward | wait | shared
  · exact forward
  · rcases wait with ⟨tag, tagEq⟩
    have tagSome : parsedExprWaitTag? expression = some tag := by
      simp [parsedExprWaitTag?, tagEq]
    have spec := (parsedExprIsIntegerMatrixReadStageInput_spec expression).mp stage
    simp only [parsedExprIntegerMatrixReadStageInputSpec] at spec
    rw [tagSome] at spec
    simp at spec
  · have impossible := l1bmShared_stageInput_false expression shared
    rw [impossible] at stage
    exact Bool.noConfusion stage

/-- A shared-block `.l1bm` row executes as the L1-to-L1 block producer: the
shared-block stage dispatches exactly these five operations to
`executeParsedL1PEToL1Expression` and is the identity on every other row. -/
theorem l1bmShared_sharedBlock_executes (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (shared : parsedExprIsL1SharedBlockProducer expression = true) :
    executeParsedSharedBlockExpression readState currentState expression
        updateTurnaround =
      executeParsedL1PEToL1Expression readState currentState expression
        updateTurnaround := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | l1bm l1op =>
          cases l1op <;> simp [parsedExprIsL1SharedBlockProducer,
            executeParsedSharedBlockExpression] at shared ⊢
      | alu name precision unsigned arg =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | immediate value unsigned => simp [parsedExprIsL1SharedBlockProducer] at shared
      | zero => simp [parsedExprIsL1SharedBlockProducer] at shared
      | mau precision matrix kind half round =>
          simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixWrite precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | matrixRead precision => simp [parsedExprIsL1SharedBlockProducer] at shared
      | «wait» tag => simp [parsedExprIsL1SharedBlockProducer] at shared
      | noforward => simp [parsedExprIsL1SharedBlockProducer] at shared
      | l2bm l2op => simp [parsedExprIsL1SharedBlockProducer] at shared

/-- **A shared-block `.l1bm` row is never the unique `.lm1` writer.**  Its whole
stage preserves every PE register file, so it contributes nothing to the PE 0
`LM1` commit. -/
theorem l1bmShared_row_peRegisters_frame (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockExpression readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters :=
  executeParsedSharedBlockExpression_peRegisters readState currentState next expression
    updateTurnaround executed

/-! ## 3. The stage facts read off a successful `.pe` step

`executeIntegerProducerInstructionLine` has four guards before the stage
pipeline: the issue checker, the pending-wait test, the Rust-unsupported ALU
test and the supported-producer test.  A `.ok` result therefore certifies that
none of the three `.unknown`/`.failure` exits was taken. -/

theorem executeIntegerProducerInstructionLine_pe_waits_complete
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  by_contra h
  rw [Bool.not_eq_false] at h
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, h] at success

theorem executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  have waits := executeIntegerProducerInstructionLine_pe_waits_complete
    normalizedExpressions state next success
  by_contra h
  rw [Bool.not_eq_false] at h
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, waits, h] at success

theorem executeIntegerProducerInstructionLine_pe_supported_of_ok
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  have waits := executeIntegerProducerInstructionLine_pe_waits_complete
    normalizedExpressions state next success
  have noUnsupported := executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok
    normalizedExpressions state next success
  by_contra h
  rw [Bool.not_eq_true] at h
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, waits, noUnsupported, h] at success

/-! ### Stage-selection facts for an all-inert line -/

theorem inert_list_facts (expressions : List ParsedExpr)
    (all : ∀ expression ∈ expressions,
      parsedExprIsPEInertProducer expression = true) :
    expressions.filter parsedExprIsMslMsrProducer = [] ∧
      expressions.filter parsedExprIsFloatReluProducer = [] ∧
      expressions.filter parsedExprIsBlockFloatProducer = [] ∧
      expressions.filter parsedExprIsMatrixMAUProducer = [] ∧
      expressions.any parsedExprIsMatrixWriteProducer = false ∧
      expressions.filter parsedExprIsSupportedFloatMAUProducer = [] ∧
      expressions.filter parsedExprIsL1ToPEProducer = [] ∧
      expressions.any parsedExprIsIntegerBARWriter = false ∧
      (∀ expression ∈ expressions.filter
        parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward) := by
  have facts := fun expression member => parsedExprIsPEInertProducer_facts expression
    (all expression member)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.1]; simp
  · exact List.any_eq_false.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.2.2.1]; simp
  · exact List.any_eq_false.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.2.2.2.2]; simp
  · intro expression member
    exact parsedExprIsPEInertProducer_stageInput_noforward expression
      (all expression (List.mem_filter.mp member).1) (List.mem_filter.mp member).2

/-! ## 4. An all-inert line preserves every PE register file

The integer stage is the only stage that can write a PE register file on an
all-inert line.  Its per-PE core filters the expressions down to
`parsedExprIsIntegerMatrixReadStageInput` rows, which on an inert line are all
`.noforward`; the four-cycle matrix-read preparation of a `.noforward` list is
the identity (`parsedIntegerMatrixReadLineFourCycleStep_noforward`), and the
float-MAU stage has an empty selection. -/

theorem executeIntegerProducerLineAtPECore_peRegisters_of_stageInput_noforward
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (stageAll : ∀ expression ∈ expressions.filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.peRegisters = state.peRegisters := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  rw [parsedIntegerMatrixReadLineFourCycleStep_noforward
    (expressions := expressions.filter parsedExprIsIntegerMatrixReadStageInput)
    (all := stageAll)] at executed
  simp only [] at executed
  rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)] at executed
  simp only [] at executed
  split at executed
  · simp at executed
  · simp at executed
  · simp only [StepResult.ok.injEq] at executed
    subst executed
    funext other
    by_cases h : other = pe <;> simp [h]

theorem executeIntegerProducerLineAtPE_peRegisters_of_inert
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (stageAll : ∀ expression ∈ expressions.filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (noBAR : expressions.any parsedExprIsIntegerBARWriter = false)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.peRegisters = state.peRegisters := by
  unfold executeIntegerProducerLineAtPE at executed
  rw [noBAR] at executed
  simp only [Bool.false_and] at executed
  exact executeIntegerProducerLineAtPECore_peRegisters_of_stageInput_noforward
    expressions state next pe stageAll floatEmpty executed

theorem executeIntegerProducerLineAtPEs_peRegisters_of_inert
    (expressions : List ParsedExpr) (pes : List PEId)
    (stageAll : ∀ expression ∈ expressions.filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (noBAR : expressions.any parsedExprIsIntegerBARWriter = false) :
    ∀ (state next : State),
      executeIntegerProducerLineAtPEs expressions pes state = .ok next →
      next.peRegisters = state.peRegisters := by
  induction pes with
  | nil =>
      intro state next executed
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next executed
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i intermediate headExecuted
        have head := executeIntegerProducerLineAtPE_peRegisters_of_inert expressions
          state intermediate pe stageAll floatEmpty noBAR headExecuted
        have tail := ih intermediate next executed
        exact tail.trans head

/-! ### The whole `.pe` line -/

theorem executeIntegerProducerInstructionLine_pe_peRegisters_of_inert
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    next.peRegisters = state.peRegisters := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  obtain ⟨mslEmpty, reluEmpty, blockEmpty, mauEmpty, noWrite, floatEmpty,
    l1ToPEEmpty, noBAR, stageAll⟩ :=
    inert_list_facts (normalizedExpressions.map NormalizedExpr.toParsed) all
  have supportedAny : normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true := by
    simpa [List.all_map] using
      executeIntegerProducerInstructionLine_pe_supported_of_ok normalizedExpressions
        state next success
  have noUnsupportedAny : normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok normalizedExpressions
        state next success
  have waitsAny : normalizedExpressions.any
      ((parsedExprWaitPending state) ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_waits_complete normalizedExpressions
        state next success
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny] at success
  split at success
  · cases success
  · cases success
  · rename_i nextPEs executed
    rw [executeParsedMslMsrProducers_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mslEmpty] at success
    dsimp only at success
    rw [executeParsedFloatReluProducers_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ reluEmpty] at success
    dsimp only at success
    rw [executeParsedBlockFloatProducer_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ blockEmpty] at success
    dsimp only at success
    rw [executeParsedMatrixMAUAndWrites_id state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mauEmpty noWrite] at success
    dsimp only at success
    split at success
    · cases success
    · cases success
    · rename_i nextWithBlocks sharedExec
      rw [executeParsedL1ToPEProducers_nil state nextWithBlocks
        (normalizedExpressions.map NormalizedExpr.toParsed) _ _ _ l1ToPEEmpty] at success
      dsimp only at success
      simp only [StepResult.ok.injEq] at success
      rw [← success]
      simp only
      rw [executeParsedSharedBlockProducers_peRegisters state nextPEs nextWithBlocks
        (normalizedExpressions.map NormalizedExpr.toParsed) _ sharedExec]
      exact executeIntegerProducerLineAtPEs_peRegisters_of_inert
        ((normalizedExpressions.map NormalizedExpr.toParsed).filter fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression &&
            !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression)
        (List.finRange 4096)
        (fun expression member =>
          stageAll expression
            (List.mem_filter.mpr
              ⟨(List.mem_filter.mp (List.mem_filter.mp member).1).1,
                (List.mem_filter.mp member).2⟩))
        (List.filter_eq_nil_iff.mpr fun expression member => by
          have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
            (List.mem_filter.mp member).1
          have := (List.filter_eq_nil_iff.mp floatEmpty) expression member'
          simpa using this)
        (List.any_eq_false.mpr fun expression member => by
          have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
            (List.mem_filter.mp member).1
          have := (List.any_eq_false.mp noBAR) expression member'
          simpa using this)
        state nextPEs executed

/-! ## 5. An all-inert line writes no PE register, hence satisfies the shape -/

theorem welcomePEInertLine_shape (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true) :
    WelcomePEWriteShape expressions := by
  refine Or.inl ?_
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  have preserved := executeIntegerProducerInstructionLine_pe_peRegisters_of_inert
    expressions (welcomeInitialState welcomeZeroWords) next all executed
  refine ⟨[], ?_, ?_⟩
  · have pointwise := congrFun preserved welcomePE
    simpa [commitParsedMaskedWrites] using pointwise
  · intro write member
    simp at member

/-! ## 6. The corrected aggregate obligation

`WelcomePEOtherShapeObligation` is keyed on `all parsedExprIsPlainIntegerALU =
false`.  By F5 that class is not covered by the six family `Prop`s: it also
contains lines whose non-plain rows are `.noforward`, non-pending `.wait`, or
shared-block `.l1bm` rows, and lines containing special ALU rows
(`msl`/`msr`, float relu, block float).

`WelcomePEGapShapeObligation` below is the seventh `Prop`: it is exactly the
residue "non-plain and no six-family row".  The six family obligations plus the
gap give `WelcomePEOtherShapeObligation`, and with the plain obligation that
gives `WelcomePELm1WriteShapeObligation`. -/

/-- **The seventh obligation (F5).**  Every unrefuted non-plain line that
contains no row of the six families satisfies the write shape. -/
def WelcomePEGapShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixReadProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixMAUProducer = false →
    (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSupportedFloatMAUProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixWriteProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL1ToPEProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL2BMProducer = false →
    WelcomePEWriteShape expressions

/-- **The six family obligations and the gap exhaust the non-plain class.** -/
theorem welcomePEOtherShapeObligation_of_families
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (gap : WelcomePEGapShapeObligation) :
    WelcomePEOtherShapeObligation := by
  intro expressions unrefuted notPlain
  by_cases readAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsMatrixReadProducer = true
  · exact read expressions unrefuted readAny
  by_cases mauAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsMatrixMAUProducer = true
  · exact mau expressions unrefuted mauAny
  by_cases floatAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSupportedFloatMAUProducer = true
  · exact float expressions unrefuted floatAny
  by_cases writeAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsMatrixWriteProducer = true
  · exact write expressions unrefuted writeAny
  by_cases l1Any : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsL1ToPEProducer = true
  · exact l1 expressions unrefuted l1Any
  by_cases l2Any : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsL2BMProducer = true
  · exact l2 expressions unrefuted l2Any
  exact gap expressions unrefuted notPlain
    (by simpa using readAny) (by simpa using mauAny) (by simpa using floatAny)
    (by simpa using writeAny) (by simpa using l1Any) (by simpa using l2Any)

/-- **The corrected aggregate reduction.**  `WelcomePEPlainShapeObligation`, the
six family `Prop`s and the seventh (gap) `Prop` give the exact per-line
write-shape obligation consumed by the value argument. -/
theorem welcomePELm1WriteShapeObligation_of_aggregate
    (plain : WelcomePEPlainShapeObligation)
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (gap : WelcomePEGapShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_two plain
    (welcomePEOtherShapeObligation_of_families read mau float write l1 l2 gap)

/-! ## 7. What the gap still contains, and what is discharged

Inside the gap there are two residual classes:

* lines with a special-ALU row (`msl`/`msr`, a float-relu name, or `bfn`/`bfe`
  block float) — those rows' stages write PE register files, so they need
  their own row analysis;
* *mixed* lines: a plain row together with inert rows.  The unique `.lm1`
  writer is a plain row, but the plain obligation only applies to lines *all*
  of whose rows are plain, so the mixed assembly is still open.

The third gap class — lines all of whose rows are PE-inert — is discharged
here unconditionally by `welcomePEInertLine_shape`. -/

/-- **The special-ALU obligation.**  Every unrefuted line containing an
`msl`/`msr`, float-relu or block-float row satisfies the write shape. -/
def WelcomePESpecialALUShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = true →
    WelcomePEWriteShape expressions

/-- **The mixed plain/inert obligation.**  Every unrefuted non-plain line that
has a plain row and no family or special-ALU row satisfies the write shape. -/
def WelcomePEMixedPlainInertShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
    WelcomePEWriteShape expressions

theorem any_family_false_of_components (expressions : List ParsedExpr)
    (read : expressions.any parsedExprIsMatrixReadProducer = false)
    (mau : expressions.any parsedExprIsMatrixMAUProducer = false)
    (float : expressions.any parsedExprIsSupportedFloatMAUProducer = false)
    (write : expressions.any parsedExprIsMatrixWriteProducer = false)
    (toPE : expressions.any parsedExprIsL1ToPEProducer = false)
    (l2 : expressions.any parsedExprIsL2BMProducer = false) :
    expressions.any parsedExprIsFamilyProducer = false := by
  rw [List.any_eq_false] at *
  intro expression member
  have h1 : parsedExprIsMatrixReadProducer expression = false := by simpa using read expression member
  have h2 : parsedExprIsMatrixMAUProducer expression = false := by simpa using mau expression member
  have h3 : parsedExprIsSupportedFloatMAUProducer expression = false := by
    simpa using float expression member
  have h4 : parsedExprIsMatrixWriteProducer expression = false := by simpa using write expression member
  have h5 : parsedExprIsL1ToPEProducer expression = false := by simpa using toPE expression member
  have h6 : parsedExprIsL2BMProducer expression = false := by simpa using l2 expression member
  simp [parsedExprIsFamilyProducer, h1, h2, h3, h4, h5, h6]

/-- **The gap splits into the special-ALU obligation, the mixed plain/inert
obligation, and the discharged all-inert case.** -/
theorem welcomePEGapShapeObligation_of_special_mixed
    (special : WelcomePESpecialALUShapeObligation)
    (mixed : WelcomePEMixedPlainInertShapeObligation) :
    WelcomePEGapShapeObligation := by
  intro expressions unrefuted notPlain noRead noMau noFloat noWrite noL1 noL2
  by_cases specialAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = true
  · exact special expressions unrefuted specialAny
  by_cases plainAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsPlainIntegerALU = true
  · refine mixed expressions unrefuted notPlain plainAny ?_ (by simpa using specialAny)
    exact any_family_false_of_components _ noRead noMau noFloat noWrite noL1 noL2
  · -- all rows are inert
    have plainFalse : (expressions.map NormalizedExpr.toParsed).any
        parsedExprIsPlainIntegerALU = false := by simpa using plainAny
    have specialFalse : (expressions.map NormalizedExpr.toParsed).any
        parsedExprIsSpecialALUProducer = false := by simpa using specialAny
    have familyFalse : (expressions.map NormalizedExpr.toParsed).any
        parsedExprIsFamilyProducer = false :=
      any_family_false_of_components _ noRead noMau noFloat noWrite noL1 noL2
    have accepted := unrefuted.1
    have supportedAll := accepted.2.2.2
    have noUnsupportedAll := accepted.2.2.1
    refine welcomePEInertLine_shape expressions ?_
    intro expression member
    have supported := List.all_eq_true.mp supportedAll expression member
    have notPlain : parsedExprIsPlainIntegerALU expression = false := by
      simpa using (List.any_eq_false.mp plainFalse) expression member
    have notFamily : parsedExprIsFamilyProducer expression = false := by
      simpa using (List.any_eq_false.mp familyFalse) expression member
    have notSpecial : parsedExprIsSpecialALUProducer expression = false := by
      simpa using (List.any_eq_false.mp specialFalse) expression member
    have notUnsupported : parsedExprIsUnsupportedRustAlu expression = false := by
      simpa using (List.any_eq_false.mp noUnsupportedAll) expression member
    rcases supportedProducer_partition expression supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · rw [notPlain] at isPlain
      cases isPlain
    · rw [notFamily] at isFamily
      cases isFamily
    · rw [notSpecial] at isSpecial
      cases isSpecial
    · exact isInert
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported

/-- **The precise remainder, in one statement.**  The plain obligation, the six
family obligations, the special-ALU obligation and the mixed plain/inert
obligation imply the per-line write-shape obligation.  Everything else that the
old six-family split left open — the all-inert lines with `.noforward`,
non-pending `.wait` or shared-block `.l1bm` rows — is proved outright
(`welcomePEInertLine_shape`). -/
theorem welcomePELm1WriteShapeObligation_of_nine
    (plain : WelcomePEPlainShapeObligation)
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (special : WelcomePESpecialALUShapeObligation)
    (mixed : WelcomePEMixedPlainInertShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_aggregate plain read mau float write l1 l2
    (welcomePEGapShapeObligation_of_special_mixed special mixed)
