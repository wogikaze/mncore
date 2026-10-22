import ProofsLean.WelcomeWriterDispatch
import ProofsLean.WelcomeL1MultiDest
import ProofsLean.WelcomeValueBound
import ProofsLean.WelcomeResiduals
import ProofsLean.WelcomeWholeMachineOptimal

/-! # Generic lower-bound API for MN-Core problem tracks

This module is the reusable skeleton of the Welcome optimality chain.  It adds
**no new mathematics about the Welcome answer**: every theorem below is either

* a re-export of an existing problem-independent theorem under a stable name in
  `ProofsLean.MNCore.Generic`, or
* a short generic corollary obtained by abstracting the problem-specific parts
  (`Welcome`/`1.a-b`/`4.mul7`) as parameters.

Nothing in the existing tree is edited, and no proof is copied: the underlying
proofs stay in their original modules and are imported here.

## Contents

1. **Sealed value machine and the no-one-line skeleton** (§1).  A problem on the
   sealed whole-machine value model is `sealedProblem admissible initial post`;
   `lowerBound_two_iff_rejects_unit_lines` is the exact bound-2 reduction (and
   `lowerBound_two_iff_rejects_short_lines` its `< 2` form), while
   `lowerBound_two_iff_residual` is the residual-class form (the generic form of
   `abLowerBound_two_iff_residual`).  `OneLineRefutation` is the per-line
   "witness input + value argument" package.
2. **The `.lm1` write-shape algebra** (§2): `Lm1WritesShape`, its append laws,
   the six-block positional corollaries, the `.lm1`-filter characterisation, and
   the `Lm1FreeWrites` algebra, all re-exported.
3. **Hazard-aware projection** (§3): `executeHazardAwareNormalizedLine_ok_project`
   and its core form, plus generic program projection and the one-line
   sealed-correctness/lower-bound transfer for the total hazard machine.
4. **The certificate obstruction** (§4): any `SymbolicBoundCertificate` at bound
   two must contain (and reject) *every* legal unit-cost line, so its `contains`
   cannot be a problem-specific class.
5. **Value-argument kernel** (§5, optional): the window-counting and
   untouched-word lemmas used by the Welcome value argument.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  No existing module is
edited.
-/

namespace ProofsLean.MNCore.Generic

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open ProofsLean.MNCore
open ProofsLean.MNCore.Issue
open ProofsLean.MNCore.PEMemory

/-! ## 0. Re-exported vocabulary -/

/-- The generic machine interface. -/
abbrev Machine := ProofsLean.Machine

/-- The generic problem interface. -/
abbrev Problem := ProofsLean.Problem

/-- A program is a list of issue lines. -/
abbrev Program (m : Machine) := ProofsLean.Program m

/-- Correctness: legality plus every admissible input runs and meets the post. -/
abbrev Correct := ProofsLean.Correct

/-- A semantic refutation by one concrete input. -/
abbrev Refutes := ProofsLean.Refutes

/-- The lower-bound predicate. -/
abbrev LowerBound := ProofsLean.LowerBound

/-- A witness program together with correctness and a matching lower bound. -/
abbrev Optimal := ProofsLean.Optimal

/-- The symbolic certificate interface of `Optimality.lean`. -/
abbrev SymbolicBoundCertificate := ProofsLean.SymbolicBoundCertificate

/-- The concrete enumeration certificate interface. -/
abbrev BoundCertificate := ProofsLean.BoundCertificate

/-! ## 1. The sealed value machine and the no-one-line skeleton -/

/-- The sealed whole-machine value model used by the Welcome, `1.a-b` and
`4.mul7` tracks: lines are `InstructionLine`s, the state is the real `State`,
and a step is `executeNormalizedLine` with `failure`/`unknown` sealed to `none`.

`Input` is the problem's input type; legality is unrestricted.  This is exactly
the shape of `welcomeSealedMachine`, `abSealedMachine` and `mul7SealedMachine`,
so a new value-model problem only supplies its input type and spec. -/
noncomputable def sealedMachine (Input : Type) : Machine where
  Line := InstructionLine
  State := State
  Input := Input
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- A problem on the sealed value machine, from its three problem-specific
components.  This is the generic form of `welcomeSpec`, `abSpec` and
`mul7Spec`. -/
noncomputable def sealedProblem (Input : Type) (admissible : Input → Prop)
    (initial : Input → State) (post : Input → State → Prop) :
    Problem (sealedMachine Input) where
  admissible := admissible
  initial := initial
  post := post

@[simp] theorem sealedProblem_admissible (Input : Type) (admissible : Input → Prop)
    (initial : Input → State) (post : Input → State → Prop) (input : Input) :
    (sealedProblem Input admissible initial post).admissible input ↔ admissible input :=
  Iff.rfl

@[simp] theorem sealedProblem_initial (Input : Type) (admissible : Input → Prop)
    (initial : Input → State) (post : Input → State → Prop) (input : Input) :
    (sealedProblem Input admissible initial post).initial input = initial input :=
  rfl

@[simp] theorem sealedProblem_post (Input : Type) (admissible : Input → Prop)
    (initial : Input → State) (post : Input → State → Prop) (input : Input)
    (state : State) :
    (sealedProblem Input admissible initial post).post input state = post input state :=
  rfl

/-- The score of the sealed machine is the line cost of one-line programs. -/
@[simp] theorem sealedMachine_score_singleton (Input : Type) (line : InstructionLine) :
    ProofsLean.score (sealedMachine Input) [line] = InstructionLine.cost line :=
  rfl

/-- **A program of score zero is empty.**  Only `positiveCost` is used. -/
theorem score_eq_zero_iff (m : Machine) (program : Program m) :
    ProofsLean.score m program = 0 ↔ program = [] := by
  constructor
  · cases program with
    | nil => intro _; rfl
    | cons line rest =>
        intro h
        have positive := m.positiveCost line
        simp only [ProofsLean.score] at h
        omega
  · intro h
    rw [h]
    rfl

/-- **The shape of a program of score below two**: it is empty or one unit-cost
line.  Only `positiveCost` is used. -/
theorem score_lt_two_iff (m : Machine) (program : Program m) :
    ProofsLean.score m program < 2 ↔
      program = [] ∨ ∃ line : m.Line, program = [line] ∧ m.lineCost line = 1 := by
  constructor
  · intro h
    cases program with
    | nil => exact Or.inl rfl
    | cons line rest =>
        right
        have positive := m.positiveCost line
        have scoreEq : ProofsLean.score m (line :: rest) =
            m.lineCost line + ProofsLean.score m rest := rfl
        have restZero : ProofsLean.score m rest = 0 := by
          rw [scoreEq] at h
          omega
        have restEmpty : rest = [] := (score_eq_zero_iff m rest).mp restZero
        subst rest
        refine ⟨line, rfl, ?_⟩
        rw [scoreEq] at h
        simp only [ProofsLean.score] at h
        omega
  · intro h
    rcases h with rfl | ⟨line, rfl, costOne⟩
    · simp [ProofsLean.score]
    · simp only [ProofsLean.score, costOne, Nat.add_zero]
      omega

/-- **The generic no-one-line skeleton.**  For a machine whose scores are
positive, a bound of two is exactly the statement that no one-line program of
cost one is correct.  The empty program must be refuted separately (it is the
only program of score zero).  This is `welcomeLowerBound_two_iff_rejects_short_lines`
and the trivial direction of `abLowerBound_two_iff_rejects_short_lines`,
abstracted from the concrete machine and spec. -/
theorem lowerBound_two_iff_rejects_unit_lines (m : Machine) (spec : Problem m)
    (emptyIncorrect : ¬ Correct m spec []) :
    LowerBound m spec 2 ↔
      ∀ line : m.Line, m.lineCost line = 1 → ¬ Correct m spec [line] := by
  constructor
  · intro lower line costOne correct
    have bound := lower [line] correct
    have scoreEq : ProofsLean.score m [line] = m.lineCost line := rfl
    rw [scoreEq, costOne] at bound
    omega
  · intro rejects program correct
    by_contra notBound
    have short : ProofsLean.score m program < 2 := by omega
    rcases (score_lt_two_iff m program).mp short with rfl | ⟨line, rfl, costOne⟩
    · exact emptyIncorrect correct
    · exact rejects line costOne correct

/-- **The short-line form of the no-one-line skeleton.**  This is the exact
shape of `welcomeLowerBound_two_iff_rejects_short_lines` (and the `.pe` part of
the `1.a-b` reduction), with `lineCost < 2` in place of `lineCost = 1`.  The two
forms are equivalent by `positiveCost`. -/
theorem lowerBound_two_iff_rejects_short_lines (m : Machine) (spec : Problem m)
    (emptyIncorrect : ¬ Correct m spec []) :
    LowerBound m spec 2 ↔
      ∀ line : m.Line, m.lineCost line < 2 → ¬ Correct m spec [line] := by
  rw [lowerBound_two_iff_rejects_unit_lines m spec emptyIncorrect]
  constructor
  · intro refuted line short
    exact refuted line (by have := m.positiveCost line; omega)
  · intro refuted line unit
    exact refuted line (by omega)

/-- **Lower bound two from the residual class** (the generic
`abLowerBound_two_of_residual`). -/
theorem lowerBound_two_of_residual (m : Machine) (spec : Problem m)
    {ι : Type} (lineOf : ι → m.Line)
    (emptyIncorrect : ¬ Correct m spec [])
    (outsideRefuted : ∀ line : m.Line, m.lineCost line = 1 →
      (∀ i, line ≠ lineOf i) → ¬ Correct m spec [line])
    (residualRefuted : ∀ i, ¬ Correct m spec [lineOf i]) :
    LowerBound m spec 2 := by
  rw [lowerBound_two_iff_rejects_unit_lines m spec emptyIncorrect]
  intro line costOne correct
  by_cases member : ∃ i, line = lineOf i
  · obtain ⟨i, rfl⟩ := member
    exact residualRefuted i correct
  · exact outsideRefuted line costOne (fun i same => member ⟨i, same⟩) correct

/-- **The residual-class form of the bound-2 reduction.**  A new problem
indexes its residual one-line family by `lineOf : ι → m.Line` (for the
`.pe`-line residual classes, `ι = List NormalizedExpr` and
`lineOf expressions = .pe expressions`), proves that every residual line has
cost one, refutes every unit-cost line outside the family syntactically, and
refutes the residual family by its value argument.  The equivalence is the
generic form of `abLowerBound_two_iff_residual`.

The forward direction needs only the cost fact; the backward direction is
`lowerBound_two_of_residual`. -/
theorem lowerBound_two_iff_residual (m : Machine) (spec : Problem m)
    {ι : Type} (lineOf : ι → m.Line) (unit : ∀ i, m.lineCost (lineOf i) = 1)
    (emptyIncorrect : ¬ Correct m spec [])
    (outsideRefuted : ∀ line : m.Line, m.lineCost line = 1 →
      (∀ i, line ≠ lineOf i) → ¬ Correct m spec [line]) :
    LowerBound m spec 2 ↔ ∀ i, ¬ Correct m spec [lineOf i] := by
  constructor
  · intro lower i correct
    have bound := lower [lineOf i] correct
    have scoreEq : ProofsLean.score m [lineOf i] = m.lineCost (lineOf i) := rfl
    rw [scoreEq, unit i] at bound
    omega
  · intro residualRefuted
    exact lowerBound_two_of_residual m spec lineOf emptyIncorrect
      outsideRefuted residualRefuted

/-- A per-line refutation package: the problem supplies a witness input and the
value argument that no run of the one-line program at that input meets the
postcondition.  This is the "new problem only supplies its spec, its witness
input and its value argument" interface. -/
structure OneLineRefutation (m : Machine) (spec : Problem m) (line : m.Line) where
  /-- The witness input at which the line fails. -/
  input : m.Input
  /-- The witness is admissible. -/
  admissible : spec.admissible input
  /-- No run of `[line]` from the witness satisfies the postcondition. -/
  refuted : ¬ ∃ result,
    ProofsLean.execute m [line] (spec.initial input) = some result ∧
      spec.post input result

/-- A `OneLineRefutation` is a semantic refutation, hence the line is not
correct. -/
theorem OneLineRefutation.not_correct {m : Machine} {spec : Problem m}
    {line : m.Line} (refutation : OneLineRefutation m spec line) :
    ¬ Correct m spec [line] :=
  ProofsLean.refutes_not_correct ⟨refutation.admissible, refutation.refuted⟩

/-- **Bound two from per-line witness refutations.**  This is the most
instantiation-friendly entry point: prove the empty program incorrect and, for
every unit-cost line, exhibit one witness input and its value argument. -/
theorem lowerBound_two_of_oneLineRefutations (m : Machine) (spec : Problem m)
    (emptyIncorrect : ¬ Correct m spec [])
    (refutes : ∀ line : m.Line, m.lineCost line = 1 →
      OneLineRefutation m spec line) :
    LowerBound m spec 2 := by
  rw [lowerBound_two_iff_rejects_unit_lines m spec emptyIncorrect]
  intro line costOne
  exact (refutes line costOne).not_correct

/-- Residual form of `lowerBound_two_of_oneLineRefutations`. -/
theorem lowerBound_two_of_residual_oneLineRefutations (m : Machine) (spec : Problem m)
    {ι : Type} (lineOf : ι → m.Line)
    (emptyIncorrect : ¬ Correct m spec [])
    (outsideRefuted : ∀ line : m.Line, m.lineCost line = 1 →
      (∀ i, line ≠ lineOf i) → OneLineRefutation m spec line)
    (residualRefuted : ∀ i, OneLineRefutation m spec (lineOf i)) :
    LowerBound m spec 2 :=
  lowerBound_two_of_residual m spec lineOf emptyIncorrect
    (fun line costOne outside => (outsideRefuted line costOne outside).not_correct)
    (fun i => (residualRefuted i).not_correct)

/-- **The sealed-machine specialization of the no-one-line skeleton.** -/
theorem sealedLowerBound_two_iff_rejects_unit_lines {Input : Type}
    {admissible : Input → Prop} {initial : Input → State}
    {post : Input → State → Prop}
    (emptyIncorrect : ¬ Correct (sealedMachine Input)
      (sealedProblem Input admissible initial post) []) :
    LowerBound (sealedMachine Input) (sealedProblem Input admissible initial post) 2 ↔
      ∀ line : InstructionLine, InstructionLine.cost line = 1 →
        ¬ Correct (sealedMachine Input)
          (sealedProblem Input admissible initial post) [line] :=
  lowerBound_two_iff_rejects_unit_lines _ _ emptyIncorrect

/-- **The sealed-machine specialization of the witness/value-argument entry
point.** -/
theorem sealedLowerBound_two_of_oneLineRefutations {Input : Type}
    {admissible : Input → Prop} {initial : Input → State}
    {post : Input → State → Prop}
    (emptyIncorrect : ¬ Correct (sealedMachine Input)
      (sealedProblem Input admissible initial post) [])
    (refutes : ∀ line : InstructionLine, InstructionLine.cost line = 1 →
      OneLineRefutation (sealedMachine Input)
        (sealedProblem Input admissible initial post) line) :
    LowerBound (sealedMachine Input) (sealedProblem Input admissible initial post) 2 :=
  lowerBound_two_of_oneLineRefutations _ _ emptyIncorrect refutes

/-- **The empty program on the sealed machine.**  It is incorrect as soon as one
admissible input fails the postcondition at the initial state.  Every problem
needs this small lemma; it is generic because `execute` on `[]` is the identity.
-/
theorem sealed_empty_not_correct {Input : Type}
    {admissible : Input → Prop} {initial : Input → State}
    {post : Input → State → Prop}
    (witness : ∃ input : Input, admissible input ∧ ¬ post input (initial input)) :
    ¬ Correct (sealedMachine Input) (sealedProblem Input admissible initial post) [] := by
  intro correct
  obtain ⟨input, admissibleH, postFail⟩ := witness
  obtain ⟨result, run, resultPost⟩ := correct.2 input admissibleH
  simp only [ProofsLean.execute, sealedProblem] at run
  cases run
  exact postFail resultPost

/-! ## 2. The `.lm1` write-shape algebra

The definitions stay in `WelcomeWriterDispatch`/`WelcomeValueBound`; this
section only gives them stable names in `Generic` and re-exports the
problem-independent algebra.  Nothing here mentions a Welcome input, state or
answer: the predicates quantify over `PreparedParsedMaskedWrite` lists. -/

/-- One prepared PE write: destination, mask update, data bus and word
selection. -/
abbrev PreparedWrite := ProofsLean.MNCore.PEMemory.PreparedParsedMaskedWrite

/-- The `.lm1` bank test of a prepared write. -/
abbrev IsLm1Write (write : PreparedWrite) : Bool :=
  ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write

/-- A prepared-write list prepares no bank-`.lm1` word. -/
abbrev Lm1FreeWrites := ProofsLean.MNCore.Lm1FreePreparedWrites

/-- Every `.lm1` destination is a 4-aligned `.double` block whose third data
word is a copy. -/
abbrev Lm1WritesDoubleCopy := ProofsLean.MNCore.Lm1WritesDoubleCopy

/-- The `.lm1` destinations lie in at most four windows of at most two words. -/
abbrev Lm1WritesNarrow := ProofsLean.MNCore.Lm1WritesNarrow

/-- The `.lm1` shape disjunction consumed by the value argument. -/
abbrev Lm1WritesShape := ProofsLean.MNCore.Lm1WritesShape

/-- A write whose destination is `some ⟨.lm1, …⟩` passes the `.lm1` test. -/
theorem isLm1Write_of_destination_lm1 (write : PreparedWrite)
    (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity)
    (destination : write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩) :
    IsLm1Write write = true :=
  ProofsLean.MNCore.isLm1Write_of_destination_lm1 write width address destination

/-- The `Lm1FreeWrites` predicate is the requested `isLm1Write = false` form. -/
theorem lm1FreeWrites_iff (writes : List PreparedWrite) :
    Lm1FreeWrites writes ↔
      ∀ write ∈ writes, IsLm1Write write = false :=
  Iff.rfl

/-- The empty write list is `.lm1`-free. -/
theorem lm1FreeWrites_nil : Lm1FreeWrites [] :=
  ProofsLean.MNCore.lm1FreePreparedWrites_nil

/-- `.lm1`-freeness is stable under concatenation. -/
theorem lm1FreeWrites_append {head tail : List PreparedWrite}
    (headFree : Lm1FreeWrites head) (tailFree : Lm1FreeWrites tail) :
    Lm1FreeWrites (head ++ tail) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_append headFree tailFree

/-- Freeness of a two-block concatenation. -/
theorem lm1FreeWrites_two (a b : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) :
    Lm1FreeWrites (a ++ b) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_two a b ha hb

/-- Freeness of a right-associated three-block concatenation. -/
theorem lm1FreeWrites_three (a b c : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c) :
    Lm1FreeWrites (a ++ (b ++ c)) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_three a b c ha hb hc

/-- Freeness of a right-associated four-block concatenation. -/
theorem lm1FreeWrites_four (a b c d : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b)
    (hc : Lm1FreeWrites c) (hd : Lm1FreeWrites d) :
    Lm1FreeWrites (a ++ (b ++ (c ++ d))) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_four a b c d ha hb hc hd

/-- Freeness of a right-associated five-block concatenation. -/
theorem lm1FreeWrites_five (a b c d e : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c)
    (hd : Lm1FreeWrites d) (he : Lm1FreeWrites e) :
    Lm1FreeWrites (a ++ (b ++ (c ++ (d ++ e)))) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_five a b c d e ha hb hc hd he

/-- Freeness of a left-associated six-block concatenation. -/
theorem lm1FreeWrites_six (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c)
    (hd : Lm1FreeWrites d) (he : Lm1FreeWrites e) (hf : Lm1FreeWrites f) :
    Lm1FreeWrites (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1FreePreparedWrites_six a b c d e f ha hb hc hd he hf

/-- A list of `.lm1`-free writes satisfies the `.double` copy shape
vacuously. -/
theorem lm1WritesDoubleCopy_of_free (writes : List PreparedWrite)
    (free : Lm1FreeWrites writes) : Lm1WritesDoubleCopy writes :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_of_free writes free

/-- A list of `.lm1`-free writes satisfies the narrow shape vacuously. -/
theorem lm1WritesNarrow_of_free (writes : List PreparedWrite)
    (free : Lm1FreeWrites writes) : Lm1WritesNarrow writes :=
  ProofsLean.MNCore.lm1WritesNarrow_of_free writes free

/-- A list of `.lm1`-free writes satisfies the shape disjunction vacuously. -/
theorem lm1WritesShape_of_free (writes : List PreparedWrite)
    (free : Lm1FreeWrites writes) : Lm1WritesShape writes :=
  Or.inl (lm1WritesDoubleCopy_of_free writes free)

/-- A `.double` block is shaped. -/
theorem lm1WritesShape_of_double {writes : List PreparedWrite}
    (shape : Lm1WritesDoubleCopy writes) : Lm1WritesShape writes :=
  ProofsLean.MNCore.lm1WritesShape_of_double shape

/-- A narrow block is shaped. -/
theorem lm1WritesShape_of_narrow {writes : List PreparedWrite}
    (shape : Lm1WritesNarrow writes) : Lm1WritesShape writes :=
  ProofsLean.MNCore.lm1WritesShape_of_narrow shape

/-- A shaped block followed by an `.lm1`-free block is shaped. -/
theorem lm1WritesDoubleCopy_append_of_only (first second : List PreparedWrite)
    (shape : Lm1WritesDoubleCopy first)
    (only : ∀ write ∈ second, IsLm1Write write = false) :
    Lm1WritesDoubleCopy (first ++ second) :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_append_of_only first second shape only

/-- An `.lm1`-free block followed by a shaped block is shaped. -/
theorem lm1WritesDoubleCopy_append_of_only_right (first second : List PreparedWrite)
    (shape : Lm1WritesDoubleCopy second)
    (only : ∀ write ∈ first, IsLm1Write write = false) :
    Lm1WritesDoubleCopy (first ++ second) :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_append_of_only_right first second shape only

/-- A narrow block followed by an `.lm1`-free block is narrow. -/
theorem lm1WritesNarrow_append_of_only (first second : List PreparedWrite)
    (shape : Lm1WritesNarrow first)
    (only : ∀ write ∈ second, IsLm1Write write = false) :
    Lm1WritesNarrow (first ++ second) :=
  ProofsLean.MNCore.lm1WritesNarrow_append_of_only first second shape only

/-- An `.lm1`-free block followed by a narrow block is narrow. -/
theorem lm1WritesNarrow_append_of_only_right (first second : List PreparedWrite)
    (shape : Lm1WritesNarrow second)
    (only : ∀ write ∈ first, IsLm1Write write = false) :
    Lm1WritesNarrow (first ++ second) :=
  ProofsLean.MNCore.lm1WritesNarrow_append_of_only_right first second shape only

/-- The shape disjunction is stable under appending `.lm1`-free blocks. -/
theorem lm1WritesShape_append_of_only (first second : List PreparedWrite)
    (only : ∀ write ∈ second, IsLm1Write write = false)
    (shape : Lm1WritesShape first) :
    Lm1WritesShape (first ++ second) :=
  ProofsLean.MNCore.lm1WritesShape_append_of_only first second only shape

/-- The shape disjunction is stable under prepending `.lm1`-free blocks. -/
theorem lm1WritesShape_append_of_only_right (first second : List PreparedWrite)
    (only : ∀ write ∈ first, IsLm1Write write = false)
    (shape : Lm1WritesShape second) :
    Lm1WritesShape (first ++ second) :=
  ProofsLean.MNCore.lm1WritesShape_append_of_only_right first second only shape

/-- **An `.lm1`-free prefix and suffix leave the shape to the middle block.** -/
theorem lm1WritesShape_append_free_split (leading middle trailing : List PreparedWrite)
    (freeLeading : Lm1FreeWrites leading)
    (shapeMiddle : Lm1WritesShape middle)
    (freeTrailing : Lm1FreeWrites trailing) :
    Lm1WritesShape (leading ++ (middle ++ trailing)) :=
  ProofsLean.MNCore.lm1WritesShape_append_free_split leading middle trailing
    freeLeading shapeMiddle freeTrailing

/-- **The shape of a concatenation from a split into three blocks.** -/
theorem lm1WritesShape_of_append_split {writes leading middle trailing :
      List PreparedWrite}
    (split : writes = leading ++ (middle ++ trailing))
    (freeLeading : Lm1FreeWrites leading)
    (shapeMiddle : Lm1WritesShape middle)
    (freeTrailing : Lm1FreeWrites trailing) :
    Lm1WritesShape writes :=
  ProofsLean.MNCore.lm1WritesShape_of_append_split split freeLeading shapeMiddle
    freeTrailing

/-- The first block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_first (a b c d e f : List PreparedWrite)
    (shape : Lm1WritesShape a)
    (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c) (hd : Lm1FreeWrites d)
    (he : Lm1FreeWrites e) (hf : Lm1FreeWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_first a b c d e f shape hb hc hd he hf

/-- The second block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_second (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (shape : Lm1WritesShape b)
    (hc : Lm1FreeWrites c) (hd : Lm1FreeWrites d)
    (he : Lm1FreeWrites e) (hf : Lm1FreeWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_second a b c d e f ha shape hc hd he hf

/-- The third block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_third (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (shape : Lm1WritesShape c)
    (hd : Lm1FreeWrites d) (he : Lm1FreeWrites e) (hf : Lm1FreeWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_third a b c d e f ha hb shape hd he hf

/-- The fourth block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_fourth (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c)
    (shape : Lm1WritesShape d) (he : Lm1FreeWrites e) (hf : Lm1FreeWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_fourth a b c d e f ha hb hc shape he hf

/-- The fifth block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_fifth (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c)
    (hd : Lm1FreeWrites d) (shape : Lm1WritesShape e) (hf : Lm1FreeWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_fifth a b c d e f ha hb hc hd shape hf

/-- The sixth block of the six-stage concatenation is the writer's. -/
theorem lm1WritesShape_of_six_sixth (a b c d e f : List PreparedWrite)
    (ha : Lm1FreeWrites a) (hb : Lm1FreeWrites b) (hc : Lm1FreeWrites c)
    (hd : Lm1FreeWrites d) (he : Lm1FreeWrites e) (shape : Lm1WritesShape f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) :=
  ProofsLean.MNCore.lm1WritesShape_of_six_sixth a b c d e f ha hb hc hd he shape

/-! ### The `.lm1` filter characterisation

Both shapes only constrain `.lm1` destinations, so they are statements about
`writes.filter isLm1Write`.  The commit has the same property
(`commit_lm1_filter`).  These are the re-exports used by the multi-destination
L1 rows, where `.lm1`-free write lists are spliced between the `.lm1` writes. -/

/-- The commit only reads the `.lm1` writes of the list. -/
theorem commit_lm1_filter (files : PEMemory.IntegerRegisterFiles)
    (writes : List PreparedWrite) :
    (commitParsedMaskedWrites files writes).lm1 =
      (commitParsedMaskedWrites files
        (writes.filter IsLm1Write)).lm1 :=
  ProofsLean.MNCore.commitParsedMaskedWrites_lm1_filter files writes

/-- The shape holds on the `.lm1` filter whenever it holds on the list. -/
theorem lm1WritesDoubleCopy_filter (writes : List PreparedWrite)
    (shape : Lm1WritesDoubleCopy writes) :
    Lm1WritesDoubleCopy (writes.filter IsLm1Write) :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_filter writes shape

/-- Conversely, a shape on the `.lm1` filter lifts to the whole list. -/
theorem lm1WritesDoubleCopy_of_filter (writes : List PreparedWrite)
    (shape : Lm1WritesDoubleCopy (writes.filter IsLm1Write)) :
    Lm1WritesDoubleCopy writes :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_of_filter writes shape

/-- The narrow shape holds on the `.lm1` filter whenever it holds on the list. -/
theorem lm1WritesNarrow_filter (writes : List PreparedWrite)
    (shape : Lm1WritesNarrow writes) :
    Lm1WritesNarrow (writes.filter IsLm1Write) :=
  ProofsLean.MNCore.lm1WritesNarrow_filter writes shape

/-- Conversely, a narrow shape on the `.lm1` filter lifts to the whole list. -/
theorem lm1WritesNarrow_of_filter (writes : List PreparedWrite)
    (shape : Lm1WritesNarrow (writes.filter IsLm1Write)) :
    Lm1WritesNarrow writes :=
  ProofsLean.MNCore.lm1WritesNarrow_of_filter writes shape

/-- The `.double` shape is equivalent to its `.lm1`-filtered form. -/
theorem lm1WritesDoubleCopy_iff_filter (writes : List PreparedWrite) :
    Lm1WritesDoubleCopy writes ↔
      Lm1WritesDoubleCopy (writes.filter IsLm1Write) :=
  ProofsLean.MNCore.lm1WritesDoubleCopy_iff_filter writes

/-- The narrow shape is equivalent to its `.lm1`-filtered form. -/
theorem lm1WritesNarrow_iff_filter (writes : List PreparedWrite) :
    Lm1WritesNarrow writes ↔
      Lm1WritesNarrow (writes.filter IsLm1Write) :=
  ProofsLean.MNCore.lm1WritesNarrow_iff_filter writes

/-- The disjunction is stable under `.lm1`-filtering. -/
theorem lm1WritesShape_filter (writes : List PreparedWrite)
    (shape : Lm1WritesShape writes) :
    Lm1WritesShape (writes.filter IsLm1Write) := by
  rcases shape with double | narrow
  · exact Or.inl (lm1WritesDoubleCopy_filter writes double)
  · exact Or.inr (lm1WritesNarrow_filter writes narrow)

/-- The disjunction lifts from its `.lm1`-filtered form. -/
theorem lm1WritesShape_of_filter (writes : List PreparedWrite)
    (shape : Lm1WritesShape (writes.filter IsLm1Write)) :
    Lm1WritesShape writes := by
  rcases shape with double | narrow
  · exact Or.inl (lm1WritesDoubleCopy_of_filter writes double)
  · exact Or.inr (lm1WritesNarrow_of_filter writes narrow)

/-- The shape disjunction is equivalent to its `.lm1`-filtered form. -/
theorem lm1WritesShape_iff_filter (writes : List PreparedWrite) :
    Lm1WritesShape writes ↔
      Lm1WritesShape (writes.filter IsLm1Write) :=
  ⟨lm1WritesShape_filter writes, lm1WritesShape_of_filter writes⟩

/-- The `.lm1` filter of an `.lm1`-free list is empty. -/
theorem filter_isLm1Write_eq_nil (writes : List PreparedWrite)
    (free : Lm1FreeWrites writes) :
    writes.filter IsLm1Write = [] :=
  ProofsLean.MNCore.filter_isLm1Write_eq_nil writes free

/-- The `.lm1` filter of `pre ++ [write] ++ post` is `[write]` when `write` is
an `.lm1` write and `pre`/`post` are `.lm1`-free. -/
theorem filter_isLm1Write_split (pre post : List PreparedWrite)
    (write : PreparedWrite)
    (writeLm1 : IsLm1Write write = true)
    (preFree : Lm1FreeWrites pre) (postFree : Lm1FreeWrites post) :
    (pre ++ [write] ++ post).filter IsLm1Write = [write] :=
  ProofsLean.MNCore.filter_isLm1Write_split pre post write writeLm1 preFree postFree

/-! ## 3. Hazard-aware projection

A successful hazard-aware step is the sealed value step on `state.machine`
(`executeHazardAwareNormalizedLine_ok_project`).  This is the generic bridge used
by every problem to transfer a sealed-machine lower bound to the hazard-aware
machine.  The two projection theorems are re-exported verbatim; the
program/one-line corollaries below are generic and are the only proof work added
here. -/

/-- The hazard-aware state. -/
abbrev HazardState := HazardAwareState

/-- **Value projection of the core transition.**  A successful
`executeHazardAwareNormalizedLineCore` step projects to a successful sealed step
with the same machine payload and does not change the stalled-issue marker. -/
theorem executeHazardAwareNormalizedLineCore_ok_project
    (line : NormalizedLine) (state next : HazardAwareState)
    (success : executeHazardAwareNormalizedLineCore line state = .ok next) :
    executeNormalizedLine line state.machine = .ok next.machine ∧
      next.stalledPEIssue = state.stalledPEIssue :=
  ProofsLean.MNCore.executeHazardAwareNormalizedLineCore_ok_project line state next success

/-- **Value projection of the wrapper transition.**  On a non-stalled state and
a line without a wait tag, a successful hazard-aware step is a successful sealed
step with the same machine payload, and leaves the state unstalled. -/
theorem executeHazardAwareNormalizedLine_ok_project
    (line : NormalizedLine) (state next : HazardAwareState)
    (notStalled : state.stalledPEIssue = none)
    (noWait : normalizedLineWaitTag? line = none)
    (success : executeHazardAwareNormalizedLine line state = .ok next) :
    executeNormalizedLine line state.machine = .ok next.machine ∧
      next.stalledPEIssue = none :=
  ProofsLean.MNCore.executeHazardAwareNormalizedLine_ok_project line state next
    notStalled noWait success

/-- The total presentation of the hazard-aware whole machine:
`.ok ↦ some`, `.failure`/`.unknown ↦ none`.  This is the generic form of
`welcomeWholeMachine` (the `Input` field is the only difference). -/
noncomputable def hazardMachine (Input : Type) : Machine where
  Line := InstructionLine
  State := HazardAwareState
  Input := Input
  step := welcomeWholeMachine.step
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- A successful total hazard step came from a successful `.ok` partial step. -/
theorem hazardMachine_step_ok {Input : Type} {line : InstructionLine}
    {state next : HazardAwareState}
    (success : (hazardMachine Input).step line state = some next) :
    wholeMachine.step line state = .ok next := by
  have success' : welcomeWholeMachine.step line state = some next := by
    simpa [hazardMachine, welcomeWholeMachine] using success
  exact ProofsLean.MNCore.welcomeWholeMachine_step_ok success'

/-- A successful total hazard step is, definitionally, the hazard-aware wrapper
step. -/
theorem hazardMachine_step_eq {Input : Type} (line : InstructionLine)
    (state : HazardAwareState) :
    (hazardMachine Input).step line state =
      match executeHazardAwareNormalizedLine line.toNormalizedLine state with
      | .ok next => some next
      | .failure => none
      | .unknown => none :=
  rfl

/-- **Program projection.**  A successful hazard-aware run of a wait-tag-free
program from a non-stalled state is a successful sealed run from
`state.machine`, with the same final machine payload.  This is the generic
`welcomeWholeExecute_project`. -/
theorem hazardExecute_project {Input : Type} (program : List InstructionLine)
    (noWait : ∀ line ∈ program, normalizedLineWaitTag? line.toNormalizedLine = none) :
    ∀ (state result : HazardAwareState), state.stalledPEIssue = none →
      ProofsLean.execute (hazardMachine Input) program state = some result →
      ProofsLean.execute (sealedMachine Input) program state.machine = some result.machine := by
  induction program with
  | nil =>
      intro state result _notStalled run
      simp only [ProofsLean.execute, Option.some.injEq] at run
      cases run
      rfl
  | cons line rest ih =>
      intro state result notStalled run
      simp only [ProofsLean.execute] at run
      cases step : (hazardMachine Input).step line state with
      | none => rw [step] at run; cases run
      | some mid =>
          rw [step] at run
          have partialOk : wholeMachine.step line state = .ok mid :=
            hazardMachine_step_ok step
          have projected :=
            ProofsLean.MNCore.executeHazardAwareNormalizedLine_ok_project
              line.toNormalizedLine state mid notStalled (noWait line (by simp))
              (show executeHazardAwareNormalizedLine line.toNormalizedLine state = .ok mid
                from partialOk)
          have sealedStep : (sealedMachine Input).step line state.machine =
              some mid.machine := by
            simp only [sealedMachine]
            rw [projected.1]
          have tail := ih (fun restLine member => noWait restLine (by simp [member]))
            mid result projected.2 run
          simp only [ProofsLean.execute, sealedStep]
          exact tail

/-- A wait-tagged line is never a successful step from `initial`.  A problem
whose hazard initial state has no pending MV transfers discharges this from the
initial-state analysis (as `welcomeWhole_initial_step_project` does). -/
def HazardInitialNoWait {Input : Type} (initial : Input → HazardAwareState) : Prop :=
  ∀ (input : Input) (line : InstructionLine) (tag : Fin 256),
    normalizedLineWaitTag? line.toNormalizedLine = some tag →
      ∀ next, wholeMachine.step line (initial input) ≠ .ok next

/-- Identity-monad reduction used to see through the `Id.run do` block of the
hazard-aware wrapper. -/
theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- Identity-monad bind reduction used to see through the `Id.run do` block of
the hazard-aware wrapper. -/
theorem id_bind_eq {α β : Type} (a : Id α) (f : α → β) : (a >>= f) = f a := rfl

/-- **The canonical initial-state no-wait analysis.**  If the underlying sealed
initial state has no pending MV transfers and all tags are incomplete, then no
wait-tagged line can take a successful hazard-aware step from the canonical
initial state: the tag-completion fuel returns `none`, so the wrapper returns
`.unknown`.  This is the generic content of
`welcomeWhole_initial_step_project`'s wait-tag branch. -/
theorem hazardInitialNoWait_of_pendingMv_nil {Input : Type}
    (initial : Input → State)
    (pendingNil : ∀ input, (initial input).pendingMv = [])
    (tagsIncomplete : ∀ input tag, (initial input).mvCompletedTags tag = false) :
    HazardInitialNoWait (fun input => HazardAwareState.initial (initial input)) := by
  intro input line tag wait next partialOk
  have unknown : executeHazardAwareNormalizedLine line.toNormalizedLine
      (HazardAwareState.initial (initial input)) = .unknown := by
    unfold executeHazardAwareNormalizedLine
    simp only [Id.run, id_pure_eq, id_bind_eq, HazardAwareState.initial,
      Option.isSome_none, Bool.false_eq_true, ite_false, wait]
    have noneEq : completePendingMvTagAll (initial input) tag = none :=
      ProofsLean.MNCore.completePendingMvTagFuel_none_of_pendingMv_nil
        ((initial input).pendingMv.length + 1) (initial input) tag
        (pendingNil input) (tagsIncomplete input tag)
    rw [show completePendingMvTagAll (initial input) tag = none from noneEq]
  rw [show wholeMachine.step line (HazardAwareState.initial (initial input)) =
      executeHazardAwareNormalizedLine line.toNormalizedLine
        (HazardAwareState.initial (initial input)) from rfl, unknown] at partialOk
  cases partialOk

/-- The canonical hazard-aware problem induced by a sealed problem: same
admissible inputs, hazard-aware initial state, postcondition read through
`state.machine`.  This is the generic form of `welcomeWholeSpec`. -/
noncomputable def hazardProblem (Input : Type) (sealedSpec : Problem (sealedMachine Input)) :
    Problem (hazardMachine Input) where
  admissible := sealedSpec.admissible
  initial := fun input => HazardAwareState.initial (sealedSpec.initial input)
  post := fun input state => sealedSpec.post input state.machine

@[simp] theorem hazardProblem_admissible (Input : Type)
    (sealedSpec : Problem (sealedMachine Input)) (input : Input) :
    (hazardProblem Input sealedSpec).admissible input ↔
      sealedSpec.admissible input :=
  Iff.rfl

@[simp] theorem hazardProblem_initial (Input : Type)
    (sealedSpec : Problem (sealedMachine Input)) (input : Input) :
    (hazardProblem Input sealedSpec).initial input =
      HazardAwareState.initial (sealedSpec.initial input) :=
  rfl

@[simp] theorem hazardProblem_post (Input : Type)
    (sealedSpec : Problem (sealedMachine Input)) (input : Input)
    (state : HazardAwareState) :
    (hazardProblem Input sealedSpec).post input state =
      sealedSpec.post input state.machine :=
  rfl

/-- **The sealed empty-program refutation lifts to the canonical hazard-aware
problem.**  The empty hazard run ends in the canonical initial state, whose
machine is the sealed initial state. -/
theorem hazardProblem_empty_not_correct {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (sealedEmpty : ¬ Correct (sealedMachine Input) sealedSpec []) :
    ¬ Correct (hazardMachine Input) (hazardProblem Input sealedSpec) [] := by
  intro correct
  apply sealedEmpty
  refine ⟨trivial, ?_⟩
  intro input admissible
  obtain ⟨result, run, post⟩ := correct.2 input admissible
  have run' : some (HazardAwareState.initial (sealedSpec.initial input)) = some result := by
    simpa [ProofsLean.execute, hazardMachine, welcomeWholeMachine, hazardProblem,
      HazardAwareState.initial] using run
  have same : HazardAwareState.initial (sealedSpec.initial input) = result :=
    Option.some.inj run'
  subst result
  refine ⟨(HazardAwareState.initial (sealedSpec.initial input)).machine, ?_, ?_⟩
  · rfl
  · exact post

/-- **A one-line program correct on the hazard-aware machine is correct on the
sealed machine**, provided the hazard initial state has no successful wait-tagged
step and the two specs agree on admissible inputs, initial states and
postconditions.  This is the generic `welcomeWholeLine_sealedCorrect`. -/
theorem hazardLine_correct_sealed {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (hazardSpec : Problem (hazardMachine Input))
    (admissible : ∀ input, hazardSpec.admissible input ↔ sealedSpec.admissible input)
    (initial : ∀ input, hazardSpec.initial input =
      HazardAwareState.initial (sealedSpec.initial input))
    (post : ∀ (input : Input) (state : HazardAwareState),
      hazardSpec.post input state → sealedSpec.post input state.machine)
    (noWaitInitial : HazardInitialNoWait hazardSpec.initial)
    (line : InstructionLine)
    (correct : Correct (hazardMachine Input) hazardSpec [line]) :
    Correct (sealedMachine Input) sealedSpec [line] := by
  refine ⟨trivial, ?_⟩
  intro input admissibleSealed
  have admissibleHazard : hazardSpec.admissible input :=
    (admissible input).mpr admissibleSealed
  obtain ⟨result, run, resultPost⟩ := correct.2 input admissibleHazard
  have stepOk : (hazardMachine Input).step line (hazardSpec.initial input) = some result := by
    simpa [ProofsLean.execute] using run
  have partialOk : wholeMachine.step line (hazardSpec.initial input) = .ok result :=
    hazardMachine_step_ok stepOk
  have noWait : normalizedLineWaitTag? line.toNormalizedLine = none := by
    cases wait : normalizedLineWaitTag? line.toNormalizedLine with
    | none => rfl
    | some tag => exact absurd partialOk (noWaitInitial input line tag wait result)
  have notStalled : (hazardSpec.initial input).stalledPEIssue = none := by
    rw [initial input]
    rfl
  have projected :=
    ProofsLean.MNCore.executeHazardAwareNormalizedLine_ok_project
      line.toNormalizedLine (hazardSpec.initial input) result notStalled noWait partialOk
  have machineEq : (hazardSpec.initial input).machine = sealedSpec.initial input := by
    rw [initial input]
    rfl
  have projected' : executeNormalizedLine line.toNormalizedLine (sealedSpec.initial input) =
      .ok result.machine := by
    rw [← machineEq]
    exact projected.1
  have sealedStep : (sealedMachine Input).step line (sealedSpec.initial input) =
      some result.machine := by
    simp only [sealedMachine]
    rw [projected']
  refine ⟨result.machine, ?_, post input result resultPost⟩
  have execEq : ProofsLean.execute (sealedMachine Input) [line] (sealedSpec.initial input) =
      (sealedMachine Input).step line (sealedSpec.initial input) := by
    simp only [ProofsLean.execute]
    cases (sealedMachine Input).step line (sealedSpec.initial input) <;> rfl
  rw [execEq]
  exact sealedStep

/-- **The canonical-problem specialization**: the only remaining hypothesis is
the initial-state no-wait analysis. -/
theorem hazardProblem_line_correct_sealed {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (noWaitInitial : HazardInitialNoWait
      (fun input => HazardAwareState.initial (sealedSpec.initial input)))
    (line : InstructionLine)
    (correct : Correct (hazardMachine Input) (hazardProblem Input sealedSpec) [line]) :
    Correct (sealedMachine Input) sealedSpec [line] :=
  hazardLine_correct_sealed sealedSpec (hazardProblem Input sealedSpec)
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ resultPost => resultPost)
    noWaitInitial line correct

/-- **Sealed lower bound ⇒ hazard lower bound at bound two**, for the canonical
hazard-aware problem.  This is the exact shape of
`welcomeWholeMachine_lowerBound_two`: only an empty-program refutation and the
initial no-wait analysis are problem-specific. -/
theorem hazardProblem_lowerBound_two_of_sealed {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (sealedLower : LowerBound (sealedMachine Input) sealedSpec 2)
    (emptyHazard : ¬ Correct (hazardMachine Input) (hazardProblem Input sealedSpec) [])
    (noWaitInitial : HazardInitialNoWait
      (fun input => HazardAwareState.initial (sealedSpec.initial input))) :
    LowerBound (hazardMachine Input) (hazardProblem Input sealedSpec) 2 := by
  rw [lowerBound_two_iff_rejects_unit_lines _ _ emptyHazard]
  intro line costOne correct
  have sealedCorrect :=
    hazardProblem_line_correct_sealed sealedSpec noWaitInitial line correct
  have bound := sealedLower [line] sealedCorrect
  have costOne' : InstructionLine.cost line = 1 := by
    simpa [hazardMachine] using costOne
  have scoreEq : ProofsLean.score (sealedMachine Input) [line] =
      InstructionLine.cost line := rfl
  rw [scoreEq, costOne'] at bound
  omega

/-- **The fully instantiated hazard lift.**  A sealed lower bound and a sealed
empty-program refutation transfer to the canonical hazard-aware problem for
free, once the initial state has no pending MV transfers and incomplete tags
(the usual zero-initialised machine).  This is the whole generic content of
`welcomeWholeMachine_lowerBound_two`. -/
theorem hazardProblem_lowerBound_two_of_sealed_of_nil_pending {Input : Type}
    (sealedSpec : Problem (sealedMachine Input))
    (sealedLower : LowerBound (sealedMachine Input) sealedSpec 2)
    (sealedEmpty : ¬ Correct (sealedMachine Input) sealedSpec [])
    (pendingNil : ∀ input, (sealedSpec.initial input).pendingMv = [])
    (tagsIncomplete : ∀ input tag, (sealedSpec.initial input).mvCompletedTags tag = false) :
    LowerBound (hazardMachine Input) (hazardProblem Input sealedSpec) 2 :=
  hazardProblem_lowerBound_two_of_sealed sealedSpec sealedLower
    (hazardProblem_empty_not_correct sealedSpec sealedEmpty)
    (hazardInitialNoWait_of_pendingMv_nil (fun input => sealedSpec.initial input)
      pendingNil tagsIncomplete)

/-! ## 4. The certificate obstruction -/

/-- A symbolic certificate is sound: it implies the lower bound.  Re-export of
`SymbolicBoundCertificate.sound`. -/
theorem symbolicBoundCertificate_sound {m : Machine} {spec : Problem m} {bound : Nat}
    (certificate : SymbolicBoundCertificate m spec bound) :
    LowerBound m spec bound :=
  ProofsLean.SymbolicBoundCertificate.sound certificate

/-- A concrete enumeration certificate is sound. -/
theorem boundCertificate_sound {m : Machine} {spec : Problem m} {bound : Nat}
    (certificate : BoundCertificate m spec bound) :
    LowerBound m spec bound :=
  ProofsLean.BoundCertificate.sound certificate

/-- **The certificate obstruction, generic form.**  At bound two, the `covers`
field forces every legal unit-cost line into the certificate's family.  Hence
any `SymbolicBoundCertificate` must *contain* every such line, whatever the
problem-specific family is. -/
theorem certificate_contains_short_line {m : Machine} {spec : Problem m}
    (certificate : SymbolicBoundCertificate m spec 2) (line : m.Line)
    (legal : m.legal [line]) (short : m.lineCost line < 2) :
    certificate.contains [line] := by
  apply certificate.covers
  · exact legal
  · simpa [ProofsLean.score] using short

/-- **The certificate obstruction, refutation form.**  Every legal unit-cost line
is rejected by any bound-two symbolic certificate.  This is
`welcomeBoundTwoCertificate_rejects_every_short_line` for an arbitrary machine:
its proof uses only `legal`, the score definition and the unit cost. -/
theorem certificate_rejects_short_line {m : Machine} {spec : Problem m}
    (certificate : SymbolicBoundCertificate m spec 2) (line : m.Line)
    (legal : m.legal [line]) (short : m.lineCost line < 2) :
    ¬ Correct m spec [line] :=
  certificate.rejected [line] (certificate_contains_short_line certificate line legal short)

/-- On the sealed machine legality is `True`, so the obstruction applies to every
line of issue cost below two. -/
theorem sealedCertificate_rejects_every_short_line {Input : Type}
    {admissible : Input → Prop} {initial : Input → State}
    {post : Input → State → Prop}
    (certificate : SymbolicBoundCertificate (sealedMachine Input)
      (sealedProblem Input admissible initial post) 2)
    (line : InstructionLine) (short : InstructionLine.cost line < 2) :
    ¬ Correct (sealedMachine Input) (sealedProblem Input admissible initial post) [line] := by
  exact certificate_rejects_short_line certificate line trivial short

/-- A bound-two certificate whose family is a problem-specific class `contains`
must in particular contain every legal unit-cost line; so no problem-specific
class can be the whole `contains`. -/
theorem certificate_family_must_cover_unit_lines {m : Machine} {spec : Problem m}
    (certificate : SymbolicBoundCertificate m spec 2) :
    ∀ line : m.Line, m.legal [line] → m.lineCost line = 1 →
      certificate.contains [line] :=
  fun line legal unit => certificate_contains_short_line certificate line legal (by omega)

/-! ## 5. Value-argument kernel

These are the problem-independent counting and untouched-word lemmas of
`WelcomeValueBound.lean`.  They are stated for a 16-word LM1 readback (the
Welcome/`1.a-b` shape); a problem observing a different number of words needs
its own counting lemma, but the same proof recipe.

The typical instantiation is:

1. `Lm1WritesNarrow` supplies at most four windows of at most two words;
2. `exists_uncovered_of_windows` produces an observed word `t` outside them;
3. `commit_lm1_word_zero` shows the committed write list leaves `t` at its old
   value (the problem's initial state supplies `oldZero`);
4. the problem's postcondition says `t` should be non-zero at the witness input.
-/

/-- The observed LM1 word `t` of a 16-word readback (word `t` of the output). -/
abbrev lm1Target := ProofsLean.MNCore.lm1Target

/-- A window of at most two observed words covers at most two members. -/
theorem card_window_le (start : Fin PEMemory.Bank.lm1.capacity) (size : Nat)
    (sizeTwo : size ≤ 2) :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun t => distance PEMemory.Bank.lm1 start (lm1Target t) < size)).card ≤ 2 :=
  ProofsLean.MNCore.card_window_le start size sizeTwo

/-- The union of the observed words covered by a list of narrow windows has at
most two words per window. -/
theorem card_covered_le (windows : List (Fin PEMemory.Bank.lm1.capacity × Nat))
    (sizes : ∀ p ∈ windows, p.2 ≤ 2) :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun t => ∃ p ∈ windows,
        distance PEMemory.Bank.lm1 p.1 (lm1Target t) < p.2)).card ≤
      2 * windows.length :=
  ProofsLean.MNCore.card_covered_le windows sizes

/-- **The counting half.**  At most four windows of at most two words each
cannot cover all sixteen observed words, so some observed word is untouched. -/
theorem exists_uncovered_of_windows (windows : List (Fin PEMemory.Bank.lm1.capacity × Nat))
    (bound : windows.length ≤ 4) (sizes : ∀ p ∈ windows, p.2 ≤ 2) :
    ∃ t : Fin 16, ∀ p ∈ windows,
      ¬ distance PEMemory.Bank.lm1 p.1 (lm1Target t) < p.2 :=
  ProofsLean.MNCore.exists_uncovered_of_windows windows bound sizes

/-- **The untouched-word half.**  If every `.lm1` write either misses `target`
or writes a zero/copied third data word, then committing the write list leaves
`target` at its old value. -/
theorem commit_lm1_word_zero (files : PEMemory.IntegerRegisterFiles)
    (writes : List PreparedWrite) (target : Fin PEMemory.Bank.lm1.capacity)
    (keeps : ∀ write ∈ writes,
      ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity)
        (data : WordBus) (selection : PEWordSelection),
        write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
        write.data = data → write.selection = selection →
          count PEMemory.Bank.lm1 width ≤ distance PEMemory.Bank.lm1 address target ∨
            (∀ bound : 2 < 4, data ⟨2, bound⟩ = 0) ∧
              distance PEMemory.Bank.lm1 address target = 2)
    (oldZero : files.lm1 target = 0) :
    (commitParsedMaskedWrites files writes).lm1 target = 0 :=
  ProofsLean.MNCore.commitParsedMaskedWrites_lm1_word_zero files writes target keeps oldZero

end ProofsLean.MNCore.Generic
