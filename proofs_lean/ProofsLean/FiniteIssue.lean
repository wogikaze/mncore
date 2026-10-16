import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.BitVec
import ProofsLean.Issue
import ProofsLean.FiniteRegion

namespace ProofsLean.MNCore.Issue

theorem natBelow_finite (bound : Nat) : Finite {value : Nat // value < bound} := by
  apply Finite.of_injective (fun value => (⟨value.1, value.2⟩ : Fin bound))
  intro a b equal
  apply Subtype.ext
  exact congrArg Fin.val equal

def optionNatInFiniteEnvelope (bound : Nat) (value : Option Nat) : Prop :=
  ∀ n, value = some n → n < bound

private def optionNatCode (bound : Nat) :
    {value : Option Nat // optionNatInFiniteEnvelope bound value} → Option (Fin bound)
  | ⟨none, _⟩ => none
  | ⟨some n, property⟩ => some ⟨n, property n rfl⟩

private theorem optionNatCode_injective (bound : Nat) :
    Function.Injective (optionNatCode bound) := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some n =>
          simp only [optionNatCode] at equal
          cases equal
      | some n =>
        cases b with
        | none =>
          simp only [optionNatCode] at equal
          cases equal
        | some m =>
          simp only [optionNatCode, Option.some.injEq] at equal
          have valuesEqual : n = m := congrArg Fin.val equal
          cases valuesEqual
          rfl

theorem optionNatBelow_finite (bound : Nat) :
    Finite {value : Option Nat // optionNatInFiniteEnvelope bound value} :=
  Finite.of_injective (optionNatCode bound) (optionNatCode_injective bound)

def ParsedMask.inFiniteEnvelope : ParsedMask → Prop
  | .pattern .. => True
  | .entry _ index => index < 32

abbrev ParsedMaskFiniteCode := (Bool × Fin 16) ⊕ (Bool × Fin 32)
private instance : Fintype ParsedMaskFiniteCode := inferInstance

def ParsedMask.finiteCode (mask : {mask : ParsedMask // mask.inFiniteEnvelope}) :
    ParsedMaskFiniteCode :=
  match mask with
  | ⟨.pattern longLong bits, _⟩ => Sum.inl (longLong, bits.toFin)
  | ⟨.entry longLong index, bound⟩ =>
    Sum.inr (longLong, ⟨index, by simpa [ParsedMask.inFiniteEnvelope] using bound⟩)

theorem ParsedMask.finiteCode_injective :
    Function.Injective ParsedMask.finiteCode := by
  intro a b codeEqual
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a with
      | pattern longLong bits =>
        cases b with
        | pattern otherLongLong otherBits =>
          simp only [ParsedMask.finiteCode, Sum.inl.injEq, Prod.mk.injEq] at codeEqual
          rcases codeEqual with ⟨rfl, bitsEqual⟩
          have bitsEqual' : bits = otherBits := BitVec.toFin_injective bitsEqual
          subst otherBits
          rfl
        | entry otherLongLong otherIndex =>
          simp only [ParsedMask.finiteCode] at codeEqual
          cases codeEqual
      | entry longLong index =>
        cases b with
        | pattern otherLongLong otherBits =>
          simp only [ParsedMask.finiteCode] at codeEqual
          cases codeEqual
        | entry otherLongLong otherIndex =>
          simp only [ParsedMask.finiteCode, Sum.inr.injEq, Prod.mk.injEq] at codeEqual
          rcases codeEqual with ⟨rfl, valueEqual⟩
          have indexEqual : index = otherIndex := congrArg Fin.val valueEqual
          subst otherIndex
          rfl

theorem ParsedMask.inFiniteEnvelope_finite :
    Finite {mask : ParsedMask // mask.inFiniteEnvelope} :=
  Finite.of_injective ParsedMask.finiteCode ParsedMask.finiteCode_injective

def Access.inFiniteEnvelope (access : Access) : Prop :=
  access.region.inFiniteEnvelope

private def Bank.finiteCode : Bank → Fin 10
  | .grf0 => 0 | .grf1 => 1 | .lm0 => 2 | .lm1 => 3 | .t => 4
  | .l1bm => 5 | .l2bm => 6 | .pdm => 7 | .dram => 8 | .omr => 9

private theorem Bank.finiteCode_injective : Function.Injective Bank.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [Bank.finiteCode] at equal ⊢

private def Access.finiteCode
    (access : {access : Access // access.inFiniteEnvelope}) : Fin 10 × RegionFiniteCode :=
  (access.1.bank.finiteCode,
    Region.finiteCode ⟨access.1.region, access.2⟩)

private theorem Access.finiteCode_injective :
    Function.Injective Access.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a with
      | mk abank aregion =>
        cases b with
        | mk bbank bregion =>
          simp only [Access.finiteCode, Prod.mk.injEq] at equal
          rcases equal with ⟨banks, regions⟩
          have bankEq := Bank.finiteCode_injective banks
          have regionEq := Region.finiteCode_injective regions
          cases bankEq
          have rawRegionEq : aregion = bregion := congrArg Subtype.val regionEq
          cases rawRegionEq
          rfl

theorem Access.inFiniteEnvelope_finite :
    Finite {access : Access // access.inFiniteEnvelope} :=
  Finite.of_injective Access.finiteCode Access.finiteCode_injective

def omrEntryInFiniteEnvelope (entry : Nat) : Prop := entry < 16

private def omrEntryCode
    (entry : {entry : Nat // omrEntryInFiniteEnvelope entry}) : Fin 16 :=
  ⟨entry.1, entry.2⟩

private theorem omrEntryCode_injective : Function.Injective omrEntryCode := by
  intro a b equal
  apply Subtype.ext
  exact congrArg Fin.val equal

theorem omrEntryInFiniteEnvelope_finite :
    Finite {entry : Nat // omrEntryInFiniteEnvelope entry} :=
  Finite.of_injective omrEntryCode omrEntryCode_injective

private def Group.code : Group → Fin 10
  | .alu => 0
  | .mauCalc => 1
  | .mauWrite => 2
  | .mauRead => 3
  | .l1bm => 4
  | .l1bmTurnaround => 5
  | .l2bm => 6
  | .l2bmDarw => 7
  | .wait => 8
  | .noforward => 9

private theorem Group.code_injective : Function.Injective Group.code := by
  intro a b equal
  cases a <;> cases b <;> simp [Group.code] at equal ⊢

private def groupCodes (expressions : List Expr) : List (Fin 10) :=
  expressions.map (fun expression => Group.code (expression.group.getD .alu))

private theorem projectFrom_length (nextId : Nat) (expressions : List ParsedExpr) :
    (projectFrom nextId expressions).length = expressions.length := by
  induction expressions generalizing nextId with
  | nil => rfl
  | cons _ _ ih => simp [projectFrom, ih]

private theorem ParsedExpr.issueGroup_isSome (expression : ParsedExpr) :
    expression.issueGroup.isSome := by
  cases expression with
  | mk op sources destinations flush text =>
    simp only [ParsedExpr.issueGroup]
    split <;> first | rfl | (split <;> rfl)

private theorem projectFrom_group_some (nextId : Nat) (expressions : List ParsedExpr)
    (expression : Expr) (member : expression ∈ projectFrom nextId expressions) :
    expression.group.isSome := by
  induction expressions generalizing nextId with
  | nil => simp [projectFrom] at member
  | cons parsed rest ih =>
    simp only [projectFrom, List.mem_cons] at member
    rcases member with head | tail
    · subst expression
      simpa [ParsedExpr.toIssueExpr] using parsed.issueGroup_isSome
    · exact ih (nextId + 1) tail

private theorem projectFrom_groupCodes_nodup (nextId : Nat)
    (expressions : List ParsedExpr)
    (groups : groupsUnique (projectFrom nextId expressions)) :
    (groupCodes (projectFrom nextId expressions)).Nodup := by
  induction expressions generalizing nextId with
  | nil => simp [groupCodes, projectFrom]
  | cons parsed rest ih =>
    change (Group.code ((parsed.toIssueExpr nextId).group.getD .alu) ::
      groupCodes (projectFrom (nextId + 1) rest)).Nodup
    rw [List.nodup_cons]
    constructor
    · intro member
      simp only [groupCodes, List.mem_map] at member
      rcases member with ⟨expression, tailMem, codeEqual⟩
      have someHead : (parsed.toIssueExpr nextId).group.isSome := by
        simpa [ParsedExpr.toIssueExpr] using parsed.issueGroup_isSome
      have someTail : expression.group.isSome :=
        projectFrom_group_some (nextId + 1) rest expression tailMem
      have groupEqual : (parsed.toIssueExpr nextId).group = expression.group := by
        cases headOption : (parsed.toIssueExpr nextId).group with
        | none => simp [headOption] at someHead
        | some headGroup =>
          cases tailOption : expression.group with
          | none => simp [tailOption] at someTail
          | some tailGroup =>
            have codeEq : Group.code tailGroup = Group.code headGroup := by
              simpa [groupCodes, headOption, tailOption] using codeEqual
            exact (congrArg some (Group.code_injective codeEq)).symm
      have idsDiffer : (parsed.toIssueExpr nextId).id ≠ expression.id := by
        intro idsEqual
        have lower := projectFrom_id_lower (nextId + 1) rest expression tailMem
        simp [ParsedExpr.toIssueExpr] at idsEqual
        omega
      cases headOption : (parsed.toIssueExpr nextId).group with
      | none => simp [headOption] at someHead
      | some group =>
        have rejectTail := groups (parsed.toIssueExpr nextId)
          (by simp [projectFrom]) expression
          (List.mem_cons_of_mem _ tailMem) idsDiffer group headOption
        have tailHasSameGroup : expression.group = some group := by
          rw [← groupEqual, headOption]
        exact rejectTail tailHasSameGroup
    · apply ih
      intro e he f hf different group eGroup
      exact groups e (List.mem_cons_of_mem _ he) f (List.mem_cons_of_mem _ hf)
        different group eGroup

theorem projectLine_expression_count_le_ten (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) : expressions.length ≤ 10 := by
  have groups := legal.2.1
  have nodup := projectFrom_groupCodes_nodup 0 expressions groups
  have lengthEq : (groupCodes (projectFrom 0 expressions)).length = expressions.length := by
    simp [groupCodes, projectFrom_length]
  have finiteCard := List.toFinset_card_of_nodup nodup
  have subset : (groupCodes (projectLine expressions)).toFinset ⊆ Finset.univ :=
    Finset.subset_univ _
  have cardLe := Finset.card_le_card subset
  rw [Finset.card_univ, Fintype.card_fin] at cardLe
  have cardLe' : (groupCodes (projectFrom 0 expressions)).toFinset.card ≤ 10 := by
    simpa [projectLine] using cardLe
  rw [← lengthEq, ← finiteCard]
  exact cardLe'

end ProofsLean.MNCore.Issue
