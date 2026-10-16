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

/-- A finite element type has only finitely many lists up to any fixed length.
This is the container-level finiteness lemma needed when bounded PE expression
and operand lists are composed into line carriers. -/
theorem listLengthLE_finite (α : Type) [Finite α] (bound : Nat) :
    Finite {values : List α // values.length ≤ bound} := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  induction bound with
  | zero =>
      apply Finite.of_injective (fun _ : {values : List α // values.length ≤ 0} => PUnit.unit)
      intro a b _
      apply Subtype.ext
      have aBound := a.property
      have bBound := b.property
      have ha : a.1 = [] := by
        cases h : a.1 with
        | nil => rfl
        | cons head rest => simp [h] at aBound
      have hb : b.1 = [] := by
        cases h : b.1 with
        | nil => rfl
        | cons head rest => simp [h] at bBound
      exact ha.trans hb.symm
  | succ bound ih =>
      let Tail := {values : List α // values.length ≤ bound}
      letI : Finite Tail := ih
      letI : Fintype Tail := Fintype.ofFinite Tail
      let code (values : {values : List α // values.length ≤ bound.succ}) : Option α × Tail :=
        match values with
        | ⟨[], _⟩ => (none, ⟨[], Nat.zero_le _⟩)
        | ⟨head :: rest, hlen⟩ =>
            (some head, ⟨rest, by
              have hlen' : rest.length + 1 ≤ bound + 1 := by simpa using hlen
              omega⟩)
      apply Finite.of_injective code
      intro a b equal
      cases a with
      | mk av ah =>
        cases b with
        | mk bv bh =>
          apply Subtype.ext
          cases av with
          | nil =>
              cases bv with
              | nil => rfl
              | cons head rest => simp [code] at equal
          | cons ahead arest =>
              cases bv with
              | nil => simp [code] at equal
              | cons bhead brest =>
                  simp [code] at equal
                  rcases equal with ⟨heads, tails⟩
                  cases heads
                  have tailEq : arest = brest := congrArg Subtype.val tails
                  cases tailEq
                  rfl

theorem natBelow_finite (bound : Nat) : Finite {value : Nat // value < bound} := by
  apply Finite.of_injective (fun value => (⟨value.1, value.2⟩ : Fin bound))
  intro a b equal
  apply Subtype.ext
  exact congrArg Fin.val equal

/-- The selected assemble3 boundary probes accept all signed `mabdiff` values
from -255 through 255 and reject -256 and 256. This is a finite carrier for
that observed envelope; parser correspondence remains a separate obligation. -/
def mabdiffInFiniteEnvelope (mabdiff : Int) : Prop :=
  -256 ≤ mabdiff ∧ mabdiff < 256

private def mabdiffFiniteCode
    (mabdiff : {mabdiff : Int // mabdiffInFiniteEnvelope mabdiff}) : Fin 512 := by
  refine ⟨(mabdiff.1 + 256).toNat, ?_⟩
  have hbound := mabdiff.2
  unfold mabdiffInFiniteEnvelope at hbound
  have hnonneg : 0 ≤ mabdiff.1 + 256 := by omega
  have hlt : mabdiff.1 + 256 < 512 := by omega
  have hcast : ((mabdiff.1 + 256).toNat : Int) = mabdiff.1 + 256 :=
    Int.toNat_of_nonneg hnonneg
  have hcastLt : ((mabdiff.1 + 256).toNat : Int) < 512 := by
    rw [hcast]
    exact hlt
  exact_mod_cast hcastLt

private theorem mabdiffFiniteCode_injective :
    Function.Injective mabdiffFiniteCode := by
  intro a b equal
  apply Subtype.ext
  have valuesEqual := congrArg Fin.val equal
  change (a.1 + 256).toNat = (b.1 + 256).toNat at valuesEqual
  have abound := a.2
  have bbound := b.2
  unfold mabdiffInFiniteEnvelope at abound bbound
  have aNonneg : 0 ≤ a.1 + 256 := by omega
  have bNonneg : 0 ≤ b.1 + 256 := by omega
  have aCast : ((a.1 + 256).toNat : Int) = a.1 + 256 := Int.toNat_of_nonneg aNonneg
  have bCast : ((b.1 + 256).toNat : Int) = b.1 + 256 := Int.toNat_of_nonneg bNonneg
  have intValuesEqual := congrArg (Int.ofNat) valuesEqual
  change ((a.1 + 256).toNat : Int) = ((b.1 + 256).toNat : Int) at intValuesEqual
  rw [aCast, bCast] at intValuesEqual
  omega

theorem mabdiffInFiniteEnvelope_finite :
    Finite {mabdiff : Int // mabdiffInFiniteEnvelope mabdiff} :=
  Finite.of_injective mabdiffFiniteCode mabdiffFiniteCode_injective

private def ParsedRrnOp.finiteCode : ParsedRrnOp → Fin 8
  | .fadd => 0 | .max => 1 | .min => 2 | .iadd => 3
  | .band => 4 | .and => 5 | .bor => 6 | .or => 7

private theorem ParsedRrnOp.finiteCode_injective :
    Function.Injective ParsedRrnOp.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedRrnOp.finiteCode] at equal ⊢

def ParsedRrn.inFiniteEnvelope (rrn : ParsedRrn) : Prop :=
  rrn.precision.toNat < 128

private def ParsedRrn.finiteCode
    (rrn : {rrn : ParsedRrn // rrn.inFiniteEnvelope}) : Fin 128 × Fin 8 :=
  (⟨rrn.1.precision.toNat, rrn.2⟩, ParsedRrnOp.finiteCode rrn.1.op)

private theorem ParsedRrn.finiteCode_injective :
    Function.Injective ParsedRrn.finiteCode := by
  rintro ⟨⟨ap, ao⟩, ha⟩ ⟨⟨bp, bo⟩, hb⟩ equal
  apply Subtype.ext
  simp only [ParsedRrn.finiteCode, Prod.mk.injEq, Fin.mk.injEq] at equal
  rcases equal with ⟨charValues, opValues⟩
  have charNatEqual := congrArg Fin.val charValues
  have precisionEqual : ap = bp := Char.toNat_inj.mp charNatEqual
  have opEqual : ao = bo := ParsedRrnOp.finiteCode_injective opValues
  cases precisionEqual
  cases opEqual
  rfl

theorem ParsedRrn.inFiniteEnvelope_finite :
    Finite {rrn : ParsedRrn // rrn.inFiniteEnvelope} :=
  Finite.of_injective ParsedRrn.finiteCode ParsedRrn.finiteCode_injective

private theorem ParsedRrn.finiteCode_value_injective
    (a b : ParsedRrn) (ha : a.inFiniteEnvelope) (hb : b.inFiniteEnvelope)
    (equal : ParsedRrn.finiteCode ⟨a, ha⟩ = ParsedRrn.finiteCode ⟨b, hb⟩) :
    a = b := by
  have subtypeEqual := ParsedRrn.finiteCode_injective equal
  exact congrArg Subtype.val subtypeEqual

inductive ParsedL1Mabdiff where
  | distrib (offset : Int) | gather (offset : Int)
  deriving DecidableEq, Repr

def ParsedL1Mabdiff.inFiniteEnvelope : ParsedL1Mabdiff → Prop
  | .distrib offset | .gather offset => ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope offset

private def ParsedL1Mabdiff.finiteCode
    (op : {op : ParsedL1Mabdiff // op.inFiniteEnvelope}) : Fin 512 ⊕ Fin 512 :=
  match op with
  | ⟨.distrib offset, bound⟩ => Sum.inl (mabdiffFiniteCode ⟨offset, bound⟩)
  | ⟨.gather offset, bound⟩ => Sum.inr (mabdiffFiniteCode ⟨offset, bound⟩)

private theorem ParsedL1Mabdiff.finiteCode_injective :
    Function.Injective ParsedL1Mabdiff.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a <;> cases b <;>
        simp [ParsedL1Mabdiff.finiteCode] at equal ⊢
      all_goals
        exact congrArg Subtype.val (mabdiffFiniteCode_injective equal)

theorem ParsedL1Mabdiff.inFiniteEnvelope_finite :
    Finite {op : ParsedL1Mabdiff // op.inFiniteEnvelope} :=
  Finite.of_injective ParsedL1Mabdiff.finiteCode ParsedL1Mabdiff.finiteCode_injective

inductive ParsedL1Selector where
  | mab (index : Nat) | mab4 (index : Nat)
  deriving DecidableEq, Repr

def ParsedL1Selector.inFiniteEnvelope : ParsedL1Selector → Prop
  | .mab index | .mab4 index => index < 16

private def ParsedL1Selector.finiteCode
    (selector : {selector : ParsedL1Selector // selector.inFiniteEnvelope}) : Fin 16 ⊕ Fin 16 :=
  match selector with
  | ⟨.mab index, bound⟩ => Sum.inl ⟨index, bound⟩
  | ⟨.mab4 index, bound⟩ => Sum.inr ⟨index, bound⟩

private theorem ParsedL1Selector.finiteCode_injective :
    Function.Injective ParsedL1Selector.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a <;> cases b <;>
        simp [ParsedL1Selector.finiteCode] at equal ⊢
      all_goals exact congrArg Fin.val equal

theorem ParsedL1Selector.inFiniteEnvelope_finite :
    Finite {selector : ParsedL1Selector // selector.inFiniteEnvelope} :=
  Finite.of_injective ParsedL1Selector.finiteCode ParsedL1Selector.finiteCode_injective

def ParsedL1Op.selectorInFiniteEnvelope : ParsedL1Op → Prop
  | .mwrite index | .m4write index => index < 16
  | _ => True

def ParsedL1Op.selectorView? : ParsedL1Op → Option ParsedL1Selector
  | .mwrite index => some (.mab index)
  | .m4write index => some (.mab4 index)
  | _ => none

theorem ParsedL1Op.selectorView?_bounded
    (op : ParsedL1Op) (bound : op.selectorInFiniteEnvelope) :
    ∀ value, op.selectorView? = some value → value.inFiniteEnvelope := by
  cases op with
  | mwrite index =>
      intro value equal
      cases equal
      change index < 16 at bound
      simpa [ParsedL1Selector.inFiniteEnvelope] using bound
  | m4write index =>
      intro value equal
      cases equal
      change index < 16 at bound
      simpa [ParsedL1Selector.inFiniteEnvelope] using bound
  | _ => simp [ParsedL1Op.selectorView?]

def ParsedL2Op.fromL1InFiniteEnvelope : ParsedL2Op → Prop
  | .fromL1b index => index < 8
  | _ => True

inductive ParsedL2FromL1 where
  | selector (index : Nat)
  deriving DecidableEq, Repr

def ParsedL2FromL1.inFiniteEnvelope : ParsedL2FromL1 → Prop
  | .selector index => index < 8

private def ParsedL2FromL1.finiteCode
    (selector : {selector : ParsedL2FromL1 // selector.inFiniteEnvelope}) : Fin 8 :=
  match selector with
  | ⟨.selector index, bound⟩ => ⟨index, bound⟩

private theorem ParsedL2FromL1.finiteCode_injective :
    Function.Injective ParsedL2FromL1.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a with
      | selector ai =>
        cases b with
        | selector bi =>
          have indices : ai = bi := congrArg Fin.val equal
          cases indices
          rfl

theorem ParsedL2FromL1.inFiniteEnvelope_finite :
    Finite {selector : ParsedL2FromL1 // selector.inFiniteEnvelope} :=
  Finite.of_injective ParsedL2FromL1.finiteCode ParsedL2FromL1.finiteCode_injective

def ParsedL2Op.fromL1View? : ParsedL2Op → Option ParsedL2FromL1
  | .fromL1b index => some (.selector index)
  | _ => none

theorem ParsedL2Op.fromL1View?_bounded
    (op : ParsedL2Op) (bound : op.fromL1InFiniteEnvelope) :
    ∀ value, op.fromL1View? = some value → value.inFiniteEnvelope := by
  cases op with
  | fromL1b index =>
      intro value equal
      cases equal
      change index < 8 at bound
      simpa [ParsedL2FromL1.inFiniteEnvelope] using bound
  | _ => simp [ParsedL2Op.fromL1View?]

abbrev ParsedL1OpFiniteCode :=
  Fin 9 × (Fin 1 ⊕ Fin 16 ⊕
    ((Fin 128 × Fin 8) × Bool ⊕ Fin 512))

def ParsedL1Op.inFiniteEnvelope : ParsedL1Op → Prop
  | .mwrite index | .m4write index => index < 16
  | .reduce rrn _ | .reduce4 rrn _ => rrn.inFiniteEnvelope
  | .distrib offset | .gather offset => mabdiffInFiniteEnvelope offset
  | .pbcast | .mbcast | .m4bcast => True

private def ParsedL1Op.finiteCode
    (op : {op : ParsedL1Op // op.inFiniteEnvelope}) : ParsedL1OpFiniteCode :=
  match op with
  | ⟨.pbcast, _⟩ => (0, Sum.inl 0)
  | ⟨.mbcast, _⟩ => (1, Sum.inl 0)
  | ⟨.mwrite index, bound⟩ => (2, Sum.inr (Sum.inl ⟨index, bound⟩))
  | ⟨.m4bcast, _⟩ => (3, Sum.inl 0)
  | ⟨.m4write index, bound⟩ => (4, Sum.inr (Sum.inl ⟨index, bound⟩))
  | ⟨.reduce rrn round, bound⟩ =>
      (5, Sum.inr (Sum.inr (Sum.inl (ParsedRrn.finiteCode ⟨rrn, bound⟩, round))))
  | ⟨.reduce4 rrn round, bound⟩ =>
      (6, Sum.inr (Sum.inr (Sum.inl (ParsedRrn.finiteCode ⟨rrn, bound⟩, round))))
  | ⟨.distrib offset, bound⟩ =>
      (7, Sum.inr (Sum.inr (Sum.inr (mabdiffFiniteCode ⟨offset, bound⟩))))
  | ⟨.gather offset, bound⟩ =>
      (8, Sum.inr (Sum.inr (Sum.inr (mabdiffFiniteCode ⟨offset, bound⟩))))

private theorem ParsedL1Op.finiteCode_injective :
    Function.Injective ParsedL1Op.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a <;> cases b <;>
        simp_all [ParsedL1Op.finiteCode, ParsedRrn.finiteCode]
      all_goals
        try exact congrArg Fin.val equal
        try
          exact ParsedRrn.finiteCode_value_injective _ _
            (by simpa [ParsedL1Op.inFiniteEnvelope] using ha)
            (by simpa [ParsedL1Op.inFiniteEnvelope] using hb)
            (Prod.ext equal.1.1 equal.1.2)
        try exact congrArg Subtype.val (mabdiffFiniteCode_injective equal)

theorem ParsedL1Op.inFiniteEnvelope_finite :
    Finite {op : ParsedL1Op // op.inFiniteEnvelope} := by
  exact Finite.of_injective ParsedL1Op.finiteCode ParsedL1Op.finiteCode_injective

def ParsedL1Op.mabdiffInFiniteEnvelope : ParsedL1Op → Prop
  | .distrib offset => ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope offset
  | .gather offset => ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope offset
  | _ => True

def ParsedL1Op.mabdiffView? : ParsedL1Op → Option ParsedL1Mabdiff
  | .distrib offset => some (.distrib offset)
  | .gather offset => some (.gather offset)
  | _ => none

theorem ParsedL1Op.mabdiffView?_bounded
    (op : ParsedL1Op) (bound : op.mabdiffInFiniteEnvelope) :
    ∀ value, op.mabdiffView? = some value → value.inFiniteEnvelope := by
  cases op with
  | distrib offset =>
      intro value equal
      cases equal
      change ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope offset at bound
      simpa [ParsedL1Mabdiff.inFiniteEnvelope] using bound
  | gather offset =>
      intro value equal
      cases equal
      change ProofsLean.MNCore.Issue.mabdiffInFiniteEnvelope offset at bound
      simpa [ParsedL1Mabdiff.inFiniteEnvelope] using bound
  | _ => simp [ParsedL1Op.mabdiffView?]

def optionNatInFiniteEnvelope (bound : Nat) (value : Option Nat) : Prop :=
  ∀ n, value = some n → n < bound

def optionNatFiniteCode (bound : Nat) :
    {value : Option Nat // optionNatInFiniteEnvelope bound value} → Option (Fin bound)
  | ⟨none, _⟩ => none
  | ⟨some n, property⟩ => some ⟨n, property n rfl⟩

theorem optionNatFiniteCode_injective (bound : Nat) :
    Function.Injective (optionNatFiniteCode bound) := by
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
          simp only [optionNatFiniteCode] at equal
          cases equal
      | some n =>
        cases b with
        | none =>
          simp only [optionNatFiniteCode] at equal
          cases equal
        | some m =>
          simp only [optionNatFiniteCode, Option.some.injEq] at equal
          have valuesEqual : n = m := congrArg Fin.val equal
          cases valuesEqual
          rfl

theorem optionNatBelow_finite (bound : Nat) :
    Finite {value : Option Nat // optionNatInFiniteEnvelope bound value} :=
  Finite.of_injective (optionNatFiniteCode bound) (optionNatFiniteCode_injective bound)

def waitTagInFiniteEnvelope (tag : Nat) : Prop := 0 < tag ∧ tag < 256

private def waitTagFiniteCode
    (tag : {tag : Nat // waitTagInFiniteEnvelope tag}) : Fin 256 :=
  ⟨tag.1, tag.2.2⟩

private theorem waitTagFiniteCode_injective : Function.Injective waitTagFiniteCode := by
  intro a b equal
  apply Subtype.ext
  exact congrArg Fin.val equal

theorem waitTagInFiniteEnvelope_finite :
    Finite {tag : Nat // waitTagInFiniteEnvelope tag} :=
  Finite.of_injective waitTagFiniteCode waitTagFiniteCode_injective

def optionWaitTagInFiniteEnvelope (tag : Option Nat) : Prop :=
  ∀ value, tag = some value → waitTagInFiniteEnvelope value

private def optionWaitTagFiniteCode
    (tag : {tag : Option Nat // optionWaitTagInFiniteEnvelope tag}) : Option (Fin 256) :=
  optionNatFiniteCode 256 ⟨tag.1, fun value equal => (tag.2 value equal).2⟩

private theorem optionWaitTagFiniteCode_injective :
    Function.Injective optionWaitTagFiniteCode := by
  intro a b equal
  apply Subtype.ext
  let a' : {value : Option Nat // optionNatInFiniteEnvelope 256 value} :=
    ⟨a.1, fun value h => (a.2 value h).2⟩
  let b' : {value : Option Nat // optionNatInFiniteEnvelope 256 value} :=
    ⟨b.1, fun value h => (b.2 value h).2⟩
  have codeEq : optionNatFiniteCode 256 a' = optionNatFiniteCode 256 b' := equal
  have valueEq : a'.1 = b'.1 :=
    congrArg (fun value : {value : Option Nat // optionNatInFiniteEnvelope 256 value} => value.1)
      (optionNatFiniteCode_injective 256 codeEq)
  exact valueEq

theorem optionWaitTagInFiniteEnvelope_finite :
    Finite {tag : Option Nat // optionWaitTagInFiniteEnvelope tag} :=
  Finite.of_injective optionWaitTagFiniteCode optionWaitTagFiniteCode_injective

def parsedBfArgInFiniteEnvelope (arg : Option Nat) : Prop :=
  ∀ value, arg = some value → 6 ≤ value ∧ value < 10

private def parsedBfArgFiniteCode
    (arg : {arg : Option Nat // parsedBfArgInFiniteEnvelope arg}) : Option (Fin 10) :=
  optionNatFiniteCode 10 ⟨arg.1, fun value equal => (arg.2 value equal).2⟩

private theorem parsedBfArgFiniteCode_injective :
    Function.Injective parsedBfArgFiniteCode := by
  intro a b equal
  apply Subtype.ext
  let a' : {value : Option Nat // optionNatInFiniteEnvelope 10 value} :=
    ⟨a.1, fun value h => (a.2 value h).2⟩
  let b' : {value : Option Nat // optionNatInFiniteEnvelope 10 value} :=
    ⟨b.1, fun value h => (b.2 value h).2⟩
  have codeEq : optionNatFiniteCode 10 a' = optionNatFiniteCode 10 b' := equal
  have valueEq : a'.1 = b'.1 :=
    congrArg (fun value : {value : Option Nat // optionNatInFiniteEnvelope 10 value} => value.1)
      (optionNatFiniteCode_injective 10 codeEq)
  exact valueEq

theorem parsedBfArgInFiniteEnvelope_finite :
    Finite {arg : Option Nat // parsedBfArgInFiniteEnvelope arg} :=
  Finite.of_injective parsedBfArgFiniteCode parsedBfArgFiniteCode_injective

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

def Bank.finiteCode : Bank → Fin 10
  | .grf0 => 0 | .grf1 => 1 | .lm0 => 2 | .lm1 => 3 | .t => 4
  | .l1bm => 5 | .l2bm => 6 | .pdm => 7 | .dram => 8 | .omr => 9

theorem Bank.finiteCode_injective : Function.Injective Bank.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [Bank.finiteCode] at equal ⊢

def Access.finiteCode
    (access : {access : Access // access.inFiniteEnvelope}) : Fin 10 × RegionFiniteCode :=
  (access.1.bank.finiteCode,
    Region.finiteCode ⟨access.1.region, access.2⟩)

theorem Access.finiteCode_injective :
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

def optionMaskInFiniteEnvelope (mask : Option ParsedMask) : Prop :=
  ∀ value, mask = some value → value.inFiniteEnvelope

abbrev ParsedMaskOptionFiniteCode := Option ParsedMaskFiniteCode
private instance : Fintype ParsedMaskOptionFiniteCode := inferInstance

def optionMaskFiniteCode
    (mask : {mask : Option ParsedMask // optionMaskInFiniteEnvelope mask}) :
    ParsedMaskOptionFiniteCode :=
  match mask with
  | ⟨none, _⟩ => none
  | ⟨some value, bound⟩ =>
    some (ParsedMask.finiteCode ⟨value, bound value rfl⟩)

theorem optionMaskFiniteCode_injective : Function.Injective optionMaskFiniteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a with
      | none => cases b with
        | none => rfl
        | some value => simp [optionMaskFiniteCode] at equal
      | some value => cases b with
        | none => simp [optionMaskFiniteCode] at equal
        | some other =>
          simp only [optionMaskFiniteCode, Option.some.injEq] at equal
          have maskEq := ParsedMask.finiteCode_injective equal
          exact congrArg some (congrArg Subtype.val maskEq)

def ParsedOperand.inFiniteEnvelope : ParsedOperand → Prop
  | .mem access _ _ _ mask => access.inFiniteEnvelope ∧ optionMaskInFiniteEnvelope mask
  | .bar _ width mask => width < 5 ∧ optionMaskInFiniteEnvelope mask
  | .forward .. => True
  | .fixed .. => True
  | .omr entry mask => entry < 16 ∧ optionMaskInFiniteEnvelope mask
  | .matrix _ width row => width < 5 ∧ optionNatInFiniteEnvelope 16 row
  | .nowrite => True
  | .l1bm width address => width < 5 ∧ optionNatInFiniteEnvelope 8192 address
  | .l2bm address l2b => address < 32768 ∧ optionNatInFiniteEnvelope 8 l2b
  | .dar address => address < 1024

theorem ParsedOperand.mem_inFiniteEnvelope_iff (access : Access) (neg ext rnd : Bool)
    (mask : Option ParsedMask) :
    ParsedOperand.inFiniteEnvelope (.mem access neg ext rnd mask) ↔
      access.inFiniteEnvelope ∧ optionMaskInFiniteEnvelope mask := Iff.rfl

theorem ParsedOperand.l1bm_inFiniteEnvelope_iff (width : Nat) (address : Option Nat) :
    ParsedOperand.inFiniteEnvelope (.l1bm width address) ↔
      width < 5 ∧ optionNatInFiniteEnvelope 8192 address := Iff.rfl

theorem ParsedOperand.l2bm_inFiniteEnvelope_iff (address : Nat) (l2b : Option Nat) :
    ParsedOperand.inFiniteEnvelope (.l2bm address l2b) ↔
      address < 32768 ∧ optionNatInFiniteEnvelope 8 l2b := Iff.rfl

abbrev OperandMemFiniteCode :=
  (Fin 10 × RegionFiniteCode) × Bool × Bool × Bool × ParsedMaskOptionFiniteCode
abbrev OperandBarFiniteCode := Bool × Fin 5 × ParsedMaskOptionFiniteCode
abbrev OperandForwardFiniteCode := Fin 4 × Bool × Bool × Bool
abbrev OperandFixedFiniteCode := Fin 6
abbrev OperandOmrFiniteCode := Fin 16 × ParsedMaskOptionFiniteCode
abbrev OperandMatrixFiniteCode := Bool × Fin 5 × Option (Fin 16)
abbrev OperandL1bmFiniteCode := Fin 5 × Option (Fin 8192)
abbrev OperandL2bmFiniteCode := Fin 32768 × Option (Fin 8)
abbrev ParsedOperandFiniteCode :=
  OperandMemFiniteCode ⊕ OperandBarFiniteCode ⊕ OperandForwardFiniteCode ⊕
  OperandFixedFiniteCode ⊕ OperandOmrFiniteCode ⊕ OperandMatrixFiniteCode ⊕
  PUnit.{1} ⊕ OperandL1bmFiniteCode ⊕ OperandL2bmFiniteCode ⊕ Fin 1024

private instance : Fintype RegionFiniteCode := inferInstance
private instance : Fintype ParsedOperandFiniteCode := inferInstance

private def operandMemCode : OperandMemFiniteCode → ParsedOperandFiniteCode := Sum.inl
private def operandBarCode (code : OperandBarFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inl code)
private def operandForwardCode (code : OperandForwardFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inl code))
private def operandFixedCode (code : OperandFixedFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl code)))
private def operandOmrCode (code : OperandOmrFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code))))
private def operandMatrixCode (code : OperandMatrixFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code)))))
private def operandNowriteCode : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl PUnit.unit))))))
private def operandL1bmCode (code : OperandL1bmFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code)))))))
private def operandL2bmCode (code : OperandL2bmFiniteCode) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inl code))))))))
private def operandDarCode (code : Fin 1024) : ParsedOperandFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr code))))))))

private def ParsedForward.finiteCode : ParsedForward → Fin 4
  | .aluf => 0 | .mauf => 1 | .lbf => 2 | .mreadf => 3

private def ParsedFixed.finiteCode : ParsedFixed → Fin 6
  | .l2bid => 0 | .l1bid => 1 | .mabid => 2 | .peid => 3 | .subpeid => 4 | .msb1 => 5

private theorem ParsedForward.finiteCode_injective :
    Function.Injective ParsedForward.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedForward.finiteCode] at equal ⊢

private theorem ParsedFixed.finiteCode_injective :
    Function.Injective ParsedFixed.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedFixed.finiteCode] at equal ⊢

def ParsedOperand.finiteCode
    (operand : {operand : ParsedOperand // operand.inFiniteEnvelope}) :
    ParsedOperandFiniteCode := by
  rcases operand with ⟨operand, bounds⟩
  cases operand with
  | mem access neg ext rnd mask =>
      rcases bounds with ⟨accessBound, maskBound⟩
      exact operandMemCode
        ((Access.finiteCode ⟨access, accessBound⟩), neg, ext, rnd,
          optionMaskFiniteCode ⟨mask, maskBound⟩)
  | bar lm1 width mask =>
      rcases bounds with ⟨widthBound, maskBound⟩
      exact operandBarCode (lm1, ⟨width, widthBound⟩,
        optionMaskFiniteCode ⟨mask, maskBound⟩)
  | forward kind neg ext rnd =>
      exact operandForwardCode (kind.finiteCode, neg, ext, rnd)
  | fixed kind =>
      exact operandFixedCode kind.finiteCode
  | omr entry mask =>
      rcases bounds with ⟨entryBound, maskBound⟩
      exact operandOmrCode (⟨entry, entryBound⟩,
        optionMaskFiniteCode ⟨mask, maskBound⟩)
  | matrix y width row =>
      rcases bounds with ⟨widthBound, rowBound⟩
      exact operandMatrixCode (y, ⟨width, widthBound⟩,
        optionNatFiniteCode 16 ⟨row, rowBound⟩)
  | nowrite => exact operandNowriteCode
  | l1bm width address =>
      rcases bounds with ⟨widthBound, addressBound⟩
      exact operandL1bmCode (⟨width, widthBound⟩,
        optionNatFiniteCode 8192 ⟨address, addressBound⟩)
  | l2bm address l2b =>
      rcases bounds with ⟨addressBound, l2bBound⟩
      exact operandL2bmCode (⟨address, addressBound⟩,
        optionNatFiniteCode 8 ⟨l2b, l2bBound⟩)
  | dar address =>
      exact operandDarCode ⟨address, bounds⟩

theorem ParsedOperand.finiteCode_injective : Function.Injective ParsedOperand.finiteCode := by
  intro a b codeEqual
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a <;> cases b <;>
        simp_all [ParsedOperand.finiteCode, operandMemCode, operandBarCode,
          operandForwardCode, operandFixedCode, operandOmrCode, operandMatrixCode,
          operandNowriteCode, operandL1bmCode, operandL2bmCode, operandDarCode,
          ParsedForward.finiteCode, ParsedFixed.finiteCode,
          Sum.inl_ne_inr, Sum.inr_ne_inl]
      all_goals
        solve
        | rcases codeEqual with ⟨accessEqual, _, _, _, maskEqual⟩
          exact ⟨congrArg Subtype.val (Access.finiteCode_injective accessEqual),
            congrArg Subtype.val (optionMaskFiniteCode_injective maskEqual)⟩
        | rcases codeEqual with ⟨_, _, maskEqual⟩
          exact congrArg Subtype.val (optionMaskFiniteCode_injective maskEqual)
        | rcases codeEqual with ⟨_, maskEqual⟩
          exact congrArg Subtype.val (optionMaskFiniteCode_injective maskEqual)
        | rcases codeEqual with ⟨kindEqual, _, _, _⟩
          exact ParsedForward.finiteCode_injective kindEqual
        | exact ParsedFixed.finiteCode_injective codeEqual
        | rcases codeEqual with ⟨_, _, rowEqual⟩
          exact congrArg Subtype.val (optionNatFiniteCode_injective 16 rowEqual)
        | rcases codeEqual with ⟨_, addressEqual⟩
          exact congrArg Subtype.val (optionNatFiniteCode_injective 8192 addressEqual)
        | rcases codeEqual with ⟨addressEqual, l2bEqual⟩
          exact congrArg Subtype.val (optionNatFiniteCode_injective 8 l2bEqual)
        | exact congrArg Fin.val codeEqual

theorem ParsedOperand.inFiniteEnvelope_finite :
    Finite {operand : ParsedOperand // operand.inFiniteEnvelope} :=
  Finite.of_injective ParsedOperand.finiteCode ParsedOperand.finiteCode_injective

/-- A parser-bounded source tuple whose operands lie in the recorded finite
operand envelope ranges over a finite type. Destinations are deliberately not
included: Rust assigns the remaining token suffix to destinations without a
parser-side length bound. -/
def ParsedExpr.sourcesInFiniteEnvelope (expression : ParsedExpr) : Prop :=
  expression.sources.length ≤ 3 ∧
    ∀ operand ∈ expression.sources, operand.inFiniteEnvelope

theorem ParsedExpr.sourcesInFiniteEnvelope_of_parserArity
    (expression : ParsedExpr)
    (arity : expression.sourcesMatchParserArity)
    (operands : ∀ operand ∈ expression.sources, operand.inFiniteEnvelope) :
    expression.sourcesInFiniteEnvelope :=
  ⟨expression.sources_length_le_three arity, operands⟩

private def ParsedExpr.sourceCode
    (sources : {sources : List ParsedOperand //
      sources.length ≤ 3 ∧ ∀ operand ∈ sources, operand.inFiniteEnvelope}) :
    {values : List {operand : ParsedOperand // operand.inFiniteEnvelope} //
      values.length ≤ 3} := by
  let values := sources.1.attach.map fun operand =>
    (⟨operand.1, sources.2.2 operand.1 operand.2⟩ :
      {operand : ParsedOperand // operand.inFiniteEnvelope})
  refine ⟨values, ?_⟩
  simpa [values] using sources.2.1

private theorem ParsedExpr.sourceCode_injective :
    Function.Injective ParsedExpr.sourceCode := by
  intro a b equal
  apply Subtype.ext
  have valueEqual := congrArg (fun values => values.1.map Subtype.val) equal
  simpa [ParsedExpr.sourceCode, List.attach_map_val] using valueEqual

theorem ParsedExpr.sourcesInFiniteEnvelope_finite :
    Finite {sources : List ParsedOperand //
      sources.length ≤ 3 ∧ ∀ operand ∈ sources, operand.inFiniteEnvelope} := by
  let Operand := {operand : ParsedOperand // operand.inFiniteEnvelope}
  letI : Finite Operand := ParsedOperand.inFiniteEnvelope_finite
  letI : Finite {values : List Operand // values.length ≤ 3} :=
    listLengthLE_finite Operand 3
  exact Finite.of_injective ParsedExpr.sourceCode ParsedExpr.sourceCode_injective

def ParsedL1bSet.inFiniteEnvelope (set : ParsedL1bSet) : Prop :=
  set.mask < 8 ∧ set.immode < 8

def ParsedL1bSet.finiteCode
    (set : {set : ParsedL1bSet // set.inFiniteEnvelope}) : Fin 8 × Fin 8 :=
  (⟨set.1.mask, set.2.1⟩, ⟨set.1.immode, set.2.2⟩)

theorem ParsedL1bSet.finiteCode_injective : Function.Injective ParsedL1bSet.finiteCode := by
  intro a b equal
  cases a with
  | mk av ah =>
    cases b with
    | mk bv bh =>
      apply Subtype.ext
      cases av with
      | mk am ai =>
        cases bv with
        | mk bm bi =>
          simp only [ParsedL1bSet.finiteCode, Prod.mk.injEq] at equal
          rcases equal with ⟨maskCodeEq, immodeCodeEq⟩
          have maskEq : am = bm := congrArg Fin.val maskCodeEq
          have immodeEq : ai = bi := congrArg Fin.val immodeCodeEq
          cases maskEq
          cases immodeEq
          rfl

theorem ParsedL1bSet.inFiniteEnvelope_finite :
    Finite {set : ParsedL1bSet // set.inFiniteEnvelope} :=
  Finite.of_injective ParsedL1bSet.finiteCode ParsedL1bSet.finiteCode_injective

private theorem ParsedL1bSet.values_injective (a b : ParsedL1bSet)
    (equal : a.mask = b.mask ∧ a.immode = b.immode) : a = b := by
  cases a with
  | mk am ai =>
    cases b with
    | mk bm bi =>
      simp_all

abbrev ParsedL2OpFiniteCode :=
  Fin 10 × (Fin 8 × Fin 8) × (Fin 128 × Fin 8) × Fin 8 × Fin 512

def ParsedL2Op.inFiniteEnvelope : ParsedL2Op → Prop
  | .bcast set | .bcast2 set | .distrib set | .imcast set => set.inFiniteEnvelope
  | .fromL1b index => index < 8
  | .reduce rrn set => rrn.inFiniteEnvelope ∧ set.inFiniteEnvelope
  | .reduce2 rrn => rrn.inFiniteEnvelope
  | .gather | .dars | .darw => True

private def ParsedL2Op.finiteCode
    (op : {op : ParsedL2Op // op.inFiniteEnvelope}) : ParsedL2OpFiniteCode :=
  let noSet : Fin 8 × Fin 8 := (0, 0)
  let noRrn : Fin 128 × Fin 8 := (0, 0)
  let noIndex : Fin 8 := 0
  let noOffset : Fin 512 := 0
  match op with
  | ⟨.bcast set, bound⟩ => (0, ParsedL1bSet.finiteCode ⟨set, bound⟩, noRrn, noIndex, noOffset)
  | ⟨.bcast2 set, bound⟩ => (1, ParsedL1bSet.finiteCode ⟨set, bound⟩, noRrn, noIndex, noOffset)
  | ⟨.distrib set, bound⟩ => (2, ParsedL1bSet.finiteCode ⟨set, bound⟩, noRrn, noIndex, noOffset)
  | ⟨.fromL1b index, bound⟩ => (3, noSet, noRrn, ⟨index, bound⟩, noOffset)
  | ⟨.reduce rrn set, bound⟩ =>
      (4, ParsedL1bSet.finiteCode ⟨set, bound.2⟩,
        ParsedRrn.finiteCode ⟨rrn, bound.1⟩, noIndex, noOffset)
  | ⟨.reduce2 rrn, bound⟩ =>
      (5, noSet, ParsedRrn.finiteCode ⟨rrn, bound⟩, noIndex, noOffset)
  | ⟨.gather, _⟩ => (6, noSet, noRrn, noIndex, noOffset)
  | ⟨.imcast set, bound⟩ => (7, ParsedL1bSet.finiteCode ⟨set, bound⟩, noRrn, noIndex, noOffset)
  | ⟨.dars, _⟩ => (8, noSet, noRrn, noIndex, noOffset)
  | ⟨.darw, _⟩ => (9, noSet, noRrn, noIndex, noOffset)

private theorem ParsedL2Op.finiteCode_injective :
    Function.Injective ParsedL2Op.finiteCode := by
  intro a b equal
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      apply Subtype.ext
      cases a <;> cases b <;>
        simp_all [ParsedL2Op.finiteCode, ParsedL1bSet.finiteCode, ParsedRrn.finiteCode]
      all_goals
        try exact congrArg Fin.val equal
        try exact ParsedL1bSet.values_injective _ _ equal
        try
          exact ParsedRrn.finiteCode_value_injective _ _
            (by simpa [ParsedL2Op.inFiniteEnvelope] using ha)
            (by simpa [ParsedL2Op.inFiniteEnvelope] using hb)
            (Prod.ext equal.1 equal.2)
        try
          exact And.intro
            (ParsedRrn.finiteCode_value_injective _ _
              (by simpa [ParsedL2Op.inFiniteEnvelope] using ha.1)
              (by simpa [ParsedL2Op.inFiniteEnvelope] using hb.1)
              (Prod.ext equal.2.1 equal.2.2))
            (ParsedL1bSet.values_injective _ _ equal.1)

theorem ParsedL2Op.inFiniteEnvelope_finite :
    Finite {op : ParsedL2Op // op.inFiniteEnvelope} :=
  Finite.of_injective ParsedL2Op.finiteCode ParsedL2Op.finiteCode_injective

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
