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

/-- Encoded instruction words observed from the official flat assembler:
PE uses a `j` word and MV uses an `m` word. Their bit widths come from the
checked assembler-output boundary record; the universal source-to-encoding
correspondence remains a separate obligation. -/
abbrev AssemblerInstructionWord := Sum (BitVec 426) (BitVec 82)

private theorem bitVec_finite (width : Nat) : Finite (BitVec width) :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

theorem AssemblerInstructionWord.finite : Finite AssemblerInstructionWord := by
  letI : Finite (BitVec 426) := bitVec_finite 426
  letI : Finite (BitVec 82) := bitVec_finite 82
  letI : Fintype (BitVec 426) := Fintype.ofFinite _
  letI : Fintype (BitVec 82) := Fintype.ofFinite _
  exact Finite.of_fintype _

instance : Finite AssemblerInstructionWord := AssemblerInstructionWord.finite

noncomputable instance : Fintype AssemblerInstructionWord := Fintype.ofFinite _

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

theorem encodedPrograms_lengthBounded_finite (bound : Nat) :
    Finite {program : List AssemblerInstructionWord // program.length ≤ bound} :=
  listLengthLE_finite AssemblerInstructionWord bound

private theorem nodup_length_le_fintype_card {α : Type} [Fintype α] [DecidableEq α]
    (values : List α) (nodup : values.Nodup) : values.length ≤ Fintype.card α := by
  have injective : Function.Injective values.get :=
    List.nodup_iff_injective_get.mp nodup
  have cardBound := Fintype.card_le_of_injective values.get injective
  simpa using cardBound

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

def ParsedMaskTargets.finiteCode (targets : ParsedMaskTargets) :=
  (targets.grf0, targets.grf1, targets.t, targets.lm0, targets.lm1,
    targets.maskRegister)

theorem ParsedMaskTargets.finiteCode_injective :
    Function.Injective ParsedMaskTargets.finiteCode := by
  intro a b equal
  cases a with
  | mk agrf0 agrf1 atarget alm0 alm1 amask =>
    cases b with
    | mk bgrf0 bgrf1 btarget blm0 blm1 bmask =>
      simp [ParsedMaskTargets.finiteCode] at equal
      rcases equal with ⟨h0, h1, h2, h3, h4, h5⟩
      cases h0
      cases h1
      cases h2
      cases h3
      cases h4
      cases h5
      rfl

theorem ParsedMaskTargets.finite : Finite ParsedMaskTargets := by
  letI : Fintype (Bool × Bool × Bool × Bool × Bool × Bool) := inferInstance
  exact Finite.of_injective ParsedMaskTargets.finiteCode
    ParsedMaskTargets.finiteCode_injective

def ParsedMaskDirective.inFiniteEnvelope (directive : ParsedMaskDirective) : Prop :=
  (directive.widthWords = 2 ∨ directive.widthWords = 4) ∧ directive.entry < 32

abbrev ParsedMaskDirectiveFiniteCode := Fin 5 × ParsedMaskTargets × Fin 32

private def ParsedMaskDirective.finiteCode
    (directive : {directive : ParsedMaskDirective // directive.inFiniteEnvelope}) :
    ParsedMaskDirectiveFiniteCode :=
  (⟨directive.1.widthWords, by
      rcases directive.2.1 with widthEq | widthEq <;> omega⟩,
    directive.1.targets, ⟨directive.1.entry, directive.2.2⟩)

private theorem ParsedMaskDirective.finiteCode_injective :
    Function.Injective ParsedMaskDirective.finiteCode := by
  intro a b equal
  rcases a with ⟨⟨aw, atargets, aentry⟩, ha⟩
  rcases b with ⟨⟨bw, btargets, bentry⟩, hb⟩
  simp only [ParsedMaskDirective.finiteCode, Prod.mk.injEq, Fin.mk.injEq] at equal
  rcases equal with ⟨widthEq, targetsEq, entryEq⟩
  cases widthEq
  cases targetsEq
  cases entryEq
  rfl

theorem ParsedMaskDirective.inFiniteEnvelope_finite :
    Finite {directive : ParsedMaskDirective // directive.inFiniteEnvelope} := by
  letI : Finite ParsedMaskTargets := ParsedMaskTargets.finite
  letI : Fintype ParsedMaskTargets := Fintype.ofFinite _
  letI : Fintype ParsedMaskDirectiveFiniteCode := inferInstance
  exact Finite.of_injective ParsedMaskDirective.finiteCode
    ParsedMaskDirective.finiteCode_injective

/-- Applying an in-envelope mask directive preserves the finite control-state
carrier; all other parsed lines preserve the prior state. -/
theorem ParsedLine.updateMaskState_inFiniteEnvelope
    (line : ParsedLine) (state : ParsedMaskDirective)
    (stateBound : state.inFiniteEnvelope)
    (lineBound : line.maskDirectiveInFiniteEnvelope) :
    (line.updateMaskState state).inFiniteEnvelope := by
  cases line <;>
    simp_all [ParsedLine.maskDirectiveInFiniteEnvelope,
      ParsedLine.updateMaskState, ParsedMaskDirective.inFiniteEnvelope]

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
  access.region.inFiniteEnvelope ∧
    (access.bank = .grf0 ∨ access.bank = .grf1 →
      access.region.address0 < 512 ∧ access.region.address1 < 512 ∧
        access.region.address2 < 512 ∧ access.region.address3 < 512)

def Bank.finiteCode : Bank → Fin 10
  | .grf0 => 0 | .grf1 => 1 | .lm0 => 2 | .lm1 => 3 | .t => 4
  | .l1bm => 5 | .l2bm => 6 | .pdm => 7 | .dram => 8 | .omr => 9

theorem Bank.finiteCode_injective : Function.Injective Bank.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [Bank.finiteCode] at equal ⊢

def Access.finiteCode
    (access : {access : Access // access.inFiniteEnvelope}) : Fin 10 × RegionFiniteCode :=
  (access.1.bank.finiteCode,
    Region.finiteCode ⟨access.1.region, access.2.1⟩)

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

theorem Access.grf_capacity_envelope (access : Access)
    (bounded : access.inFiniteEnvelope)
    (bank : access.bank = .grf0 ∨ access.bank = .grf1) :
    access.region.address0 < 512 ∧ access.region.address1 < 512 ∧
      access.region.address2 < 512 ∧ access.region.address3 < 512 :=
  bounded.2 bank

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

theorem optionMaskInFiniteEnvelope_finite :
    Finite {mask : Option ParsedMask // optionMaskInFiniteEnvelope mask} :=
  Finite.of_injective optionMaskFiniteCode optionMaskFiniteCode_injective

def ParsedOperand.inFiniteEnvelope : ParsedOperand → Prop
  | .mem access _ _ _ mask => access.inFiniteEnvelope ∧ optionMaskInFiniteEnvelope mask
  | .bar _ width mask => (width = 1 ∨ width = 2) ∧ optionMaskInFiniteEnvelope mask
  | .forward .. => True
  | .fixed .. => True
  | .omr entry mask => 0 < entry ∧ entry < 16 ∧ optionMaskInFiniteEnvelope mask
  | .matrix _ width row => (width = 1 ∨ width = 2 ∨ width = 4) ∧ optionNatInFiniteEnvelope 16 row
  | .nowrite => True
  | .l1bm width address => (width = 1 ∨ width = 2 ∨ width = 4) ∧ optionNatInFiniteEnvelope 8192 address
  | .l2bm address l2b => address < 32768 ∧ optionNatInFiniteEnvelope 8 l2b
  | .dar address => address < 1024

theorem ParsedOperand.mem_inFiniteEnvelope_iff (access : Access) (neg ext rnd : Bool)
    (mask : Option ParsedMask) :
    ParsedOperand.inFiniteEnvelope (.mem access neg ext rnd mask) ↔
      access.inFiniteEnvelope ∧ optionMaskInFiniteEnvelope mask := Iff.rfl

theorem ParsedOperand.bar_inFiniteEnvelope_iff (lm1 : Bool) (width : Nat)
    (mask : Option ParsedMask) :
    ParsedOperand.inFiniteEnvelope (.bar lm1 width mask) ↔
      (width = 1 ∨ width = 2) ∧ optionMaskInFiniteEnvelope mask := Iff.rfl

theorem ParsedOperand.omr_inFiniteEnvelope_iff (entry : Nat)
    (mask : Option ParsedMask) :
    ParsedOperand.inFiniteEnvelope (.omr entry mask) ↔
      0 < entry ∧ entry < 16 ∧ optionMaskInFiniteEnvelope mask := Iff.rfl

theorem ParsedOperand.matrix_inFiniteEnvelope_iff (y : Bool) (width : Nat)
    (row : Option Nat) :
    ParsedOperand.inFiniteEnvelope (.matrix y width row) ↔
      (width = 1 ∨ width = 2 ∨ width = 4) ∧
        optionNatInFiniteEnvelope 16 row := Iff.rfl

theorem ParsedOperand.l1bm_inFiniteEnvelope_iff (width : Nat) (address : Option Nat) :
    ParsedOperand.inFiniteEnvelope (.l1bm width address) ↔
      (width = 1 ∨ width = 2 ∨ width = 4) ∧
        optionNatInFiniteEnvelope 8192 address := Iff.rfl

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
      have widthLT : width < 5 := by rcases widthBound with h | h <;> omega
      exact operandBarCode (lm1, ⟨width, widthLT⟩,
        optionMaskFiniteCode ⟨mask, maskBound⟩)
  | forward kind neg ext rnd =>
      exact operandForwardCode (kind.finiteCode, neg, ext, rnd)
  | fixed kind =>
      exact operandFixedCode kind.finiteCode
  | omr entry mask =>
      rcases bounds with ⟨positive, entryBound, maskBound⟩
      exact operandOmrCode (⟨entry, entryBound⟩,
        optionMaskFiniteCode ⟨mask, maskBound⟩)
  | matrix y width row =>
      rcases bounds with ⟨widthBound, rowBound⟩
      have widthLT : width < 5 := by rcases widthBound with h | h | h <;> omega
      exact operandMatrixCode (y, ⟨width, widthLT⟩,
        optionNatFiniteCode 16 ⟨row, rowBound⟩)
  | nowrite => exact operandNowriteCode
  | l1bm width address =>
      rcases bounds with ⟨widthBound, addressBound⟩
      have widthLT : width < 5 := by rcases widthBound with h | h | h <;> omega
      exact operandL1bmCode (⟨width, widthLT⟩,
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
operand envelope ranges over a finite type. Destination lists use a separate
bound because Rust assigns the remaining token suffix to destinations without
a parser-side length bound. -/
def ParsedExpr.sourcesInFiniteEnvelope (expression : ParsedExpr) : Prop :=
  expression.sources.length ≤ 3 ∧
    ∀ operand ∈ expression.sources, operand.inFiniteEnvelope

theorem ParsedExpr.sourcesInFiniteEnvelope_of_parserArity
    (expression : ParsedExpr)
    (arity : expression.sourcesMatchParserArity)
    (operands : ∀ operand ∈ expression.sources, operand.inFiniteEnvelope) :
    expression.sourcesInFiniteEnvelope :=
  ⟨expression.sources_length_le_three arity, operands⟩

private def ParsedOperand.listFiniteCode (bound : Nat)
    (operands : {operands : List ParsedOperand //
      operands.length ≤ bound ∧ ∀ operand ∈ operands, operand.inFiniteEnvelope}) :
    {values : List {operand : ParsedOperand // operand.inFiniteEnvelope} //
      values.length ≤ bound} := by
  let values := operands.1.attach.map fun operand =>
    (⟨operand.1, operands.2.2 operand.1 operand.2⟩ :
      {operand : ParsedOperand // operand.inFiniteEnvelope})
  refine ⟨values, ?_⟩
  simpa [values] using operands.2.1

private theorem ParsedOperand.listFiniteCode_injective (bound : Nat) :
    Function.Injective (ParsedOperand.listFiniteCode bound) := by
  intro a b equal
  apply Subtype.ext
  have valueEqual := congrArg (fun values => values.1.map Subtype.val) equal
  simpa [ParsedOperand.listFiniteCode, List.attach_map_val] using valueEqual

theorem ParsedOperand.listInFiniteEnvelope_finite (bound : Nat) :
    Finite {operands : List ParsedOperand //
      operands.length ≤ bound ∧ ∀ operand ∈ operands, operand.inFiniteEnvelope} := by
  let Operand := {operand : ParsedOperand // operand.inFiniteEnvelope}
  letI : Finite Operand := ParsedOperand.inFiniteEnvelope_finite
  letI : Finite {values : List Operand // values.length ≤ bound} :=
    listLengthLE_finite Operand bound
  exact Finite.of_injective (ParsedOperand.listFiniteCode bound)
    (ParsedOperand.listFiniteCode_injective bound)

/-- Lean's `Char` has no built-in `Finite` instance. Unicode scalar values
still form a finite carrier, encoded by their code points below U+110000. -/
private def charFiniteCode (character : Char) : Fin 0x110000 := by
  refine ⟨character.toNat, ?_⟩
  have valid := character.valid
  change character.val < 0xd800 ∨
    (0xdfff < character.val ∧ character.val < 0x110000) at valid
  have codeBound : character.val.toNat < 0x110000 := by
    rcases valid with below | ⟨_, below⟩
    · have belowNat := UInt32.lt_iff_toNat_lt.mp below
      exact Nat.lt_trans belowNat (by decide)
    · exact UInt32.lt_iff_toNat_lt.mp below
  change character.val.toNat < 0x110000
  exact codeBound

private theorem charFiniteCode_injective : Function.Injective charFiniteCode := by
  intro a b equal
  have valuesEqual := congrArg Fin.val equal
  change a.toNat = b.toNat at valuesEqual
  exact Char.toNat_inj.mp valuesEqual

theorem char_finite : Finite Char :=
  Finite.of_injective charFiniteCode charFiniteCode_injective

private def ParsedRrn.unrestrictedFiniteCode (rrn : ParsedRrn) : Fin 0x110000 × Fin 8 :=
  (charFiniteCode rrn.precision, ParsedRrnOp.finiteCode rrn.op)

private theorem ParsedRrn.unrestrictedFiniteCode_injective :
    Function.Injective ParsedRrn.unrestrictedFiniteCode := by
  intro a b equal
  cases a with
  | mk ap ao =>
    cases b with
    | mk bp bo =>
      simp only [ParsedRrn.unrestrictedFiniteCode, Prod.mk.injEq] at equal
      have charNatEqual : ap.toNat = bp.toNat := by
        have codeEqual := congrArg Fin.val equal.1
        simpa [charFiniteCode] using codeEqual
      have precisionEqual := Char.toNat_inj.mp charNatEqual
      have opEqual := ParsedRrnOp.finiteCode_injective equal.2
      cases precisionEqual
      cases opEqual
      rfl

theorem ParsedRrn.finite : Finite ParsedRrn :=
  Finite.of_injective ParsedRrn.unrestrictedFiniteCode
    ParsedRrn.unrestrictedFiniteCode_injective

def ParsedAluName.finiteCode : ParsedAluName → Fin 32
  | .msl => 0 | .msr => 1 | .passa => 2 | .inc => 3
  | .dec => 4 | .not => 5 | .lnot => 6 | .rsqrt => 7
  | .floor => 8 | .ftoi => 9 | .bfe => 10 | .bfn => 11
  | .max => 12 | .min => 13 | .packbit => 14 | .and => 15
  | .or => 16 | .xor => 17 | .add => 18 | .sub => 19
  | .lsl => 20 | .lsr => 21 | .bsl => 22 | .bsr => 23
  | .relu => 24 | .relu0 => 25 | .relu1 => 26 | .relu2 => 27
  | .relu3 => 28 | .lrelud => 29 | .lreluo => 30 | .ilrelud => 31

theorem ParsedAluName.finiteCode_injective :
    Function.Injective ParsedAluName.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedAluName.finiteCode] at equal ⊢

theorem ParsedAluName.finite : Finite ParsedAluName :=
  Finite.of_injective ParsedAluName.finiteCode ParsedAluName.finiteCode_injective

def ParsedPrecision.finiteCode (precision : ParsedPrecision) : Fin 7 :=
  ⟨precision.code, by cases precision <;> decide⟩

theorem ParsedPrecision.finiteCode_injective :
    Function.Injective ParsedPrecision.finiteCode := by
  intro a b equal
  apply ParsedPrecision.code_injective
  exact congrArg Fin.val equal

theorem ParsedPrecision.finite : Finite ParsedPrecision :=
  Finite.of_injective ParsedPrecision.finiteCode ParsedPrecision.finiteCode_injective

def CalcKind.finiteCode : CalcKind → Fin 4
  | .fma => 0 | .mul => 1 | .add => 2 | .passa => 3

theorem CalcKind.finiteCode_injective : Function.Injective CalcKind.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [CalcKind.finiteCode] at equal ⊢

theorem CalcKind.finite : Finite CalcKind :=
  Finite.of_injective CalcKind.finiteCode CalcKind.finiteCode_injective

abbrev ParsedMvKindFiniteCode := Fin 9 × Option ParsedRrn

private def ParsedMvKind.finiteCode : ParsedMvKind → ParsedMvKindFiniteCode
  | .nop => (0, none)
  | .copy => (1, none)
  | .broadcast => (2, none)
  | .broadcast2 => (3, none)
  | .broadcast4 => (4, none)
  | .distribute => (5, none)
  | .reduce rrn => (6, some rrn)
  | .reduce2 rrn => (7, some rrn)
  | .reduce4 rrn => (8, some rrn)

private theorem ParsedMvKind.finiteCode_injective :
    Function.Injective ParsedMvKind.finiteCode := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedMvKind.finiteCode] at equal ⊢
  all_goals assumption

theorem ParsedMvKind.finite : Finite ParsedMvKind := by
  letI : Finite ParsedRrn := ParsedRrn.finite
  letI : Fintype ParsedRrn := Fintype.ofFinite ParsedRrn
  letI : Fintype ParsedMvKindFiniteCode := inferInstance
  exact Finite.of_injective ParsedMvKind.finiteCode ParsedMvKind.finiteCode_injective

abbrev ParsedMvOperandFiniteCode :=
  Fin 3 × Fin (2 ^ 64) × Option (Fin 256) × Bool × Option (Fin 256)

private def ParsedMvOperand.finiteCode (operand : ParsedMvOperand) :
    ParsedMvOperandFiniteCode :=
  match operand with
  | .pdm address group => (0, address, group, false, none)
  | .dram address group indirect => (1, address, group, indirect, none)
  | .l2bm address group l2b => (2, address, group, false, l2b)

private theorem ParsedMvOperand.finiteCode_injective :
    Function.Injective ParsedMvOperand.finiteCode := by
  intro a b equal
  cases a <;> cases b <;>
    simp [ParsedMvOperand.finiteCode] at equal ⊢
  all_goals assumption

theorem ParsedMvOperand.finite : Finite ParsedMvOperand := by
  letI : Fintype ParsedMvOperandFiniteCode := inferInstance
  exact Finite.of_injective ParsedMvOperand.finiteCode
    ParsedMvOperand.finiteCode_injective

abbrev NormalizedMvFiniteCode :=
  ParsedMvKind × Fin (2 ^ 64) × Option (Fin 256) × Option (Fin (2 ^ 32)) ×
    Fin 256 × Option ParsedMvOperand × Option ParsedMvOperand

private def NormalizedMv.finiteCode (transfer : NormalizedMv) : NormalizedMvFiniteCode :=
  (transfer.kind, transfer.size, transfer.tag, transfer.nd, transfer.priority,
    transfer.source, transfer.destination)

private theorem NormalizedMv.finiteCode_injective :
    Function.Injective NormalizedMv.finiteCode := by
  intro a b equal
  cases a with
  | mk ak asize atag and apriority asource adestination =>
    cases b with
    | mk bk bsize btag bnd bpriority bsource bdestination =>
      simp [NormalizedMv.finiteCode] at equal
      rcases equal with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

theorem NormalizedMv.finite : Finite NormalizedMv := by
  letI : Finite ParsedMvKind := ParsedMvKind.finite
  letI : Fintype ParsedMvKind := Fintype.ofFinite ParsedMvKind
  letI : Finite ParsedMvOperand := ParsedMvOperand.finite
  letI : Fintype ParsedMvOperand := Fintype.ofFinite ParsedMvOperand
  letI : Fintype NormalizedMvFiniteCode := inferInstance
  exact Finite.of_injective NormalizedMv.finiteCode NormalizedMv.finiteCode_injective

/-- MV sizes need no extra envelope restriction: the parsed representation
already stores them in `Fin (2^64)`, matching the Rust parser's `u64` field.
The assembler's stricter accepted sizes are a separate correspondence fact;
they must not be assumed to prove finiteness of parser-representable lines. -/
def NormalizedMv.sizeInFiniteEnvelope (transfer : NormalizedMv) : Prop :=
  True

theorem ParsedMv.normalize_sizeInFiniteEnvelope (transfer : ParsedMv) :
    transfer.normalize.sizeInFiniteEnvelope :=
  True.intro

theorem mv_size_1_in_envelope :
    NormalizedMv.sizeInFiniteEnvelope
      ({kind := .copy, size := ⟨1, by decide⟩, tag := none, nd := none,
        priority := 0, source := none, destination := none} : NormalizedMv) := by
  trivial

theorem mv_size_32768_in_envelope :
    NormalizedMv.sizeInFiniteEnvelope
      ({kind := .copy, size := ⟨32768, by decide⟩, tag := none, nd := none,
        priority := 0, source := none, destination := none} : NormalizedMv) := by
  trivial

theorem NormalizedMv.sizeInFiniteEnvelope_finite :
    Finite {transfer : NormalizedMv // transfer.sizeInFiniteEnvelope} := by
  letI : Finite NormalizedMv := NormalizedMv.finite
  exact Finite.of_injective (fun transfer : {transfer : NormalizedMv //
      transfer.sizeInFiniteEnvelope} => transfer.1)
    (by
      intro a b equal
      exact Subtype.ext equal)

theorem ParsedExpr.sourcesInFiniteEnvelope_finite :
    Finite {sources : List ParsedOperand //
      sources.length ≤ 3 ∧ ∀ operand ∈ sources, operand.inFiniteEnvelope} :=
  ParsedOperand.listInFiniteEnvelope_finite 3

/-- Destination lists whose operands lie in the finite operand envelope and
contain no duplicate parsed operand. This is a finite-carrier condition, not
yet a consequence proved from `LegalParsedLine`: operand-role validation and
assembler acceptance must justify it before this envelope can cover all legal
source lines. -/
def ParsedExpr.destinationsInFiniteEnvelope (expression : ParsedExpr) : Prop :=
  expression.destinations.Nodup ∧
    ∀ operand ∈ expression.destinations, operand.inFiniteEnvelope

abbrev ParsedOperandNodupListFiniteEnvelope :=
  {operands : List ParsedOperand //
    operands.Nodup ∧ ∀ operand ∈ operands, operand.inFiniteEnvelope}

private def ParsedOperand.nodupListFiniteCode
    [Fintype {operand : ParsedOperand // operand.inFiniteEnvelope}]
    (operands : ParsedOperandNodupListFiniteEnvelope) :
    {values : List {operand : ParsedOperand // operand.inFiniteEnvelope} //
      values.length ≤ Fintype.card {operand : ParsedOperand // operand.inFiniteEnvelope}} := by
  classical
  let toOperand := fun operand : {operand : ParsedOperand // operand ∈ operands.1} =>
    (⟨operand.1, operands.2.2 operand.1 operand.2⟩ :
      {operand : ParsedOperand // operand.inFiniteEnvelope})
  let values := operands.1.attach.map toOperand
  have valuesNodup : values.Nodup := by
    apply List.Nodup.map
    · intro a b equal
      exact Subtype.ext
        (congrArg
          (fun operand : {operand : ParsedOperand // operand.inFiniteEnvelope} => operand.1)
          equal)
    · exact List.nodup_attach.mpr operands.2.1
  refine ⟨values, ?_⟩
  exact nodup_length_le_fintype_card values valuesNodup

private theorem ParsedOperand.nodupListFiniteCode_injective
    [Fintype {operand : ParsedOperand // operand.inFiniteEnvelope}] :
    Function.Injective ParsedOperand.nodupListFiniteCode := by
  intro a b equal
  apply Subtype.ext
  have valueEqual := congrArg (fun values => values.1.map Subtype.val) equal
  simpa [ParsedOperand.nodupListFiniteCode, List.attach_map_val] using valueEqual

theorem ParsedExpr.destinationsInFiniteEnvelope_finite :
    Finite ParsedOperandNodupListFiniteEnvelope := by
  classical
  let Operand := {operand : ParsedOperand // operand.inFiniteEnvelope}
  letI : Finite Operand := ParsedOperand.inFiniteEnvelope_finite
  letI : Fintype Operand := Fintype.ofFinite Operand
  letI : Finite {values : List Operand //
      values.length ≤ Fintype.card Operand} :=
    listLengthLE_finite Operand (Fintype.card Operand)
  exact Finite.of_injective ParsedOperand.nodupListFiniteCode
    ParsedOperand.nodupListFiniteCode_injective

/-- `mask` is an eight-bit bitmap of selected L1Bs (so the full set is 255);
`immode` is the three-bit selector mode. -/
def ParsedL1bSet.inFiniteEnvelope (set : ParsedL1bSet) : Prop :=
  set.mask < 256 ∧ set.immode < 8

def ParsedL1bSet.finiteCode
    (set : {set : ParsedL1bSet // set.inFiniteEnvelope}) : Fin 256 × Fin 8 :=
  (⟨set.1.mask, set.2.1⟩, ⟨set.1.immode, set.2.2⟩)

theorem ParsedL1bSet.fullSelectorMask_inFiniteEnvelope :
    ParsedL1bSet.inFiniteEnvelope ⟨255, 7⟩ := by
  simp [ParsedL1bSet.inFiniteEnvelope]

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
  Fin 10 × (Fin 256 × Fin 8) × (Fin 128 × Fin 8) × Fin 8 × Fin 512

def ParsedL2Op.inFiniteEnvelope : ParsedL2Op → Prop
  | .bcast set | .bcast2 set | .distrib set | .imcast set => set.inFiniteEnvelope
  | .fromL1b index => index < 8
  | .reduce rrn set => rrn.inFiniteEnvelope ∧ set.inFiniteEnvelope
  | .reduce2 rrn => rrn.inFiniteEnvelope
  | .gather | .dars | .darw => True

private def ParsedL2Op.finiteCode
    (op : {op : ParsedL2Op // op.inFiniteEnvelope}) : ParsedL2OpFiniteCode :=
  let noSet : Fin 256 × Fin 8 := (0, 0)
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

abbrev ParsedOpAluFiniteCode :=
  ParsedAluName × Option ParsedPrecision × Bool × Option (Fin 10)
abbrev ParsedOpMauFiniteCode :=
  ParsedPrecision × Bool × CalcKind × Option Char × Bool
abbrev ParsedOpImmediateFiniteCode := Fin (2 ^ 32) × Bool
abbrev ParsedOpFiniteCode :=
  Sum ParsedOpAluFiniteCode
    (Sum ParsedOpImmediateFiniteCode
      (Sum PUnit.{1}
        (Sum ParsedOpMauFiniteCode
          (Sum ParsedPrecision
            (Sum ParsedPrecision
              (Sum (Fin 256)
                (Sum PUnit.{1}
                  (Sum ParsedL1OpFiniteCode ParsedL2OpFiniteCode))))))))

private noncomputable instance : Fintype Char := by
  letI : Finite Char := char_finite
  exact Fintype.ofFinite Char
private noncomputable instance : Fintype ParsedAluName := by
  letI : Finite ParsedAluName := ParsedAluName.finite
  exact Fintype.ofFinite ParsedAluName
private noncomputable instance : Fintype ParsedPrecision := by
  letI : Finite ParsedPrecision := ParsedPrecision.finite
  exact Fintype.ofFinite ParsedPrecision
private noncomputable instance : Fintype CalcKind := by
  letI : Finite CalcKind := CalcKind.finite
  exact Fintype.ofFinite CalcKind
private noncomputable instance : Fintype ParsedOpAluFiniteCode := inferInstance
private noncomputable instance : Fintype ParsedOpImmediateFiniteCode := inferInstance
private noncomputable instance : Fintype ParsedOpMauFiniteCode := inferInstance
private noncomputable instance : Fintype ParsedL1OpFiniteCode := inferInstance
private noncomputable instance : Fintype ParsedL2OpFiniteCode := inferInstance
private noncomputable instance : Fintype ParsedOpFiniteCode := inferInstance

private def parsedOpAluCode (code : ParsedOpAluFiniteCode) : ParsedOpFiniteCode :=
  Sum.inl code
private def parsedOpImmediateCode (code : ParsedOpImmediateFiniteCode) : ParsedOpFiniteCode :=
  Sum.inr (Sum.inl code)
private def parsedOpZeroCode : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inl PUnit.unit))
private def parsedOpMauCode (code : ParsedOpMauFiniteCode) : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl code)))
private def parsedOpMatrixWriteCode (code : ParsedPrecision) : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code))))
private def parsedOpMatrixReadCode (code : ParsedPrecision) : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code)))))
private def parsedOpWaitCode (code : Fin 256) : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl code))))))
private abbrev ParsedOpTail9 := Sum ParsedL1OpFiniteCode ParsedL2OpFiniteCode
private abbrev ParsedOpTail8 := Sum PUnit.{1} ParsedOpTail9
private abbrev ParsedOpTail7 := Sum (Fin 256) ParsedOpTail8
private abbrev ParsedOpTail6 := Sum ParsedPrecision ParsedOpTail7
private abbrev ParsedOpTail5 := Sum ParsedPrecision ParsedOpTail6
private abbrev ParsedOpTail4 := Sum ParsedOpMauFiniteCode ParsedOpTail5
private abbrev ParsedOpTail3 := Sum PUnit.{1} ParsedOpTail4
private abbrev ParsedOpTail2 := Sum ParsedOpImmediateFiniteCode ParsedOpTail3
private abbrev ParsedOpTail1 := Sum ParsedOpAluFiniteCode ParsedOpTail2
private def parsedOpTail9L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail9 := Sum.inl code
private def parsedOpTail9L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail9 := Sum.inr code
private def parsedOpTail8L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail8 :=
  Sum.inr (parsedOpTail9L1 code)
private def parsedOpTail8L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail8 :=
  Sum.inr (parsedOpTail9L2 code)
private def parsedOpTail7L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail7 :=
  Sum.inr (parsedOpTail8L1 code)
private def parsedOpTail7L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail7 :=
  Sum.inr (parsedOpTail8L2 code)
private def parsedOpTail6L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail6 :=
  Sum.inr (parsedOpTail7L1 code)
private def parsedOpTail6L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail6 :=
  Sum.inr (parsedOpTail7L2 code)
private def parsedOpTail5L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail5 :=
  Sum.inr (parsedOpTail6L1 code)
private def parsedOpTail5L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail5 :=
  Sum.inr (parsedOpTail6L2 code)
private def parsedOpTail4L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail4 :=
  Sum.inr (parsedOpTail5L1 code)
private def parsedOpTail4L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail4 :=
  Sum.inr (parsedOpTail5L2 code)
private def parsedOpTail3L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail3 :=
  Sum.inr (parsedOpTail4L1 code)
private def parsedOpTail3L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail3 :=
  Sum.inr (parsedOpTail4L2 code)
private def parsedOpTail2L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail2 :=
  Sum.inr (parsedOpTail3L1 code)
private def parsedOpTail2L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail2 :=
  Sum.inr (parsedOpTail3L2 code)
private def parsedOpTail1L1 (code : ParsedL1OpFiniteCode) : ParsedOpTail1 :=
  Sum.inr (parsedOpTail2L1 code)
private def parsedOpTail1L2 (code : ParsedL2OpFiniteCode) : ParsedOpTail1 :=
  Sum.inr (parsedOpTail2L2 code)
private def parsedOpNoforwardCode : ParsedOpFiniteCode :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inl PUnit.unit)))))))
private def parsedOpL1bmCode (code : ParsedL1OpFiniteCode) : ParsedOpFiniteCode :=
  parsedOpTail1L1 code
private def parsedOpL2bmCode (code : ParsedL2OpFiniteCode) : ParsedOpFiniteCode :=
  parsedOpTail1L2 code

def ParsedOp.inFiniteEnvelope : ParsedOp → Prop
  | .alu _ _ _ arg => parsedBfArgInFiniteEnvelope arg
  | .immediate .. | .zero | .mau .. | .matrixWrite .. | .matrixRead .. | .noforward => True
  | .wait tag => waitTagInFiniteEnvelope tag
  | .l1bm op => op.inFiniteEnvelope
  | .l2bm op => op.inFiniteEnvelope

private def ParsedOp.finiteCode
    (op : {op : ParsedOp // op.inFiniteEnvelope}) : ParsedOpFiniteCode := by
  rcases op with ⟨op, bound⟩
  cases op with
  | alu name precision unsigned arg =>
      exact parsedOpAluCode (name, precision, unsigned,
        parsedBfArgFiniteCode ⟨arg, bound⟩)
  | immediate value unsigned => exact parsedOpImmediateCode (value.toFin, unsigned)
  | zero => exact parsedOpZeroCode
  | mau precision matrix kind half round =>
      exact parsedOpMauCode (precision, matrix, kind, half, round)
  | matrixWrite precision => exact parsedOpMatrixWriteCode precision
  | matrixRead precision => exact parsedOpMatrixReadCode precision
  | wait tag => exact parsedOpWaitCode (waitTagFiniteCode ⟨tag, bound⟩)
  | noforward => exact parsedOpNoforwardCode
  | l1bm operation => exact parsedOpL1bmCode (ParsedL1Op.finiteCode ⟨operation, bound⟩)
  | l2bm operation => exact parsedOpL2bmCode (ParsedL2Op.finiteCode ⟨operation, bound⟩)

private theorem ParsedOp.finiteCode_injective : Function.Injective ParsedOp.finiteCode := by
  intro a b equal
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  apply Subtype.ext
  cases a <;> cases b <;>
    simp_all [ParsedOp.finiteCode, parsedOpAluCode, parsedOpImmediateCode,
      parsedOpZeroCode, parsedOpMauCode, parsedOpMatrixWriteCode,
      parsedOpMatrixReadCode, parsedOpWaitCode, parsedOpNoforwardCode,
      parsedOpL1bmCode, parsedOpL2bmCode, parsedOpTail1L1, parsedOpTail1L2,
      parsedOpTail2L1, parsedOpTail2L2, parsedOpTail3L1, parsedOpTail3L2,
      parsedOpTail4L1, parsedOpTail4L2, parsedOpTail5L1, parsedOpTail5L2,
      parsedOpTail6L1, parsedOpTail6L2, parsedOpTail7L1, parsedOpTail7L2,
      parsedOpTail8L1, parsedOpTail8L2, parsedOpTail9L1, parsedOpTail9L2]
  all_goals
    first
    | rcases equal with ⟨_, _, _, argCodeEqual⟩
      exact congrArg Subtype.val (parsedBfArgFiniteCode_injective argCodeEqual)
    | exact BitVec.toFin_inj.mp equal.1
    | exact congrArg Fin.val equal
    | exact congrArg Subtype.val (ParsedL1Op.finiteCode_injective equal)
    | exact congrArg Subtype.val (ParsedL2Op.finiteCode_injective equal)

theorem ParsedOp.inFiniteEnvelope_finite :
    Finite {op : ParsedOp // op.inFiniteEnvelope} := by
  letI : Finite ParsedAluName := ParsedAluName.finite
  letI : Finite ParsedPrecision := ParsedPrecision.finite
  letI : Finite CalcKind := CalcKind.finite
  letI : Finite Char := char_finite
  letI : Finite {op : ParsedL1Op // op.inFiniteEnvelope} :=
    ParsedL1Op.inFiniteEnvelope_finite
  letI : Finite {op : ParsedL2Op // op.inFiniteEnvelope} :=
    ParsedL2Op.inFiniteEnvelope_finite
  exact Finite.of_injective ParsedOp.finiteCode ParsedOp.finiteCode_injective

abbrev ParsedOperandListFiniteEnvelope (bound : Nat) :=
  {operands : List ParsedOperand //
    operands.length ≤ bound ∧ ∀ operand ∈ operands, operand.inFiniteEnvelope}

def NormalizedExpr.inFiniteEnvelope (expression : NormalizedExpr) : Prop :=
  expression.op.inFiniteEnvelope ∧
    expression.parserSourceArityValid ∧
    expression.sourcesPassRoleScreen ∧
    expression.forwardingSourcePositionsValid ∧
    expression.blockDestinationArityValid ∧
    expression.sources.length ≤ 3 ∧
    (∀ operand ∈ expression.sources, operand.inFiniteEnvelope) ∧
    expression.destinations.Nodup ∧
    ParsedOperand.destinationsAvoidKnownSourceOnly expression.destinations ∧
    (∀ operand ∈ expression.destinations, operand.inFiniteEnvelope) ∧
    expression.destinationsPassRoleScreen ∧
    optionMaskInFiniteEnvelope expression.flush

/-- The exact parsed-expression facts needed to normalize into the finite
carrier. The source bound is derived from parser opcode arity; destination
uniqueness, numeric ranges, and flush ranges remain parser/assembler
correspondence obligations. -/
def ParsedExpr.inFiniteEnvelope (expression : ParsedExpr) : Prop :=
  expression.op.inFiniteEnvelope ∧
    expression.parserSourceArityValid ∧
    expression.sourcesPassRoleScreen ∧
    expression.forwardingSourcePositionsValid ∧
    expression.blockDestinationArityValid ∧
    (∀ operand ∈ expression.sources, operand.inFiniteEnvelope) ∧
    expression.destinations.Nodup ∧
    ParsedOperand.destinationsAvoidKnownSourceOnly expression.destinations ∧
    (∀ operand ∈ expression.destinations, operand.inFiniteEnvelope) ∧
    expression.destinationsPassRoleScreen ∧
    optionMaskInFiniteEnvelope expression.flush

theorem ParsedExpr.inFiniteEnvelope_destinationRolesPassScreen
    (expression : ParsedExpr) (envelope : expression.inFiniteEnvelope) :
    expression.destinationsPassRoleScreen := by
  rcases envelope with ⟨_, _, _, _, _, _, _, _, _, roles, _⟩
  exact roles

theorem ParsedExpr.inFiniteEnvelope_sourceRolesPassScreen
    (expression : ParsedExpr) (envelope : expression.inFiniteEnvelope) :
    expression.sourcesPassRoleScreen := by
  rcases envelope with ⟨_, _, roles, _, _, _, _, _, _, _⟩
  exact roles

theorem ParsedExpr.inFiniteEnvelope_forwardingSourcePositionsValid
    (expression : ParsedExpr) (envelope : expression.inFiniteEnvelope) :
    expression.forwardingSourcePositionsValid := by
  rcases envelope with ⟨_, _, _, positions, _, _, _, _, _, _, _⟩
  exact positions

theorem ParsedExpr.normalize_inFiniteEnvelope (expression : ParsedExpr)
    (envelope : expression.inFiniteEnvelope) :
    expression.normalize.inFiniteEnvelope := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  rcases envelope with ⟨opBound, sourceArity, sourceRoles, sourcePositions,
    destinationArity, sourceBound, destinationNodup, destinationRoles,
    destinationBound, opcodeRoles, flushBound⟩
  have normalizedArity :
      (NormalizedExpr.mk op sources destinations flush).parserSourceArityValid :=
    sourceArity
  have normalizedDestinationArity :
      (NormalizedExpr.mk op sources destinations flush).blockDestinationArityValid :=
    destinationArity
  have normalizedSourceRoles :
      (NormalizedExpr.mk op sources destinations flush).sourcesPassRoleScreen :=
    sourceRoles
  have normalizedSourcePositions :
      (NormalizedExpr.mk op sources destinations flush).forwardingSourcePositionsValid :=
    sourcePositions
  simp only [ParsedExpr.normalize, NormalizedExpr.inFiniteEnvelope]
  exact ⟨opBound,
    sourceArity,
    normalizedSourceRoles,
    normalizedSourcePositions,
    normalizedDestinationArity,
    NormalizedExpr.parserSourceArityValid_length_le_three _ normalizedArity,
    sourceBound, destinationNodup, destinationRoles, destinationBound,
    opcodeRoles, flushBound⟩

private abbrev NormalizedExprFiniteCode :=
  {op : ParsedOp // op.inFiniteEnvelope} ×
    ParsedOperandListFiniteEnvelope 3 ×
    ParsedOperandNodupListFiniteEnvelope ×
    {flush : Option ParsedMask // optionMaskInFiniteEnvelope flush}

private def NormalizedExpr.finiteCode
    (expression : {expression : NormalizedExpr // expression.inFiniteEnvelope}) :
    NormalizedExprFiniteCode := by
  rcases expression with ⟨expression, bounds⟩
  rcases expression with ⟨op, sources, destinations, flush⟩
  rcases bounds with ⟨opBound, sourceArity, sourceRoles, sourcePositions,
    destinationArity, sourceLength, sourceBound, destinationNodup,
    destinationRoles, destinationBound, opcodeRoles, flushBound⟩
  exact (⟨op, opBound⟩,
    ⟨sources, sourceLength, sourceBound⟩,
    ⟨destinations, destinationNodup, destinationBound⟩,
    ⟨flush, flushBound⟩)

private theorem NormalizedExpr.finiteCode_injective :
    Function.Injective NormalizedExpr.finiteCode := by
  intro a b equal
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  apply Subtype.ext
  cases a with
  | mk aop asources adestinations aflush =>
    cases b with
    | mk bop bsources bdestinations bflush =>
      simp only [NormalizedExpr.finiteCode, Prod.mk.injEq] at equal
      rcases equal with ⟨opEqual, sourceEqual, destinationEqual, flushEqual⟩
      have opValueEqual := congrArg Subtype.val opEqual
      have sourceValueEqual := congrArg Subtype.val sourceEqual
      have destinationValueEqual := congrArg Subtype.val destinationEqual
      have flushValueEqual := congrArg Subtype.val flushEqual
      cases opValueEqual
      cases sourceValueEqual
      cases destinationValueEqual
      cases flushValueEqual
      rfl

theorem NormalizedExpr.inFiniteEnvelope_finite :
    Finite {expression : NormalizedExpr // expression.inFiniteEnvelope} := by
  classical
  letI : Finite {op : ParsedOp // op.inFiniteEnvelope} :=
    ParsedOp.inFiniteEnvelope_finite
  letI : Finite (ParsedOperandListFiniteEnvelope 3) :=
    ParsedOperand.listInFiniteEnvelope_finite 3
  letI : Finite ParsedOperandNodupListFiniteEnvelope :=
    ParsedExpr.destinationsInFiniteEnvelope_finite
  letI : Finite {flush : Option ParsedMask // optionMaskInFiniteEnvelope flush} :=
    optionMaskInFiniteEnvelope_finite
  letI : Fintype {op : ParsedOp // op.inFiniteEnvelope} := Fintype.ofFinite _
  letI : Fintype (ParsedOperandListFiniteEnvelope 3) := Fintype.ofFinite _
  letI : Fintype ParsedOperandNodupListFiniteEnvelope := Fintype.ofFinite _
  letI : Fintype {flush : Option ParsedMask // optionMaskInFiniteEnvelope flush} :=
    Fintype.ofFinite _
  letI : Fintype NormalizedExprFiniteCode := inferInstance
  exact Finite.of_injective NormalizedExpr.finiteCode
    NormalizedExpr.finiteCode_injective

abbrev NormalizedExprListFiniteEnvelope (bound : Nat) :=
  {expressions : List NormalizedExpr //
    expressions.length ≤ bound ∧
      ∀ expression ∈ expressions, expression.inFiniteEnvelope}

private def NormalizedExpr.listFiniteCode (bound : Nat)
    (expressions : NormalizedExprListFiniteEnvelope bound) :
    {values : List {expression : NormalizedExpr // expression.inFiniteEnvelope} //
      values.length ≤ bound} := by
  let values := expressions.1.attach.map fun expression =>
    (⟨expression.1, expressions.2.2 expression.1 expression.2⟩ :
      {expression : NormalizedExpr // expression.inFiniteEnvelope})
  refine ⟨values, ?_⟩
  simpa [values] using expressions.2.1

private theorem NormalizedExpr.listFiniteCode_injective (bound : Nat) :
    Function.Injective (NormalizedExpr.listFiniteCode bound) := by
  intro a b equal
  apply Subtype.ext
  have valueEqual := congrArg (fun values => values.1.map Subtype.val) equal
  simpa [NormalizedExpr.listFiniteCode, List.attach_map_val] using valueEqual

theorem NormalizedExpr.listInFiniteEnvelope_finite (bound : Nat) :
    Finite (NormalizedExprListFiniteEnvelope bound) := by
  let Expression := {expression : NormalizedExpr // expression.inFiniteEnvelope}
  letI : Finite Expression := NormalizedExpr.inFiniteEnvelope_finite
  letI : Fintype Expression := Fintype.ofFinite Expression
  letI : Finite {values : List Expression // values.length ≤ bound} :=
    listLengthLE_finite Expression bound
  exact Finite.of_injective (NormalizedExpr.listFiniteCode bound)
    (NormalizedExpr.listFiniteCode_injective bound)

abbrev InstructionLineWaitFiniteEnvelope (wait : Option Nat) : Prop :=
  optionWaitTagInFiniteEnvelope wait

def InstructionLine.inFiniteEnvelope (bound : Nat) : InstructionLine → Prop
  | .pe expressions =>
      expressions.length ≤ 10 ∧
        ∀ expression ∈ expressions, expression.inFiniteEnvelope
  | .nop count wait => count.val < bound ∧ InstructionLineWaitFiniteEnvelope wait
  | .mv transfer => transfer.sizeInFiniteEnvelope

abbrev InstructionLineFiniteCode (bound : Nat) :=
  NormalizedExprListFiniteEnvelope 10 ⊕
    ((Fin bound × {wait : Option Nat // InstructionLineWaitFiniteEnvelope wait}) ⊕
      {transfer : NormalizedMv // transfer.sizeInFiniteEnvelope})

private def InstructionLine.finiteCode (bound : Nat)
    (line : {line : InstructionLine // line.inFiniteEnvelope bound}) :
    InstructionLineFiniteCode bound := by
  rcases line with ⟨line, bounds⟩
  cases line with
  | pe expressions => exact Sum.inl ⟨expressions, bounds.1, bounds.2⟩
  | nop count wait =>
      exact Sum.inr (Sum.inl (⟨count.val, bounds.1⟩, ⟨wait, bounds.2⟩))
  | mv transfer => exact Sum.inr (Sum.inr ⟨transfer, bounds⟩)

private theorem InstructionLine.finiteCode_injective (bound : Nat) :
    Function.Injective (InstructionLine.finiteCode bound) := by
  intro a b equal
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  apply Subtype.ext
  cases a <;> cases b <;>
    simp_all [InstructionLine.finiteCode, InstructionLine.inFiniteEnvelope]
  case mv.mv =>
    exact congrArg Subtype.val equal
  case nop.nop =>
    apply Subtype.ext
    exact equal.1

theorem InstructionLine.inFiniteEnvelope_finite (bound : Nat) :
    Finite {line : InstructionLine // line.inFiniteEnvelope bound} := by
  classical
  letI : Finite (NormalizedExprListFiniteEnvelope 10) :=
    NormalizedExpr.listInFiniteEnvelope_finite 10
  letI : Fintype (NormalizedExprListFiniteEnvelope 10) := Fintype.ofFinite _
  letI : Finite {wait : Option Nat // InstructionLineWaitFiniteEnvelope wait} :=
    optionWaitTagInFiniteEnvelope_finite
  letI : Fintype {wait : Option Nat // InstructionLineWaitFiniteEnvelope wait} :=
    Fintype.ofFinite _
  letI : Finite NormalizedMv := NormalizedMv.finite
  letI : Fintype NormalizedMv := Fintype.ofFinite _
  letI : Finite {transfer : NormalizedMv // transfer.sizeInFiniteEnvelope} :=
    NormalizedMv.sizeInFiniteEnvelope_finite
  letI : Fintype {transfer : NormalizedMv // transfer.sizeInFiniteEnvelope} :=
    Fintype.ofFinite _
  letI : Fintype (InstructionLineFiniteCode bound) := inferInstance
  exact Finite.of_injective (InstructionLine.finiteCode bound)
    (InstructionLine.finiteCode_injective bound)

def omrEntryInFiniteEnvelope (entry : Nat) : Prop := 0 < entry ∧ entry < 16

private def omrEntryCode
    (entry : {entry : Nat // omrEntryInFiniteEnvelope entry}) : Fin 16 :=
  ⟨entry.1, entry.2.2⟩

private theorem omrEntryCode_injective : Function.Injective omrEntryCode := by
  intro a b equal
  apply Subtype.ext
  exact congrArg Fin.val equal

theorem omrEntryInFiniteEnvelope_finite :
    Finite {entry : Nat // omrEntryInFiniteEnvelope entry} :=
  Finite.of_injective omrEntryCode omrEntryCode_injective

theorem omr_entry_1_in_envelope : omrEntryInFiniteEnvelope 1 := by simp [omrEntryInFiniteEnvelope]

theorem omr_entry_0_outside_envelope : ¬ omrEntryInFiniteEnvelope 0 := by simp [omrEntryInFiniteEnvelope]

theorem omr_entry_16_outside_envelope : ¬ omrEntryInFiniteEnvelope 16 := by simp [omrEntryInFiniteEnvelope]

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

/-- PE issue legality bounds the number of expressions by the ten issue groups.
If each parsed expression has the finite payload facts, normalizing the line
therefore puts it in the bounded PE-line carrier. -/
theorem InstructionLine.pe_inFiniteEnvelope_of_parsed
    (bound : Nat) (expressions : List ParsedExpr)
    (issueLegal : LegalParsedLine expressions)
    (payload : ∀ expression ∈ expressions, expression.inFiniteEnvelope) :
    InstructionLine.inFiniteEnvelope bound
      (.pe (expressions.map ParsedExpr.normalize)) := by
  change (expressions.map ParsedExpr.normalize).length ≤ 10 ∧
    ∀ expression ∈ expressions.map ParsedExpr.normalize,
      expression.inFiniteEnvelope
  constructor
  · simpa using projectLine_expression_count_le_ten expressions issueLegal
  · intro normalized member
    rcases List.mem_map.mp member with ⟨expression, sourceMember, normalizedEq⟩
    subst normalized
    exact ParsedExpr.normalize_inFiniteEnvelope expression
      (payload expression sourceMember)

end ProofsLean.MNCore.Issue
