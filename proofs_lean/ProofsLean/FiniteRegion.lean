import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import ProofsLean.Issue

namespace ProofsLean.MNCore.Issue

private abbrev RegionCode :=
  Fin 5 × Fin 32768 × Fin 32768 × Fin 32768 × Fin 32768 × Bool × Option (Fin 4)

private def boundedMadpe (m : Option Nat) (h : ∀ n, m = some n → n < 4) :
    Option (Fin 4) :=
  match m with
  | none => none
  | some n => some ⟨n, h n rfl⟩

private def regionCode (r : Region) (h : r.inFiniteEnvelope) : RegionCode := by
  rcases h with ⟨hw, h0, h1, h2, h3, hm⟩
  exact Prod.mk ⟨r.width, hw⟩
    (Prod.mk ⟨r.address0, h0⟩
      (Prod.mk ⟨r.address1, h1⟩
        (Prod.mk ⟨r.address2, h2⟩
          (Prod.mk ⟨r.address3, h3⟩
            (Prod.mk r.tIndirect (boundedMadpe r.madpe hm))))))

private theorem regionCode_injective :
    Function.Injective (fun r : {r : Region // r.inFiniteEnvelope} => regionCode r.1 r.2) := by
  intro a b equal
  rcases a with ⟨ra, ha⟩
  rcases b with ⟨rb, hb⟩
  apply Subtype.ext
  cases ra with
  | mk wa a0 a1 a2 a3 ati am =>
    cases rb with
    | mk wb b0 b1 b2 b3 bti bm =>
      simp only [regionCode, Prod.mk.injEq] at equal
      rcases equal with ⟨hw, h0, h1, h2, h3, ht, hm⟩
      have hw' : wa = wb := congrArg Fin.val hw
      have h0' : a0 = b0 := congrArg Fin.val h0
      have h1' : a1 = b1 := congrArg Fin.val h1
      have h2' : a2 = b2 := congrArg Fin.val h2
      have h3' : a3 = b3 := congrArg Fin.val h3
      have hm' : am = bm := by
        cases am <;> cases bm <;> simp_all [boundedMadpe]
      cases hw'
      cases h0'
      cases h1'
      cases h2'
      cases h3'
      cases ht
      cases hm'
      rfl

/-- Finite carrier for regions whose width, four cycle addresses, and madpe
fall within the intentionally generous PE address envelope. This says nothing
about bank-specific legality, alignment, or line-level boundedness. -/
theorem Region.inFiniteEnvelope_finite :
    Finite {r : Region // r.inFiniteEnvelope} :=
  Finite.of_injective (fun r => regionCode r.1 r.2) regionCode_injective

end ProofsLean.MNCore.Issue
