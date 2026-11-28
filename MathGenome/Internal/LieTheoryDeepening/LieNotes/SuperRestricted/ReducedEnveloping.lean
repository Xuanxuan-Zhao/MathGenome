import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping

/-! The p-center, reduced enveloping algebras, and the zero-character identification. -/

namespace LieNotes.SuperRestricted.ReducedEnveloping

open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Shared.Lie (U)

universe u v

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {G : Type v} [LieRing G] [LieAlgebra k G]

abbrev pCenterElement := @pCenterElementValue
abbrev pCenter := @pCenterValue
abbrev reducedRelations := @reducedRelationsValue
abbrev ReducedEnvelopingAlgebra := @reducedEnvelopingValue
abbrev quotientMap := @quotientMapValue

/-- The canonical quotient map is surjective and imposes exactly the reduced ideal. -/
theorem quotientMap_spec (power : restrictedPowerValue k p G) (χ : G →ₗ[k] k) :
    Function.Surjective (quotientMap power χ) ∧
    (∀ a, quotientMap power χ a = 0 ↔ a ∈ reducedRelations power χ) ∧
    (∀ x : G, quotientMap power χ (pCenterElement power x) =
      algebraMap k (ReducedEnvelopingAlgebra power χ) (χ x ^ p)) := by
  refine ⟨Ideal.Quotient.mkₐ_surjective k _, fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_⟩
  intro x
  have h : quotientMap power χ (pCenterElement power x - algebraMap k (U k G) (χ x ^ p)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.subset_span ⟨x, rfl⟩)
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h
  exact h

/-- The reduced enveloping algebra at the zero character is the restricted enveloping algebra. -/
abbrev zeroCharacterEquiv := @zeroCharacterEquivValue

/-- The zero-character identification carries every ordinary enveloping class to the same class. -/
@[simp] theorem zeroCharacterEquiv_quotientMap (power : restrictedPowerValue k p G) (a : U k G) :
    zeroCharacterEquiv power (quotientMap power 0 a) =
      _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary.quotientMapValue
        k p power a := by
  exact Ideal.quotientEquivAlgOfEq_mk k _ a

end LieNotes.SuperRestricted.ReducedEnveloping
