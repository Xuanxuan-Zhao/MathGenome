import MathGenome.Internal.Specs.D07.Ch14.RestrictionExactness
import MathGenome.Internal.D07.Ch14.NormalQuotientRestrictionSurjectivity

/-!
The restriction exact sequence (K07.14.restriction_exactness).

Forgetting E-linearity retains the same field automorphism, hence is injective.
Its image consists precisely of the automorphisms fixing the image of E:
such an automorphism can be bundled as an E-algebra automorphism without
changing its field map. The upstream kernel and extension theorems then give
exactness in the middle and surjectivity at the right endpoint.
-/

universe u v w

namespace D07.Ch14.RestrictionExactness

open Specs.D07.Ch14.RestrictionExactness

/-- Include E-automorphisms as K-automorphisms, preserving their field maps. -/
def inclusionHom (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] :
    (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) :=
  AlgEquiv.restrictScalarsHom K

theorem inclusion_agrees : InclusionAgrees.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ σ x
  rfl

/-- An automorphism lies in this image exactly when it fixes E pointwise. -/
theorem inclusion_range (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] :
    (inclusionHom K E L).range =
      (IsScalarTower.toAlgHom K E L).fieldRange.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    exact τ.commutes y
  · intro hσ
    have hfix : ∀ y : E, σ (algebraMap E L y) = algebraMap E L y := by
      intro y
      exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _ ⟨y, rfl⟩
    let τ : L ≃ₐ[E] L := { σ.toRingEquiv with commutes' := hfix }
    exact ⟨τ, AlgEquiv.ext (fun _ => rfl)⟩

theorem restriction_exact_sequence : RestrictionExactSequence.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ _ _
  refine ⟨AlgEquiv.restrictScalarsHom_injective K, ?_,
    NormalQuotientRestrictionSurjectivity.restriction_surjective K E L⟩
  exact (inclusion_range K E L).trans
    (NormalQuotientRestrictionSurjectivity.restriction_kernel K E L).symm

end D07.Ch14.RestrictionExactness
