import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteIngredients.Restriction

/-!
# Finite Galois restriction

For finite Galois E/K and a Galois intermediate field M/K, restriction
is a surjective group homomorphism with kernel the pointwise stabilizer
of M. The latter is the image of the injective scalar-forgetting map
from Gal(E/M), compatibly with the foundational fixingSubgroupEquiv.

Source: FT-F01, notes/003/advanced-field-theory.tex:149–151.
-/

universe u v

noncomputable section

namespace AdvancedFieldTheory

/-- Restriction to a Galois intermediate field, as a group homomorphism. -/
def finiteRestriction {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M] :
    (E ≃ₐ[K] E) →* (M ≃ₐ[K] M) :=
  AlgEquiv.restrictNormalHom M

/-- Restriction has the same action on each element of M. -/
theorem finiteRestriction_apply {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M]
    (σ : E ≃ₐ[K] E) (x : M) :
    ((finiteRestriction M σ x : M) : E) = σ (x : E) :=
  AlgEquiv.restrictNormalHom_apply M σ x

/-- Every K-automorphism of M extends to E; no choice of a section is asserted. -/
theorem finiteRestriction_surjective {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M] :
    Function.Surjective (finiteRestriction M) :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) E

/-- The kernel is precisely the pointwise stabilizer used in the source. -/
theorem finiteRestriction_ker {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M] :
    (finiteRestriction M).ker = fixingSubgroup M :=
  IntermediateField.restrictNormalHom_ker M

/-- The intrinsic automorphism group embeds by forgetting M-linearity. -/
theorem finiteRestriction_intrinsic_injective {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M] :
    Function.Injective (AlgEquiv.restrictScalarsHom K : (E ≃ₐ[M] E) →* (E ≃ₐ[K] E)) :=
  AlgEquiv.restrictScalarsHom_injective K

/-- Exactness expressed using the actual inclusion of Gal(E/M) into Gal(E/K). -/
theorem finiteRestriction_ker_eq_range {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M] :
    (finiteRestriction M).ker =
      (AlgEquiv.restrictScalarsHom K : (E ≃ₐ[M] E) →* (E ≃ₐ[K] E)).range := by
  rw [finiteRestriction_ker]
  ext σ
  constructor
  · intro hσ
    exact ⟨M.fixingSubgroupEquiv ⟨σ, hσ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact (M.fixingSubgroupEquiv.symm τ).property

end AdvancedFieldTheory
