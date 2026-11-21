import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statements for FT-C01, Proposition C01 of
notes/003/advanced-field-theory.tex:652–669.
The base field is its specified image in the ambient field. No finiteness
hypothesis is imposed on the ambient Galois extension. The pointwise equation
on every element of E expresses that the ambient automorphism restricts to τ.
-/

universe u v

namespace Specs.AdvancedFieldTheory

/-- Every element outside the base field is moved on a finite Galois stage,
by an automorphism that extends to the ambient extension. -/
def exists_finite_galois_moving_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (x : L), x ∉ (⊥ : IntermediateField K L) →
    ∃ E : IntermediateField K L,
      FiniteDimensional K E ∧ IsGalois K E ∧
      ∃ hx : x ∈ E, ∃ τ : E ≃ₐ[K] E, ∃ g : L ≃ₐ[K] L,
        τ ⟨x, hx⟩ ≠ ⟨x, hx⟩ ∧
        (∀ y : E, (τ y : L) = g (y : L)) ∧ g x ≠ x

/-- The fixed field of the full group is precisely the base field. -/
def full_fixedField_eq_bot_type : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [IsGalois K L],
    IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) =
      (⊥ : IntermediateField K L)

end Specs.AdvancedFieldTheory
