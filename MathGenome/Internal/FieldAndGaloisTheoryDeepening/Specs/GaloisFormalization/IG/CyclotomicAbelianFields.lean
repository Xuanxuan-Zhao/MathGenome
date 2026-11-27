import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsSepClosed

namespace Specs.GaloisFormalization.IG

universe u v

/-- The family of realizations used in the proof of IG16, in the given separable
closure of `ℚ`. For a trivial group every field in the family is the base field. -/
def PairwiseDisjointGaloisRealizations : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]
    (A : Type v) [CommGroup A] [Finite A] (s : ℕ),
    ∃ F : Fin s → IntermediateField ℚ Ω,
      (∀ j, FiniteDimensional ℚ (F j) ∧ IsGalois ℚ (F j) ∧
        Nonempty ((F j ≃ₐ[ℚ] F j) ≃* A)) ∧
      (∀ j h, j ≠ h → F j ⊓ F h = ⊥) ∧
      (Subsingleton A → ∀ j, F j = ⊥)

end Specs.GaloisFormalization.IG
