import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteIngredients.SeparableSplittingField

/-!
# The root field of a separable polynomial

FT-F01B: the splitting-field assertion of Proposition F01 in the field-theory
volume. No finiteness, normality, or algebraicity is required of the ambient
extension. Only the polynomial is assumed separable and split there.
-/

universe u v

namespace AdvancedFieldTheory

/-- In any splitting extension, adjoining all roots of a separable polynomial
produces a finite Galois extension of the base. -/
theorem separable_rootField_finite_galois
    (K : Type u) (T : Type v) [Field K] [Field T] [Algebra K T]
    (f : Polynomial K) (hf : f.Separable)
    (hsplit : (f.map (algebraMap K T)).Splits) :
    let E := generatedField (K := K) (f.rootSet T)
    FiniteDimensional K E ∧ Normal K E ∧ Algebra.IsSeparable K E ∧ IsGalois K E := by
  let E := IntermediateField.adjoin K (f.rootSet T)
  let : f.IsSplittingField K E :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfinite : FiniteDimensional K E :=
    Polynomial.IsSplittingField.finiteDimensional E f
  have hgalois : IsGalois K E := IsGalois.of_separable_splitting_field hf
  exact ⟨hfinite, hgalois.to_normal, hgalois.to_isSeparable, hgalois⟩

/-- Degree-zero polynomials contribute no generators, so their root field
is the literal intermediate base field. No separability assumption is needed. -/
theorem rootField_eq_bot_of_natDegree_eq_zero
    (K : Type u) (T : Type v) [Field K] [Field T] [Algebra K T]
    (f : Polynomial K) (hf : f.natDegree = 0) :
    generatedField (K := K) (f.rootSet T) = ⊥ := by
  change IntermediateField.adjoin K (f.rootSet T) = ⊥
  rw [Polynomial.eq_C_of_natDegree_eq_zero hf, Polynomial.rootSet_C,
    IntermediateField.adjoin_empty]

end AdvancedFieldTheory
