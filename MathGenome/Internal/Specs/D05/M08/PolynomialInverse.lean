import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M03.Isomorphism

/-!
Independent statements for K05.08.polynomial_inverse, paper.tex:1200–1206.
The minimal polynomial and evaluation are the canonical prerequisite objects.
Invertibility is the existence of a unit in the endomorphism algebra; the first
bridge identifies this with bijectivity of the linear map. No characteristic,
splitting, or positive-dimension assumption is imposed.
-/

noncomputable section

namespace Specs.D05.M08.PolynomialInverse

/-- Units are exactly the bijective linear endomorphisms. -/
def invertible_iff_bijective : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V), IsUnit T ↔ Function.Bijective T

/-- The criterion includes the zero space, whose minimal polynomial is 1. -/
def invertible_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    IsUnit T ↔ (Minpoly.minimalPolynomial_value K V T).eval 0 ≠ 0

/-- The inverse is realized by a polynomial, with both composition identities. -/
def polynomial_inverse : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V), IsUnit T →
    ∃ p : Polynomial K,
      Evaluation.evaluation_value K V T p * T = 1 ∧
      T * Evaluation.evaluation_value K V T p = 1

/-- In the canonical linear-equivalence representation, that polynomial value
is the actual inverse linear map. -/
def inverse_eq_polynomial : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V ≃ₗ[K] V),
    ∃ p : Polynomial K,
      Evaluation.evaluation_value K V T.toLinearMap p = T.symm.toLinearMap

/-- Explicitly record the zero-dimensional convention and self-inverse map. -/
def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 →
      Minpoly.minimalPolynomial_value K V T = 1 ∧
      (Minpoly.minimalPolynomial_value K V T).eval 0 ≠ 0 ∧
      T = 0 ∧ T * T = 1 ∧ IsUnit T

end Specs.D05.M08.PolynomialInverse
