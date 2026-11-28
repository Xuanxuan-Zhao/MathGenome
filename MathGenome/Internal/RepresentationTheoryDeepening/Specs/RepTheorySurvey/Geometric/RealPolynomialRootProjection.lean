import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.Module

namespace RepTheorySurvey.Geometric.RealPolynomialRootProjectionSpecs

universe u

/-- A finite family of coefficient polynomials detects the number of distinct complex roots of
each specialization of a real polynomial family with a nonzero constant leading coefficient. -/
def RealPolynomialRootProjection : Prop :=
  ∀ (σ : Type u) [Finite σ] (F : Polynomial (MvPolynomial σ ℝ)),
    (∃ c : ℝ, c ≠ 0 ∧ F.leadingCoeff = MvPolynomial.C c) →
    ∃ Q : Finset (MvPolynomial σ ℝ), ∀ x y : σ → ℝ,
      (∀ q ∈ Q, MvPolynomial.eval x q = 0 ↔ MvPolynomial.eval y q = 0) →
        ((F.map (MvPolynomial.eval x)).rootSet ℂ).ncard =
          ((F.map (MvPolynomial.eval y)).rootSet ℂ).ncard

end RepTheorySurvey.Geometric.RealPolynomialRootProjectionSpecs
