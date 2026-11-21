import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.LagrangeSolution

/-! Independent coefficient formula in paper.tex, Theorem p204:W18.
The reciprocal of the positive integer is mapped from ℚ into the coefficient
ring. The series H is arbitrary; F is any zero-constant solution. -/
noncomputable section
universe u
namespace Specs.FiniteCombinatorics.Series.LagrangeInversion
open Specs.FiniteCombinatorics.Series.Substitution

def CoefficientFormula : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ H F : PowerSeries R),
    IsUnit (PowerSeries.constantCoeff φ) →
    PowerSeries.constantCoeff F = 0 →
    F = PowerSeries.X * composeValue φ F →
    ∀ n : ℕ, 1 ≤ n →
      PowerSeries.coeff n (composeValue H F) =
        algebraMap ℚ R ((n : ℚ)⁻¹) *
          PowerSeries.coeff (n-1) (PowerSeries.derivative H * φ^n)

def CanonicalCoefficientFormula : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ H : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff φ = (a₀ : R) → ∀ n : ℕ, 1 ≤ n →
      PowerSeries.coeff n (composeValue H
        (Specs.FiniteCombinatorics.Series.LagrangeSolution.solutionValue φ a₀)) =
        algebraMap ℚ R ((n : ℚ)⁻¹) *
          PowerSeries.coeff (n-1) (PowerSeries.derivative H * φ^n)

end Specs.FiniteCombinatorics.Series.LagrangeInversion
