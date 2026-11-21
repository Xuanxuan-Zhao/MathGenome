import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.LaplacePeano
import Mathlib.Analysis.Real.Sqrt

open Set

namespace Specs.D03Supporting

/-- Uniform control of the rescaled phase on every fixed compact interval. -/
def LaplaceUniformPhase : Prop :=
  ∀ (a b x₀ : ℝ) (φ : ℝ → ℝ),
    a < b → a < x₀ → x₀ < b →
    ContDiffOn ℝ 2 φ (Icc a b) →
    (∀ x ∈ Icc a b, φ x₀ ≤ φ x) →
    (∀ x ∈ Icc a b, φ x = φ x₀ → x = x₀) →
    0 < deriv (deriv φ) x₀ →
    ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, L ≤ lam →
        ∀ y : ℝ, |y| ≤ R →
          x₀ + y / Real.sqrt lam ∈ Icc a b ∧
          |lam * (φ (x₀ + y / Real.sqrt lam) - φ x₀) -
            deriv (deriv φ) x₀ * y ^ 2 / 2| < η

end Specs.D03Supporting
