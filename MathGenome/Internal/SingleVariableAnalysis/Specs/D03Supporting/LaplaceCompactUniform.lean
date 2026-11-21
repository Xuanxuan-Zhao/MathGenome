import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.LaplaceUniformPhase
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential

open Set

namespace Specs.D03Supporting

/-- Compact-uniform Laplace rescaling for real or complex continuous amplitudes.
The `RCLike` quantifier includes the canonical fields ℝ and ℂ. -/
def LaplaceCompactUniform : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (a b x₀ : ℝ) (φ : ℝ → ℝ) (g : ℝ → 𝕂),
    a < b → a < x₀ → x₀ < b →
    ContDiffOn ℝ 2 φ (Icc a b) →
    (∀ x ∈ Icc a b, φ x₀ ≤ φ x) →
    (∀ x ∈ Icc a b, φ x = φ x₀ → x = x₀) →
    0 < deriv (deriv φ) x₀ → ContinuousOn g (Icc a b) →
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, L ≤ lam →
        ∀ y : ℝ, |y| ≤ R →
          x₀ + y / Real.sqrt lam ∈ Icc a b ∧
          ‖Real.exp (-lam * (φ (x₀ + y / Real.sqrt lam) - φ x₀)) •
              g (x₀ + y / Real.sqrt lam) -
            Real.exp (-deriv (deriv φ) x₀ * y ^ 2 / 2) • g x₀‖ < ε

end Specs.D03Supporting
