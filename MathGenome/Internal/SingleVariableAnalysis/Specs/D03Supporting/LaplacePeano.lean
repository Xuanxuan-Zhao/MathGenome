import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open Filter Set
open scoped Topology

namespace Specs.D03Supporting

/-- The local second-order expansion of the phase at its interior minimum.
All regularity is relative to the closed interval. -/
def LaplacePeano : Prop :=
  ∀ (a b x₀ : ℝ) (φ : ℝ → ℝ),
    a < b → a < x₀ → x₀ < b →
    ContDiffOn ℝ 2 φ (Icc a b) →
    (∀ x ∈ Icc a b, φ x₀ ≤ φ x) →
    (∀ x ∈ Icc a b, φ x = φ x₀ → x = x₀) →
    0 < deriv (deriv φ) x₀ →
    deriv φ x₀ = 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ → ℝ,
        ρ 0 = 0 ∧ Tendsto ρ (𝓝 0) (𝓝 0) ∧
        ∀ h : ℝ, |h| < δ →
          x₀ + h ∈ Icc a b ∧
          φ (x₀ + h) - φ x₀ =
            deriv (deriv φ) x₀ * h ^ 2 / 2 + h ^ 2 * ρ h

end Specs.D03Supporting
