import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallPoisson

/-! Independent types for the bounds in paper.tex, Corollary
`cor:pde-harmonic-harnack` (900–932), with the dimension-one convention
at 945. Monotone convergence is assigned to HarnackConvergence.
The compact comparison constants are chosen before the harmonic function. -/
noncomputable section
open Set Metric

namespace P201Specs.Harnack

/-- The sharp concentric-ball bounds, including n = 1. Connectedness of
an ambient domain is unnecessary for this local assertion. -/
def BallBoundsStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ),
    MeanValues.IsHarmonic Ω u → (∀ y ∈ Ω, 0 ≤ u y) →
    ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    ∀ (ρ : ℝ), 0 ≤ ρ → ρ < 1 → ∀ (x : Space n), ‖x - a‖ ≤ ρ * r →
      ((1 - ρ) / (1 + ρ) ^ (n - 1)) * u a ≤ u x ∧
      u x ≤ ((1 + ρ) / (1 - ρ) ^ (n - 1)) * u a

/-- Two positive constants depending only on the domain, compact set,
and reference point, uniformly for all nonnegative real harmonic functions. -/
def CompactBoundsStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n), IsConnected (Ω : Set (Space n)) →
    ∀ (K : Set (Space n)), IsCompact K → K ⊆ (Ω : Set _) →
    ∀ (a₀ : Space n), a₀ ∈ Ω →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (u : Space n → ℝ), MeanValues.IsHarmonic Ω u → (∀ y ∈ Ω, 0 ≤ u y) →
        ∀ x ∈ K, c * u a₀ ≤ u x ∧ u x ≤ C * u a₀

end P201Specs.Harnack
