import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues

/-! Independent statements of paper.tex, Proposition `prop:pde-harmonic-derivatives`.
The neighborhood is represented by an arbitrary open domain containing the closed ball.
Multi-indices and all derivatives use the canonical spatial interface.
-/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff
namespace P201Specs.DerivativesLiouville

/-- The constant is uniform in the function, center, radius, domain, and scalar field.
For real-valued functions the norm is the absolute value in the manuscript. -/
def InteriorDerivativeEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : MultiIndex n, ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜),
      MeanValues.IsHarmonic Ω u → ∀ (a : Space n) (r : ℝ),
      0 < r → closedBall a r ⊆ (Ω : Set _) →
      ‖multiPartial u α a‖ ≤ C / r ^ (n + α.card) * ∫ y in ball a r, ‖u y‖

/-- Either one-sided bound suffices; no bound on the absolute value is assumed. -/
def LiouvilleStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ u : Space n → ℝ,
    MeanValues.IsHarmonic ⊤ u →
    ((∃ M : ℝ, ∀ x, u x ≤ M) ∨ (∃ m : ℝ, ∀ x, m ≤ u x)) →
    ∃ c : ℝ, ∀ x, u x = c

end P201Specs.DerivativesLiouville
