import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import Mathlib.Analysis.Analytic.Uniqueness

/-! Independent specification of paper.tex:739–767, cor:pde-harmonic-analytic.
Analyticity is over ℝ, also for complex-valued functions. The harmonicity
predicate is the shared C² / coordinate-Laplacian definition. -/
noncomputable section
open Set

namespace P201Specs.AnalyticContinuation

/-- Interior real analyticity, including dimension one, with no boundary assumptions. -/
def AnalyticityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜), MeanValues.IsHarmonic Ω u →
      AnalyticOnNhd ℝ u (Ω : Set (Space n))

/-- Agreement on any nonempty open subset propagates over a connected open domain. -/
def ContinuationStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u v : Space n → 𝕜),
    IsConnected (Ω : Set (Space n)) → MeanValues.IsHarmonic Ω u → MeanValues.IsHarmonic Ω v →
    ∀ V : Set (Space n), IsOpen V → V.Nonempty → V ⊆ (Ω : Set (Space n)) → EqOn u v V →
      EqOn u v (Ω : Set (Space n))

end P201Specs.AnalyticContinuation
