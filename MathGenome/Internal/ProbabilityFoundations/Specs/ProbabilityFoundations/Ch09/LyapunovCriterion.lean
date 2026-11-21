import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.IndependentRowObjects
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent statements of paper.tex:3186–3198 (Lyapunov's criterion).
The row data include centering, finite second moments and within-row
independence. Row lengths and probability spaces can vary arbitrarily. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace Specs.ProbabilityFoundations.Ch09.LyapunovCriterion
open _root_.ProbabilityFoundations.Ch09.IndependentRows
open Specs.ProbabilityFoundations.Ch09.IndependentRows

universe u

/-- The quantitative Lindeberg bound for normalized moments. -/
def LindebergBound : Prop :=
  ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (R : Row r Ω) (n : ℕ) (δ : ℝ), 0 < δ →
    (∀ j, Integrable (fun ω => |normalized R n j ω| ^ (2 + δ)) (R.μ n)) →
    ∀ ε : ℝ, 0 < ε →
      lindeberg R n ε ≤ ε ^ (-δ) *
        ∑ j, ∫ ω, |normalized R n j ω| ^ (2 + δ) ∂R.μ n

/-- The original, unnormalized Lyapunov condition with arbitrary real δ > 0.
Integrability of the nonnegative moment is finiteness of its expectation. -/
def CentralLimit : Prop :=
  ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (R : Row r Ω) (δ : ℝ), 0 < δ →
    (∀ n, 0 < varianceSum R n) →
    (∀ n j, Integrable (fun ω => |R.X n j ω| ^ (2 + δ)) (R.μ n)) →
    Tendsto (fun n => (∑ j, ∫ ω, |R.X n j ω| ^ (2 + δ) ∂R.μ n) /
      (scale R n) ^ (2 + δ)) atTop (𝓝 0) →
    TendstoInDistribution (sum R) atTop (id : ℝ → ℝ) R.μ (gaussianReal 0 1)

end Specs.ProbabilityFoundations.Ch09.LyapunovCriterion
