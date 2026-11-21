import Mathlib.Probability.Moments.Variance

/-!
Independent statements for the variance-method conclusions of paper.tex,
Theorem p205:W23. `MemLp X 2 μ` requires almost-everywhere measurability and
a finite second moment; on a probability space this also ensures integrability.
Probabilities are real values of the measures and variance is Mathlib's
canonical real variance. The sample spaces in the sequence may vary with `n`.
-/

open MeasureTheory Filter
open scoped Topology

universe u

namespace Specs.P205.Probability.VarianceMethod

/-- The probability of zero is at most the relative variance. -/
def ZeroProbabilityBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), MemLp X 2 μ → (∀ᵐ ω ∂μ, 0 ≤ X ω) →
    0 < (∫ ω, X ω ∂μ) →
    μ.real {ω | X ω = 0} ≤
      ProbabilityTheory.variance X μ / (∫ ω, X ω ∂μ) ^ 2

/-- Vanishing relative variance implies positive values with probability tending
to one, even when the underlying probability spaces vary. -/
def PositiveProbabilityTendstoOne : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → ℝ),
    (∀ n, MemLp (X n) 2 (μ n)) →
    (∀ n, ∀ᵐ ω ∂μ n, 0 ≤ X n ω) →
    (∀ n, 0 < (∫ ω, X n ω ∂μ n)) →
    Tendsto (fun n ↦ ProbabilityTheory.variance (X n) (μ n) /
      (∫ ω, X n ω ∂μ n) ^ 2) atTop (𝓝 0) →
    Tendsto (fun n ↦ (μ n).real {ω | 0 < X n ω}) atTop (𝓝 1)

end Specs.P205.Probability.VarianceMethod
