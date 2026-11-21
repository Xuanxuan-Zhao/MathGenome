import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.Gaussian
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus

noncomputable section
open MeasureTheory Polynomial Set
open scoped BigOperators

namespace NumAnalysis206.Quadrature.Specs

/-- W59's analytic remainder for the W58 Gaussian rule. The supremum is the
uniform norm of the supplied top derivative on the closed interval. No
regularity or measurability is required outside that interval. -/
def gaussianRemainder : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ), 1 ≤ n →
    FiniteMoment μ (2 * n) → (gramMatrix μ n).PosDef →
    ∀ (a b : ℝ), μ.support ⊆ Icc a b →
    ∀ (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ),
    NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b (2 * n) f D →
    ∀ π : ℝ[X], IsMonicOrthogonal μ n π →
    ∀ x : Fin n → ℝ, Function.Injective x → (∀ i, π.IsRoot (x i)) →
      (∃ ξ ∈ Icc a b,
        (∫ t : ℝ, f t ∂μ) - ∑ i, gaussianWeightValue μ x i * f (x i) =
          D (2 * n) ξ / ((2 * n).factorial : ℝ) *
            (∫ t : ℝ, (π.eval t)^2 ∂μ)) ∧
      |(∫ t : ℝ, f t ∂μ) - ∑ i, gaussianWeightValue μ x i * f (x i)| ≤
        sSup ((fun t => |D (2 * n) t|) '' Icc a b) / ((2 * n).factorial : ℝ) *
          (∫ t : ℝ, (π.eval t)^2 ∂μ)

end NumAnalysis206.Quadrature.Specs
