import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped MeasureTheory
universe u

namespace P207.AzumaHoeffdingSpec

/-- Finite-horizon version: the process is only required to be a martingale
through time `n`. Probabilities are real-valued probabilities. -/
def azuma_hoeffding : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (n : ℕ)
    (a b : ℕ → ℝ),
    (∀ k ≤ n, Measurable[ℱ k] (M k)) →
    (∀ k ≤ n, Integrable (M k) μ) →
    (∀ k < n, μ[M (k + 1) | ℱ k] =ᵐ[μ] M k) →
    (∀ k < n, ∀ᵐ ω ∂μ,
      a k ≤ M (k + 1) ω - M k ω ∧ M (k + 1) ω - M k ω ≤ b k) →
    let V := ∑ k ∈ Finset.range n, (b k - a k) ^ 2
    ∀ t : ℝ, 0 < t →
      (0 < V →
        μ.real {ω | t ≤ M n ω - M 0 ω} ≤ Real.exp (-2 * t ^ 2 / V) ∧
        μ.real {ω | M n ω - M 0 ω ≤ -t} ≤ Real.exp (-2 * t ^ 2 / V) ∧
        μ.real {ω | t ≤ |M n ω - M 0 ω|} ≤ 2 * Real.exp (-2 * t ^ 2 / V)) ∧
      (V = 0 →
        μ.real {ω | t ≤ M n ω - M 0 ω} = 0 ∧
        μ.real {ω | M n ω - M 0 ω ≤ -t} = 0)

end P207.AzumaHoeffdingSpec
