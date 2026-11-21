import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped BigOperators

namespace Specs.P205.Probability

universe u v

/-- Theorem 5.6: both tails of a finite independent bounded family, including
    the almost surely constant case and the empty family. -/
def HoeffdingStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ι : Type v) [Fintype ι] (X : ι → Ω → ℝ) (a b : ι → ℝ),
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, a i ≤ b i) →
    (∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i)) →
    let S : Ω → ℝ := fun ω ↦ ∑ i, (X i ω - ∫ ω, X i ω ∂μ)
    let V : ℝ := ∑ i, (b i - a i) ^ 2
    (∀ t : ℝ, 0 < t → 0 < V →
      μ.real {ω | t ≤ S ω} ≤ Real.exp (-2 * t ^ 2 / V) ∧
      μ.real {ω | S ω ≤ -t} ≤ Real.exp (-2 * t ^ 2 / V)) ∧
    (V = 0 → (∀ᵐ ω ∂μ, S ω = 0) ∧
      ∀ t : ℝ, 0 < t →
        μ.real {ω | t ≤ S ω} = 0 ∧ μ.real {ω | S ω ≤ -t} = 0)

end Specs.P205.Probability
