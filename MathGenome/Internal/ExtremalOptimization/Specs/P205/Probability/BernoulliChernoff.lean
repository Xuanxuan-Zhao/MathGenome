import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.BernoulliMGF
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

namespace Specs.P205.Probability

/-! Theorem W26 in paper.tex. The family is finite, including the empty family.
The Bernoulli property is almost sure and p records the actual success laws.
All powers below are real powers; the stated parameter ranges make their bases positive. -/

/-- Inclusive multiplicative upper tail, including δ = 0. -/
def BernoulliChernoffUpper : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) → iIndepFun X ν →
    ∀ δ : ℝ, 0 ≤ δ →
      ν.real {ω | (1 + δ) * (∑ i, p i) ≤ ∑ i, X i ω} ≤
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∑ i, p i)

/-- Inclusive multiplicative lower tail for 0 ≤ δ < 1. -/
def BernoulliChernoffLower : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) → iIndepFun X ν →
    ∀ δ : ℝ, 0 ≤ δ → δ < 1 →
      ν.real {ω | (∑ i, X i ω) ≤ (1 - δ) * (∑ i, p i)} ≤
        (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (∑ i, p i)

/-- The endpoint δ = 1 of the lower tail. -/
def BernoulliChernoffAtOne : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) → iIndepFun X ν →
    ν.real {ω | (∑ i, X i ω) = 0} ≤ Real.exp (-(∑ i, p i))

/-- At zero mean the sum vanishes a.e. and all asserted right sides are one.
Independence is not needed for this degeneracy. -/
def BernoulliChernoffZeroMean : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) →
    (∑ i, p i) = 0 →
      (∀ᵐ ω ∂ν, (∑ i, X i ω) = 0) ∧
      Real.exp (-(∑ i, p i)) = 1 ∧
      ∀ δ : ℝ, 0 ≤ δ →
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∑ i, p i) = 1 ∧
        (δ < 1 → (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (∑ i, p i) = 1)

end Specs.P205.Probability
