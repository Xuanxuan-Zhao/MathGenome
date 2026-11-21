import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.ExponentialMoments

open MeasureTheory ProbabilityTheory

namespace Specs.P205.Probability

/-- The reusable moment stage of paper.tex, W26. Bernoulli variables are real
measurable functions taking values 0 or 1 almost surely. The given parameters
are their actual success probabilities. Arbitrary finite index types include
the empty family, and the exponential parameter can have either sign. -/
def BernoulliMGF : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) → iIndepFun X ν →
    ∀ lam : ℝ,
      Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) ν ∧
      mgf (fun ω => ∑ i, X i ω) ν lam = ∏ i, (1 + p i * (Real.exp lam - 1)) ∧
      (∏ i, (1 + p i * (Real.exp lam - 1))) ≤
        Real.exp ((∑ i, p i) * (Real.exp lam - 1))

/-- The zero-mean case; independence is unnecessary for this conclusion. -/
def BernoulliSumZero : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (X : ι → Ω → ℝ) (p : ι → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∀ᵐ ω ∂ν, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, p i = ν.real {ω | X i ω = 1}) →
    (∑ i, p i) = 0 → ∀ᵐ ω ∂ν, (∑ i, X i ω) = 0

end Specs.P205.Probability
