import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory Set

namespace Specs.ProbabilityFoundations.Ch09.BerryEsseenTheorem

universe u

/-- Berry–Esseen, paper.tex:3313–3356. Indices start at zero, so `range n`
represents the first n summands. Equality of pushforward measures expresses
identical distribution on the original, possibly incomplete, probability space.
The mean is the actual integral. The positive parameter σ and the centered
second-moment identity specify the positive square root of the variance.
The constant is quantified before all laws and sample sizes. -/
def BerryEsseen : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → ℝ),
      (∀ k, Measurable (X k)) → iIndepFun X P →
      (∀ k, P.map (X k) = P.map (X 0)) →
      ∀ m σ : ℝ, 0 < σ →
      (∫ ω, X 0 ω ∂P) = m →
      (∫ ω, (X 0 ω - m) ^ 2 ∂P) = σ ^ 2 →
      Integrable (fun ω => |X 0 ω - m| ^ 3) P →
      ∀ n : ℕ, 1 ≤ n →
        (⨆ x : ℝ,
          |(P {ω | (∑ k ∈ Finset.range n, (X k ω - m)) /
              (σ * Real.sqrt (n : ℝ)) ≤ x}).toReal -
            ((gaussianReal 0 1) (Iic x)).toReal|) ≤
          (C / Real.sqrt (n : ℝ)) * (∫ ω, |X 0 ω - m| ^ 3 ∂P) / σ ^ 3

end Specs.ProbabilityFoundations.Ch09.BerryEsseenTheorem
