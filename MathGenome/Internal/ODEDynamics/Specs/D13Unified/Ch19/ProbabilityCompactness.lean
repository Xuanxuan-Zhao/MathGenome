import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
The statement of `paper.tex`, Lemma `d13:19:probability-compactness`.
The measurable structure is exactly the Borel sigma algebra. The subsequence
and the limiting probability are chosen before quantifying over test functions.
-/

open Filter MeasureTheory Topology

namespace Specs.D13Unified.Ch19

/-- Every sequence of Borel probabilities on a nonempty compact metric space
has one subsequence whose integrals converge for all continuous real functions. -/
def ProbabilityCompactness : Prop :=
  ∀ (K : Type*) [MetricSpace K] [CompactSpace K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (ν : ℕ → ProbabilityMeasure K),
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ μ : ProbabilityMeasure K,
      ∀ g : K → ℝ, Continuous g →
        Tendsto (fun k => ∫ x, g x ∂(ν (n k) : Measure K)) atTop
          (𝓝 (∫ x, g x ∂(μ : Measure K)))

end Specs.D13Unified.Ch19
