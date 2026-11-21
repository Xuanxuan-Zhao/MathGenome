import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CanonicalPathLaw

/-! Fixed deterministic time in paper.tex §2.3 (p207:W07).
The future includes the state at time `n` and uses the product sigma algebra.
The supplied filtration is arbitrary subject to the original one-step law. -/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

universe u v
namespace P207.Markov.FixedFutureLawSpec

noncomputable section

/-- On the countable discrete state space the canonical expectation is measurable. -/
def measurable_stateExpectation : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (g : (ℕ → S) → ℝ),
    Measurable (fun i => stateExpectation P i g)

/-- The same uniform bound as for the path function holds for its expectations. -/
def stateExpectation_bound : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (g : (ℕ → S) → ℝ)
    (C : ℝ), (∀ x, ‖g x‖ ≤ C) → ∀ i, ‖stateExpectation P i g‖ ≤ C

/-- The full bounded measurable future identity, tested against every event of `ℱ n`. -/
def fixed_future_integral : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ →
    ∀ (g : (ℕ → S) → ℝ), Measurable g → (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) →
    ∀ (n : ℕ) (A : Set Ω), MeasurableSet[ℱ n] A →
      (∫ ω in A, g (fun k => X (n + k) ω) ∂μ) =
        ∫ ω in A, stateExpectation P (X n ω) g ∂μ

end
end P207.Markov.FixedFutureLawSpec
