import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Interfaces

open MeasureTheory
open scoped ENNReal MeasureTheory

universe u v

namespace P207.Markov.DeterministicTransitionsSpec

/-- Deterministic transition probabilities for every event, at all times including zero. -/
def transition_probabilities : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [mΩ : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ → ∀ m n : ℕ, ∀ A : Set S,
    μ[(fun ω => Set.indicator {ω | X (n + m) ω ∈ A}
      (fun _ => (1 : ℝ)) ω) | ℱ n] =ᵐ[μ]
      fun ω => (event (power P m) (X n ω) A).toReal

/-- The full marginal probability measure, rather than only its singleton masses. -/
def marginal_law : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [mΩ : MeasurableSpace Ω]
    (P : StochasticMatrix S) (ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P ν X ℱ μ → ∀ n : ℕ,
    μ.map (X n) = (evolve ν P n).toMeasure

end P207.Markov.DeterministicTransitionsSpec
