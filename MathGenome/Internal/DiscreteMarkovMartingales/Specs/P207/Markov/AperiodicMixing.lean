import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StationaryReturnTimes
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation

/-! The full convergence theorem of paper.tex, §3.4 (W16).
The stationary-law versions are slightly stronger: existence of that law
implies positive recurrence by W14. The final statement obtains the law from
positive recurrence, rather than requiring its existence as an extra assumption.
There are no support or moment restrictions on the initial law. -/

open Filter
open scoped Topology
universe u
namespace P207.Markov.AperiodicMixingSpec

def aperiodic_tendsto_totalVariation : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → (∀ i, Aperiodic P i) → IsStationary P π →
    ∀ i, Tendsto (fun n => totalVariation (power P n i) π) atTop (𝓝 0)

def aperiodic_tendsto_totalVariation_evolve : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → (∀ i, Aperiodic P i) → IsStationary P π →
    ∀ ν : ProbabilityLaw S,
      Tendsto (fun n => totalVariation (evolve ν P n) π) atTop (𝓝 0)

def exists_unique_stationary_mixing : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S),
    Irreducible P → (∃ i, PositiveRecurrent P i) → (∀ i, Aperiodic P i) →
    ∃ π : ProbabilityLaw S, IsStationary P π ∧
      (∀ ρ : ProbabilityLaw S, IsStationary P ρ → ρ = π) ∧
      (∀ i, Tendsto (fun n => totalVariation (power P n i) π) atTop (𝓝 0)) ∧
      (∀ ν : ProbabilityLaw S,
        Tendsto (fun n => totalVariation (evolve ν P n) π) atTop (𝓝 0))

end P207.Markov.AperiodicMixingSpec
