import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ExcursionMeasure
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Stationarity

/-! The complete conclusions of paper.tex, §3.2, p207:W14.
The mean and occupation are extended nonnegative expectations under the
canonical law, so infinite return times are retained. Class properties are
stated for communicating states of an arbitrary countable chain. -/

open scoped ENNReal
universe u
namespace P207.Markov.StationaryReturnTimesSpec

noncomputable section

def stationary_probability_iff_positiveRecurrent : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S), Irreducible P →
    ((∃ π : ProbabilityLaw S, IsStationary P π) ↔ ∃ i, PositiveRecurrent P i)

def stationary_positiveRecurrent : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsStationary P π → ∀ i, PositiveRecurrent P i

def stationary_meanReturnTime : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsStationary P π → ∀ i, π i = 1 / meanReturnTime P i

def stationary_excursionMass : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S),
    Irreducible P → IsStationary P π → ∀ i j, excursionMass P i j = π j / π i

def stationary_probability_unique : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π ρ : ProbabilityLaw S),
    Irreducible P → IsStationary P π → IsStationary P ρ → π = ρ

def positiveRecurrent_iff_of_communicate : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) {i j : S},
    Communicate P i j → (PositiveRecurrent P i ↔ PositiveRecurrent P j)

def nullRecurrent_iff_of_communicate : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) {i j : S},
    Communicate P i j → (NullRecurrent P i ↔ NullRecurrent P j)

end
end P207.Markov.StationaryReturnTimesSpec
