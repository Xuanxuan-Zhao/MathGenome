import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.MeanHittingTime

/-! The finite irreducible conclusion of paper.tex, p207:W12.
Entrance includes time zero; positive return starts at time one.
Both means are extended nonnegative expectations, with no prior finiteness assumption. -/

open scoped ENNReal
universe u
namespace P207.Markov.FinitePositiveRecurrenceSpec

def meanHittingTime_lt_top : Prop :=
  ∀ {S : Type u} [Finite S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S),
    Irreducible P → ∀ i j, meanHittingTime P {j} i < ⊤

def meanReturnTime_lt_top : Prop :=
  ∀ {S : Type u} [Finite S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S),
    Irreducible P → ∀ j, meanReturnTime P j < ⊤

def positiveRecurrent : Prop :=
  ∀ {S : Type u} [Finite S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S),
    Irreducible P → ∀ j, PositiveRecurrent P j

end P207.Markov.FinitePositiveRecurrenceSpec
