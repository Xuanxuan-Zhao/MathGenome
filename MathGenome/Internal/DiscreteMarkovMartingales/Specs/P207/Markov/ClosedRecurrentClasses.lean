import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClassRecurrence

/-! The closedness and first-hit assertions of paper.tex, p207:W12.
The class may be proper, and recurrence need not be positive recurrence.
The shared first entrance `hittingTime` includes time zero. -/
universe u
namespace P207.Markov.ClosedRecurrentClassesSpec

def recurrent_class_isClosed : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (C : Set S),
    IsCommunicatingClass P C → (∃ r ∈ C, Recurrent P r) → IsClosed P C

def recurrent_class_hittingProbability : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (C : Set S),
    IsCommunicatingClass P C → (∃ r ∈ C, Recurrent P r) →
    ∀ i ∈ C, ∀ j ∈ C, hittingProbability P {j} i = 1

end P207.Markov.ClosedRecurrentClassesSpec
