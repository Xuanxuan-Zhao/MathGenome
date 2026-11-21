import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces

/-! Recurrence classification in paper.tex, §2.8 (p207:W12).
The communicating states may lie in a proper class of a reducible chain. -/

universe u
namespace P207.Markov.ClassRecurrenceSpec

def recurrent_iff_of_communicate : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) {i j : S},
    Communicate P i j → (Recurrent P i ↔ Recurrent P j)

def transient_iff_of_communicate : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) {i j : S},
    Communicate P i j → (Transient P i ↔ Transient P j)

end P207.Markov.ClassRecurrenceSpec
