import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces

/-! Period assertion of paper.tex, §p207:W12. The shared gcd convention
includes the empty return set. The statements need no recurrence assumption. -/

universe u
namespace P207.Markov.ClassPeriodSpec

/-- Distinct communicating states have a common positive return length. -/
def communicate_common_returnLength : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) {i j : S},
    Communicate P i j → i ≠ j →
    ∃ n, n ∈ returnLengths P i ∧ n ∈ returnLengths P j

/-- Period is constant on every communicating class, including singleton classes. -/
def period_eq_of_communicate : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) {i j : S},
    Communicate P i j → period P i = period P j

end P207.Markov.ClassPeriodSpec
