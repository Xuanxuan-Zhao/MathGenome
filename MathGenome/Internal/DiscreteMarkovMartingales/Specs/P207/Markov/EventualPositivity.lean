import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClassPeriod

/-! Eventual positivity from the first paragraph of the proof of paper.tex,
§p207:W16. These statements use the canonical transition powers and period.
No recurrence or stationary law is assumed. The algebraic results are valid
without countability, and hence in particular for the paper's countable chains. -/

universe u
namespace P207.Markov.EventualPositivitySpec

/-- An addition-closed set of natural numbers with gcd one contains a tail.
Zero need not belong to the set. -/
def eventually_mem_of_add_closed_setGcd_one : Prop :=
  ∀ (s : Set ℕ),
    (∀ m ∈ s, ∀ n ∈ s, m + n ∈ s) → Nat.setGcd s = 1 →
    ∃ N : ℕ, ∀ n ≥ N, n ∈ s

/-- Every sufficiently large positive integer is a return length at an
aperiodic state. -/
def eventual_returnLengths : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (a : S),
    Aperiodic P a → ∃ N : ℕ, ∀ n ≥ N, n ∈ returnLengths P a

/-- A single aperiodic state of an irreducible chain suffices for eventual
positivity between every pair of states. The threshold may depend on the pair. -/
def eventual_power_pos_of_aperiodic : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S), Irreducible P →
    ∀ a : S, Aperiodic P a →
    ∀ i j : S, ∃ N : ℕ, ∀ n ≥ N, 0 < power P n i j

/-- The irreducible aperiodic kernel has positive entries at all sufficiently
large times, for each specified pair of states. -/
def eventual_power_pos : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S), Irreducible P →
    (∀ a : S, Aperiodic P a) →
    ∀ i j : S, ∃ N : ℕ, ∀ n ≥ N, 0 < power P n i j

end P207.Markov.EventualPositivitySpec
