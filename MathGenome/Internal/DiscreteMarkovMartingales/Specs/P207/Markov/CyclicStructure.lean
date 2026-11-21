import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClassPeriod
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.StationaryReturnTimes
import Mathlib.Data.Nat.ModEq

/-! Cyclic partition and skeleton conclusions in paper.tex, p207:W17.
`label` encodes disjointness and exhaustion; surjectivity encodes nonempty
classes. Kernels below live on the actual class subtype, with the inherited
discrete measurable space, and their entries are exactly those of `P^d`.
No partition or skeleton irreducibility certificate is a hypothesis of the
existence statements; `cyclic_structure` also constructs the stationary law. -/

open scoped ENNReal
universe u
namespace P207.Markov
noncomputable section

structure CyclicPartition {S : Type u} (P : StochasticMatrix S) (d : ℕ) where
  period_pos : 0 < d
  label : S → Fin d
  onto : Function.Surjective label
  step : ∀ i j, 0 < P i j → (label j).val = ((label i).val + 1) % d

namespace CyclicPartition
variable {S : Type u} {P : StochasticMatrix S} {d : ℕ}

def classSet (c : CyclicPartition P d) (l : Fin d) : Set S := {i | c.label i = l}

def next (c : CyclicPartition P d) (l : Fin d) : Fin d :=
  ⟨(l.val + 1) % d, Nat.mod_lt _ c.period_pos⟩

/-- All stationary and skeleton conclusions, with explicit entry formulas.
The full-space law `μ l` is the paper's `π_l`. Its restriction `ν` to the
class is stationary for the actual restricted skeleton `Q`. -/
def StationaryData [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (c : CyclicPartition P d) (π : ProbabilityLaw S) : Prop :=
  (∀ l, lawEvent π (c.classSet l) = 1 / (d : ℝ≥0∞)) ∧
  ∃ μ : Fin d → ProbabilityLaw S,
    (∀ l i, μ l i = if c.label i = l then (d : ℝ≥0∞) * π i else 0) ∧
    (∀ l, (μ l).bind P = μ (c.next l)) ∧
    (∀ l, evolve (μ l) P d = μ l) ∧
    ∀ l, ∃ (Q : StochasticMatrix (c.classSet l)) (ν : ProbabilityLaw (c.classSet l)),
      (∀ i j, Q i j = power P d i.val j.val) ∧
      (∀ i, ν i = (d : ℝ≥0∞) * π i.val) ∧
      Irreducible Q ∧ (∀ i, Aperiodic Q i) ∧ IsStationary Q ν ∧
      (∀ i, PositiveRecurrent Q i)
end CyclicPartition

namespace CyclicStructureSpec

def exists_cyclicPartition : Prop :=
  ∀ {S : Type u} (P : StochasticMatrix S) (a : S),
    Irreducible P → Nonempty (CyclicPartition P (period P a))

def cyclic_structure_of_stationary : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (π : ProbabilityLaw S) (d : ℕ),
    Irreducible P → IsStationary P π → (∀ i, period P i = d) →
    ∃ c : CyclicPartition P d, c.StationaryData π

def cyclic_structure : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (d : ℕ),
    Irreducible P → (∃ i, PositiveRecurrent P i) → (∀ i, period P i = d) →
    ∃ (π : ProbabilityLaw S), IsStationary P π ∧
      ∃ c : CyclicPartition P d, c.StationaryData π

end CyclicStructureSpec
end
end P207.Markov
