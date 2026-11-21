import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces

/-! Excursion occupation in paper.tex, p207:W14. All expectations and sums
are extended nonnegative integrals, including when the mean return is infinite. -/
open MeasureTheory
open scoped ENNReal MeasureTheory Classical
universe u
namespace P207.Markov
noncomputable section

/-- Number of visits to `j` at times strictly before the first positive return to `i`. -/
def excursionVisits {S : Type u} (i j : S) (ω : ℕ → S) : ℝ≥0∞ :=
  ∑' n : ℕ, if (n : WithTop ℕ) < returnTime i ω ∧ ω n = j then 1 else 0

/-- Expected occupation during a single excursion started at `i`. -/
def excursionMass {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i j : S) : ℝ≥0∞ :=
  ∫⁻ ω, excursionVisits i j ω ∂statePathLaw P i

/-- The mass divided by its total, used only under finite mean return. -/
def normalizedExcursionMass {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i j : S) : ℝ≥0∞ :=
  excursionMass P i j / meanReturnTime P i

namespace ExcursionMeasureSpec

def excursionVisitsType := {S : Type u} → S → S → (ℕ → S) → ℝ≥0∞
def excursionVisitsValue : excursionVisitsType := @excursionVisits

def excursionMassType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → S → ℝ≥0∞
def excursionMassValue : excursionMassType := @excursionMass

def normalizedExcursionMassType := excursionMassType.{u}
def normalizedExcursionMassValue : normalizedExcursionMassType := @normalizedExcursionMass

def excursionMass_self : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S), excursionMass P i i = 1

def excursionMass_finite : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (hP : Irreducible P) (i : S) (hi : Recurrent P i)
    (j : S), excursionMass P i j < ⊤

def excursionMass_invariant : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S) (hi : Recurrent P i) (j : S),
    ∑' k, excursionMass P i k * P k j = excursionMass P i j

def excursionMass_total : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
    ∑' j, excursionMass P i j = meanReturnTime P i

def normalizedExcursion_stationary : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S) (hi : PositiveRecurrent P i),
    (∑' j, normalizedExcursionMass P i j = 1) ∧
    ∀ j, ∑' k, normalizedExcursionMass P i k * P k j = normalizedExcursionMass P i j

def excursion_stationary_probability : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S) (hi : PositiveRecurrent P i),
    ∃ ν : ProbabilityLaw S, (∀ j, ν j = excursionMass P i j / meanReturnTime P i) ∧
      ν.bind P = ν

end ExcursionMeasureSpec
end
end P207.Markov
