import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RecurrenceInterfaces

/-! The Green criterion in paper.tex, §2.6 (p207:W10).
Visits include time zero, and all sums and expectations retain infinity.
The path law is the existing canonical law, with no assumed return identities. -/

open MeasureTheory
open scoped ENNReal MeasureTheory
universe u v
namespace P207.Markov
noncomputable section

/-- Total number of visits to `i`, including the visit at time zero if present. -/
def visitCount {S : Type u} (i : S) (ω : ℕ → S) : ℝ≥0∞ :=
  ∑' n : ℕ, ({p : ℕ → S | p n = i}).indicator (fun _ => (1 : ℝ≥0∞)) ω

/-- Diagonal Green series, including the zeroth transition power. -/
def greenSeries {S : Type u} (P : StochasticMatrix S) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, power P n i i

/-- Expected total number of visits under the law started at `i`. -/
def meanVisits {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S) : ℝ≥0∞ :=
  ∫⁻ ω, visitCount i ω ∂statePathLaw P i

namespace GreenCriterionSpec

def visitCountType := {S : Type u} → S → (ℕ → S) → ℝ≥0∞
def visitCountValue : visitCountType := @visitCount

def greenSeriesType := {S : Type u} → StochasticMatrix S → S → ℝ≥0∞
def greenSeriesValue : greenSeriesType := @greenSeries

def meanVisitsType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → S → ℝ≥0∞
def meanVisitsValue : meanVisitsType := @meanVisits

def measurable_visitCount : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S), Measurable (visitCount i)

/-- The formula also covers the absorbing case `r = 1` and `r = 0`, `k = 1`. -/
def visitCount_tail : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S) (k : ℕ),
  1 ≤ k → statePathLaw P i {ω | (k : ℝ≥0∞) ≤ visitCount i ω} =
    returnProbability P i ^ (k - 1)

def greenSeries_eq_meanVisits : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  greenSeries P i = meanVisits P i

def meanVisits_eq_inv : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  returnProbability P i < 1 → meanVisits P i = (1 - returnProbability P i)⁻¹

def meanVisits_eq_top : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  Recurrent P i → meanVisits P i = ⊤

def recurrent_iff_greenSeries_eq_top : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  Recurrent P i ↔ greenSeries P i = ⊤

def transient_iff_greenSeries_lt_top : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  Transient P i ↔ greenSeries P i < ⊤

def recurrent_infinite_visits : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : StochasticMatrix S) (i : S),
  Recurrent P i → ∀ᵐ ω ∂statePathLaw P i, visitCount i ω = ⊤

/-- Explicit applicability to a chain on any probability space and its given filtration. -/
def chain_visitCount_tail : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P (PMF.pure i) X ℱ μ → ∀ k : ℕ, 1 ≤ k →
      μ {ω | (k : ℝ≥0∞) ≤ visitCount i (fun n => X n ω)} =
        returnProbability P i ^ (k - 1)

def chain_meanVisits : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P (PMF.pure i) X ℱ μ →
      (∫⁻ ω, visitCount i (fun n => X n ω) ∂μ) = meanVisits P i

/-- The almost-sure assertion also holds on any realization started at `i`. -/
def chain_recurrent_infinite_visits : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Nonempty S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (i : S) (X : ℕ → Ω → S) (ℱ : Filtration ℕ m)
    (μ : Measure Ω) [IsProbabilityMeasure μ],
    IsMarkovChain P (PMF.pure i) X ℱ μ → Recurrent P i →
      ∀ᵐ ω ∂μ, visitCount i (fun n => X n ω) = ⊤

/-- Infinite total count means infinitely many distinct visit times. -/
def visitCount_eq_top_iff : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (i : S) (ω : ℕ → S),
  visitCount i ω = ⊤ ↔ Set.Infinite {n | ω n = i}

end GreenCriterionSpec
end
end P207.Markov
