import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CanonicalPathLaw
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping
import Mathlib.Probability.Process.HittingTime

/-! First entrance includes time zero; the no-hit value is infinity.
All probabilities and nonnegative kernel sums use `ℝ≥0∞`, so the
minimality theorem also covers solutions with infinite coordinates. -/

open MeasureTheory
open scoped ENNReal MeasureTheory

universe u
namespace P207.Markov
noncomputable section

/-- The canonical first entrance into an arbitrary subset of states. -/
def hittingTime {S : Type u} (A : Set S) : (ℕ → S) → WithTop ℕ :=
  hittingAfter coordinate A 0

/-- Probability of ever entering `A`, for the canonical law started at `i`. -/
def hittingProbability {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S) : ℝ≥0∞ :=
  statePathLaw P i {ω | hittingTime A ω < ⊤}

namespace HittingProbabilitySpec

def hittingTimeType := {S : Type u} → Set S → (ℕ → S) → WithTop ℕ
def hittingTimeValue : hittingTimeType.{u} := @hittingTime

def hittingProbabilityType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → Set S → S → ℝ≥0∞
def hittingProbabilityValue : hittingProbabilityType.{u} := @hittingProbability

/-- A finite cutoff is reached exactly when one of its coordinates is in `A`. -/
def hittingTime_le_iff : Prop :=
  ∀ {S : Type u} (A : Set S) (ω : ℕ → S) (n : ℕ),
    hittingTime A ω ≤ n ↔ ∃ k ≤ n, ω k ∈ A

def hittingTime_finite_iff : Prop :=
  ∀ {S : Type u} (A : Set S) (ω : ℕ → S),
    hittingTime A ω < ⊤ ↔ ∃ k : ℕ, ω k ∈ A

def hittingTime_isStoppingTime : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (A : Set S), P207.IsDiscreteStoppingTime coordinateFiltration (hittingTime A)

def hittingProbability_le_one : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    hittingProbability P A i ≤ 1

def hittingProbability_boundary : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    i ∈ A → hittingProbability P A i = 1

def hittingProbability_harmonic : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    i ∉ A → hittingProbability P A i = action P (hittingProbability P A) i

def hittingProbability_least : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (v : S → ℝ≥0∞),
    (∀ i ∈ A, v i = 1) → (∀ i, i ∉ A → v i = action P v i) →
    ∀ i, hittingProbability P A i ≤ v i

def hittingProbability_empty : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S),
    hittingProbability P ∅ i = 0

def hittingProbability_univ : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S),
    hittingProbability P Set.univ i = 1

end HittingProbabilitySpec
end
end P207.Markov
