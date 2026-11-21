import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.HittingProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Basic.Real.ENatENNReal

open MeasureTheory
open scoped ENNReal MeasureTheory Classical

universe u
namespace P207.Markov
noncomputable section

/-- Duration in extended nonnegative reals: count the times strictly before entrance.
The finite and infinite value theorems identify this with the usual inclusion
of `WithTop ℕ` into `ℝ≥0∞`. -/
def hittingDuration {S : Type u} (A : Set S) (ω : ℕ → S) : ℝ≥0∞ :=
  ∑' n : ℕ, if (n : WithTop ℕ) < hittingTime A ω then 1 else 0

/-- Extended nonnegative expectation, without a finiteness assumption. -/
def meanHittingTime {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S) : ℝ≥0∞ :=
  ∫⁻ ω, hittingDuration A ω ∂statePathLaw P i

namespace MeanHittingTimeSpec

def hittingDurationType := {S : Type u} → Set S → (ℕ → S) → ℝ≥0∞
def hittingDurationValue : hittingDurationType.{u} := @hittingDuration

def meanHittingTimeType := {S : Type u} → [Countable S] → [MeasurableSpace S] →
  [DiscreteMeasurableSpace S] → StochasticMatrix S → Set S → S → ℝ≥0∞
def meanHittingTimeValue : meanHittingTimeType.{u} := @meanHittingTime

def hittingDuration_at_finite : Prop :=
  ∀ {S : Type u} (A : Set S) (ω : ℕ → S) (n : ℕ),
    hittingTime A ω = n → hittingDuration A ω = n

def hittingDuration_at_top : Prop :=
  ∀ {S : Type u} (A : Set S) (ω : ℕ → S),
    hittingTime A ω = ⊤ → hittingDuration A ω = ⊤

/-- The duration is precisely the canonical extended-natural inclusion. -/
def hittingDuration_eq_toENNReal : Prop :=
  ∀ {S : Type u} (A : Set S) (ω : ℕ → S),
    hittingDuration A ω = ENat.toENNReal (hittingTime A ω)

/-- The expectation is the Lebesgue integral of the original entrance time. -/
def meanHittingTime_eq_lintegral : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    meanHittingTime P A i = ∫⁻ ω, ENat.toENNReal (hittingTime A ω) ∂statePathLaw P i

def meanHittingTime_boundary : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    i ∈ A → meanHittingTime P A i = 0

def meanHittingTime_equation : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (i : S),
    i ∉ A → meanHittingTime P A i = 1 + action P (meanHittingTime P A) i

def meanHittingTime_least : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (A : Set S) (v : S → ℝ≥0∞),
    (∀ i ∈ A, v i = 0) → (∀ i, i ∉ A → v i = 1 + action P v i) →
    ∀ i, meanHittingTime P A i ≤ v i

def meanHittingTime_empty : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S),
    meanHittingTime P ∅ i = ⊤

def meanHittingTime_univ : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (i : S),
    meanHittingTime P Set.univ i = 0

end MeanHittingTimeSpec
end
end P207.Markov
