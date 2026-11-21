import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! Independent propositions for paper.tex, Proposition 1.2 and its following
counting-measure example (lines 133–157). No completeness or sigma-finiteness
is assumed. Monotone convergence here includes both the order and the limit. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch01.MeasureContinuity

universe u

def unionBoundType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω),
    (∀ n, MeasurableSet (s n)) → μ (⋃ n, s n) ≤ ∑' n, μ (s n)

def continuityFromBelowType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (A : Set Ω), (∀ n, MeasurableSet (s n)) → Monotone s → (⋃ n, s n) = A →
    Monotone (fun n => μ (s n)) ∧
      Tendsto (fun n => μ (s n)) atTop (𝓝 (μ A))

def continuityFromAboveType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (s : ℕ → Set Ω)
    (A : Set Ω), (∀ n, MeasurableSet (s n)) → Antitone s → (⋂ n, s n) = A →
    (∃ m, μ (s m) < ∞) →
    Antitone (fun n => μ (s n)) ∧
      Tendsto (fun n => μ (s n)) atTop (𝓝 (μ A))

def probabilityUnionBoundType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    P (⋃ n, s n) ≤ ∑' n, P (s n)

def probabilityContinuityFromBelowType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → Set Ω) (A : Set Ω), (∀ n, MeasurableSet (s n)) →
    Monotone s → (⋃ n, s n) = A →
    Monotone (fun n => P (s n)) ∧
      Tendsto (fun n => P (s n)) atTop (𝓝 (P A))

def probabilityContinuityFromAboveType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : ℕ → Set Ω) (A : Set Ω), (∀ n, MeasurableSet (s n)) →
    Antitone s → (⋂ n, s n) = A →
    Antitone (fun n => P (s n)) ∧
      Tendsto (fun n => P (s n)) atTop (𝓝 (P A))

/-- The standard measurable natural numbers and their canonical counting measure.
The last conjunct explicitly states the failure of continuity from above. -/
def countingTailsCounterexampleType : Prop :=
  (∀ n : ℕ, MeasurableSet (Set.Ici n)) ∧
  Antitone (fun n : ℕ => Set.Ici n) ∧
  (⋂ n : ℕ, Set.Ici n) = ∅ ∧
  (∀ n : ℕ, Measure.count (Set.Ici n) = ∞) ∧
  ¬ Tendsto (fun n : ℕ => Measure.count (Set.Ici n)) atTop
      (𝓝 (Measure.count (⋂ n : ℕ, Set.Ici n)))

end Specs.ProbabilityFoundations.Ch01.MeasureContinuity
