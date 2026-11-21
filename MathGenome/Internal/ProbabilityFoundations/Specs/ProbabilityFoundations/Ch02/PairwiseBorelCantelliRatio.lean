import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.FirstBorelCantelli
import Mathlib.Topology.Instances.Real.Lemmas

/-! The quantitative second Borel–Cantelli theorem, paper.tex:627–670.
Counts and means include indices `0, …, n`. Only pairwise independence is
assumed, and no completeness or identical-distribution hypothesis is used. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio
universe u

def occurrenceCountType := ∀ {Ω : Type u}, (ℕ → Set Ω) → ℕ → Ω → ℝ
noncomputable def occurrenceCountValue : occurrenceCountType :=
  fun A n ω => ∑ k ∈ Finset.range (n + 1), (A k).indicator (fun _ => (1 : ℝ)) ω

def expectedOccurrenceCountType := ∀ {Ω : Type u} [MeasurableSpace Ω],
  Measure Ω → (ℕ → Set Ω) → ℕ → ℝ
noncomputable def expectedOccurrenceCountValue : expectedOccurrenceCountType :=
  fun P A n => ∑ k ∈ Finset.range (n + 1), (P (A k)).toReal

def expectedCountTendstoType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∑' n, P (A n)) = ∞ →
    Tendsto (expectedOccurrenceCountValue P A) atTop atTop

def expectedCountEventuallyPositiveType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∑' n, P (A n)) = ∞ →
    ∀ᶠ n in atTop, 0 < expectedOccurrenceCountValue P A n

def pairwiseBorelCantelliRatioType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∀ n, MeasurableSet (A n)) →
    IndependenceInterfaces.PairwiseIndependentEventsValue P A →
    (∑' n, P (A n)) = ∞ →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => occurrenceCountValue A n ω / expectedOccurrenceCountValue P A n)
      atTop (𝓝 1)

/-- All pathwise conclusions hold on one event in the original sigma algebra. -/
def commonProbabilityOneEventType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∀ n, MeasurableSet (A n)) →
    IndependenceInterfaces.PairwiseIndependentEventsValue P A →
    (∑' n, P (A n)) = ∞ →
    ∃ E : Set Ω, MeasurableSet E ∧ P E = 1 ∧ ∀ ω ∈ E,
      Tendsto (fun n => occurrenceCountValue A n ω / expectedOccurrenceCountValue P A n)
        atTop (𝓝 1) ∧
      Tendsto (fun n => occurrenceCountValue A n ω) atTop atTop ∧
      ω ∈ FirstBorelCantelli.infinitelyOftenEventValue A

def secondBorelCantelliType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∀ n, MeasurableSet (A n)) →
    IndependenceInterfaces.PairwiseIndependentEventsValue P A →
    (∑' n, P (A n)) = ∞ → P (FirstBorelCantelli.infinitelyOftenEventValue A) = 1

end Specs.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio
