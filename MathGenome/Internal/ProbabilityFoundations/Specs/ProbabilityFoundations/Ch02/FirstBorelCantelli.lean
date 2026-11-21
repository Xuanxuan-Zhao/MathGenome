import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.MeasureContinuity

/-! Independent specification for the first assertion of Theorem 2.6,
paper.tex:624–643. The tail intersection starts at positive natural indices,
as in the source. No completeness or independence is assumed. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch02.FirstBorelCantelli

universe u

def infinitelyOftenEventType := ∀ {Ω : Type u}, (ℕ → Set Ω) → Set Ω

def infinitelyOftenEventValue : infinitelyOftenEventType :=
  fun A => ⋂ m : ℕ, ⋂ (_ : 1 ≤ m), ⋃ n ≥ m, A n

def measurableInfinitelyOftenEventType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (A : ℕ → Set Ω),
    (∀ n, MeasurableSet (A n)) → MeasurableSet (infinitelyOftenEventValue A)

/-- Explicitly connect the null-event conclusion to finitely many occurrences. -/
def infinitelyOftenNullIffAeFiniteType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (A : ℕ → Set Ω),
    P (infinitelyOftenEventValue A) = 0 ↔
      ∀ᵐ ω ∂P, {n : ℕ | ω ∈ A n}.Finite

def firstBorelCantelliType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∀ n, MeasurableSet (A n)) →
    (∑' n, P (A n)) < ∞ → P (infinitelyOftenEventValue A) = 0

def aeFiniteOccurrencesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω), (∀ n, MeasurableSet (A n)) →
    (∑' n, P (A n)) < ∞ → ∀ᵐ ω ∂P, {n : ℕ | ω ∈ A n}.Finite

end Specs.ProbabilityFoundations.Ch02.FirstBorelCantelli
