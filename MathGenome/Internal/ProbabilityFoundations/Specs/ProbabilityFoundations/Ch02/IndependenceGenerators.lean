import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces

/-! Independent specification of the generator assertion of Theorem 2.2,
paper.tex:507–535. The law assertion is allocated separately.

Binary intersection closure expresses the source's pi-system hypothesis
(equivalently, closure under intersections of nonempty finite subfamilies).
Neither the whole space nor nonemptiness is required of a generator class.
All finite sets of distinct indices are tested, including the empty set.
The ambient probability space need not be complete.
-/

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch02.IndependenceGenerators

universe u v

/-- The full finite-family generator criterion on the original probability space. -/
def independenceGeneratorsType : Prop :=
  ∀ {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : I → MeasurableSpace Ω) (C : I → Set (Set Ω)),
    (∀ i, F i ≤ mΩ) →
    (∀ i, ∀ A ∈ C i, ∀ B ∈ C i, A ∩ B ∈ C i) →
    (∀ i, F i = MeasurableSpace.generateFrom (C i)) →
    (IndependenceInterfaces.MutuallyIndependentValue P F ↔
      ∀ (s : Finset I) (A : I → Set Ω),
        (∀ i ∈ s, A i ∈ C i) →
          P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i))

end Specs.ProbabilityFoundations.Ch02.IndependenceGenerators
