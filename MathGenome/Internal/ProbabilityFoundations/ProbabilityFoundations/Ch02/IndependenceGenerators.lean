import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceGenerators

/-! The generator assertion of Theorem 2.2 (paper.tex:507–535).
The pi-system extension theorem tests every finite subfamily, so no
assumption that the generators contain the whole space is needed.
-/

open MeasureTheory

namespace ProbabilityFoundations.Ch02

universe u v

/-- Mutual independence can be tested on generating pi-systems, even when
the generators omit the whole space. Empty index sets and empty generator
classes are allowed. -/
theorem mutuallyIndependent_iff_generators
    {Ω : Type u} {I : Type v} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : I → MeasurableSpace Ω) (C : I → Set (Set Ω))
    (hF : ∀ i, F i ≤ mΩ)
    (hC : ∀ i, ∀ A ∈ C i, ∀ B ∈ C i, A ∩ B ∈ C i)
    (hgen : ∀ i, F i = MeasurableSpace.generateFrom (C i)) :
    MutuallyIndependent P F ↔
      ∀ (s : Finset I) (A : I → Set Ω),
        (∀ i ∈ s, A i ∈ C i) →
          P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i) := by
  constructor
  · intro h s A hA
    apply h s A
    intro i hi
    rw [hgen i]
    exact MeasurableSpace.measurableSet_generateFrom (hA i hi)
  · intro h
    apply (mutuallyIndependent_iff_iIndep P F).mpr
    have hpi : ∀ i, IsPiSystem (C i) := by
      intro i A hA B hB _
      exact hC i A hA B hB
    have hind : ProbabilityTheory.iIndepSets C P := by
      apply (ProbabilityTheory.iIndepSets_iff C P).mpr
      intro s A hA
      exact h s A hA
    exact ProbabilityTheory.iIndepSets.iIndep hF C hpi hgen hind

end ProbabilityFoundations.Ch02
