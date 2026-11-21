import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.UnionBound

/-! Union bound and simultaneous avoidance: paper.tex, Proposition p205:W15.
No independence assumption is needed. -/

open MeasureTheory

universe u v

namespace P205.Probability

theorem union_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Type v} [Fintype I]
    (A : I → Set Ω) (_hA : ∀ i, MeasurableSet (A i)) :
    μ.real (⋃ i, A i) ≤ ∑ i, μ.real (A i) :=
  measureReal_iUnion_fintype_le A

theorem avoidance_lower_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Type v} [Fintype I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    1 - ∑ i, μ.real (A i) ≤ μ.real (⋂ i, (A i)ᶜ) := by
  rw [← Set.compl_iUnion, probReal_compl_eq_one_sub (MeasurableSet.iUnion hA)]
  exact sub_le_sub_left (union_bound μ A hA) 1

theorem positive_avoidance {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Type v} [Fintype I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hsum : (∑ i, μ.real (A i)) < 1) :
    0 < μ.real (⋂ i, (A i)ᶜ) :=
  lt_of_lt_of_le (sub_pos.mpr hsum) (avoidance_lower_bound μ A hA)

theorem exists_avoiding {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Type v} [Fintype I]
    (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hsum : (∑ i, μ.real (A i)) < 1) :
    ∃ ω : Ω, ∀ i, ω ∉ A i := by
  have hpos := positive_avoidance μ A hA hsum
  have hne : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra h
    have he : (⋂ i, (A i)ᶜ) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hpos
  obtain ⟨ω, hω⟩ := hne
  exact ⟨ω, fun i => Set.mem_iInter.mp hω i⟩

theorem empty_family {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {I : Type v} [Fintype I]
    [IsEmpty I] (A : I → Set Ω) :
    μ.real (⋃ i, A i) = 0 ∧ μ.real (⋂ i, (A i)ᶜ) = 1 := by
  simp

end P205.Probability
