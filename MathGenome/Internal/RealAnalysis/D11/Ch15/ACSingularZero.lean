import MathGenome.Internal.RealAnalysis.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.ACSingularZero

/-! AC and singularity force zero, and uniqueness of AC/singular decompositions
(`paper.tex:4890–4900`). The proof only uses measurable null supports, scalar
countable additivity and the partition criterion for zero variation. In
particular the reference measure need not be finite or sigma-finite.
-/

open Set MeasureTheory

universe u v

namespace D11.Ch15.ACSingularZero

open D11.Ch14.ScalarInterfaces D11.Ch14.TotalVariation
open D11.Ch15.AbsoluteContinuity

theorem ac_singular_zero {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α)
    (hac : scalarAbsolutelyContinuous ν μ) (hs : scalarPositiveSingular ν μ) :
    ν = 0 := by
  obtain ⟨A, hA, hν, hμ⟩ := hs
  have hcomp : totalVariation ν Aᶜ = 0 := by
    rw [totalVariation_apply ν Aᶜ hA.compl]
    exact hν
  have hmass : totalVariation ν univ = 0 := by
    rw [← union_compl_self A, measure_union disjoint_compl_right hA.compl,
      hac hμ, hcomp, add_zero]
  apply VectorMeasure.ext
  intro E hE
  have hzero := (totalVariation_null_iff ν univ MeasurableSet.univ).mp hmass
  simpa only [zero_apply] using hzero E hE (subset_univ E)

/-- Absolute continuity is preserved by taking differences, as is seen on
exactly the original measurable domain. -/
theorem absolutelyContinuous_sub {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν η : VectorMeasure α K) (μ : Measure α)
    (hν : scalarAbsolutelyContinuous ν μ) (hη : scalarAbsolutelyContinuous η μ) :
    scalarAbsolutelyContinuous (ν - η) μ := by
  apply (scalar_iff (ν - η) μ).mpr
  intro E hE hzero
  have hn := (scalar_iff ν μ).mp hν E hE hzero
  have he := (scalar_iff η μ).mp hη E hE hzero
  simp only [sub_apply, hn, he, sub_self]

/-- The union of two reference-null supports supports the difference. -/
theorem singular_sub {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν η : VectorMeasure α K) (μ : Measure α)
    (hν : scalarPositiveSingular ν μ) (hη : scalarPositiveSingular η μ) :
    scalarPositiveSingular (ν - η) μ := by
  obtain ⟨A, hA, hn, hμA⟩ := hν
  obtain ⟨B, hB, he, hμB⟩ := hη
  refine ⟨A ∪ B, hA.union hB, ?_, measure_union_null hμA hμB⟩
  apply (partitionVariation_null_iff (ν - η) (A ∪ B)ᶜ (hA.union hB).compl).mpr
  intro E hE hEAB
  have hnE := (partitionVariation_null_iff ν Aᶜ hA.compl).mp hn E hE
    (hEAB.trans (compl_subset_compl.mpr subset_union_left))
  have heE := (partitionVariation_null_iff η Bᶜ hB.compl).mp he E hE
    (hEAB.trans (compl_subset_compl.mpr subset_union_right))
  simp only [sub_apply, hnE, heE, sub_self]

theorem decomposition_unique {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α)
    (a₁ s₁ a₂ s₂ : VectorMeasure α K)
    (h₁ : ν = a₁ + s₁) (h₂ : ν = a₂ + s₂)
    (ha₁ : scalarAbsolutelyContinuous a₁ μ) (hs₁ : scalarPositiveSingular s₁ μ)
    (ha₂ : scalarAbsolutelyContinuous a₂ μ) (hs₂ : scalarPositiveSingular s₂ μ) :
    a₁ = a₂ ∧ s₁ = s₂ := by
  have hdiff : a₁ - a₂ = s₂ - s₁ := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact h₁.symm.trans (h₂.trans (add_comm a₂ s₂))
  have hsing : scalarPositiveSingular (a₁ - a₂) μ := by
    rw [hdiff]
    exact singular_sub s₂ s₁ μ hs₂ hs₁
  have hz := ac_singular_zero (a₁ - a₂) μ
    (absolutelyContinuous_sub a₁ a₂ μ ha₁ ha₂) hsing
  exact ⟨sub_eq_zero.mp hz, (sub_eq_zero.mp (hdiff.symm.trans hz)).symm⟩

end D11.Ch15.ACSingularZero
