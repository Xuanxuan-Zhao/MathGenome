import MathGenome.Internal.RealAnalysis.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.ZeroDimensionCounting

/-! Zero-dimensional Hausdorff outer measure counts points (paper.tex:6040).
Finite sets are Borel, so finite additivity and singleton cost one give their
exact mass. Arbitrarily large finite subsets force infinite sets to have
infinite outer measure. No measurability is required of the set being counted. -/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u

namespace D11.Ch22

@[simp]
theorem hausdorffOuterMeasure_zero_singleton {X : Type u} [MetricSpace X] (x : X) :
    hausdorffOuterMeasure 0 ({x} : Set X) = 1 := by
  rw [hausdorffOuterMeasure_apply]
  simp only [hausdorffScaleContent_zero_singleton]
  apply le_antisymm
  · exact iSup₂_le fun δ hδ => le_rfl
  · exact le_iSup₂_of_le (1 : ℝ≥0) zero_lt_one le_rfl

theorem hausdorffOuterMeasure_zero_finite {X : Type u} [MetricSpace X]
    (E : Set X) (hE : E.Finite) :
    hausdorffOuterMeasure 0 E = (hE.toFinset.card : ℝ≥0∞) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := (hausdorffOuterMeasure 0).toMeasure
    (hausdorffOuterMeasure_borel_le 0)
  have hμ (A : Set X) (hA : MeasurableSet A) : μ A = hausdorffOuterMeasure 0 A :=
    toMeasure_apply _ _ hA
  calc
    hausdorffOuterMeasure 0 E = μ E := (hμ E hE.measurableSet).symm
    _ = ∑ x ∈ hE.toFinset, μ ({x} : Set X) := by
      simpa only [hE.coe_toFinset] using
        (sum_measure_singleton (μ := μ) (s := hE.toFinset)).symm
    _ = (hE.toFinset.card : ℝ≥0∞) := by
      simp [hμ, hausdorffOuterMeasure_zero_singleton]

theorem hausdorffOuterMeasure_zero_infinite {X : Type u} [MetricSpace X]
    (E : Set X) (hE : E.Infinite) : hausdorffOuterMeasure 0 E = ∞ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  obtain ⟨F, hFE, hF⟩ := hE.exists_subset_card_eq n
  calc
    (n : ℝ≥0∞) = hausdorffOuterMeasure 0 (F : Set X) := by
      rw [hausdorffOuterMeasure_zero_finite _ F.finite_toSet]
      simpa using congrArg (fun k : ℕ => (k : ℝ≥0∞)) hF.symm
    _ ≤ hausdorffOuterMeasure 0 E := measure_mono hFE

/-- This one formula includes finite sets, infinite sets, and the empty set. -/
theorem hausdorffOuterMeasure_zero_counting {X : Type u} [MetricSpace X]
    (E : Set X) : hausdorffOuterMeasure 0 E = (E.encard : ℝ≥0∞) := by
  rcases E.finite_or_infinite with hE | hE
  · rw [hausdorffOuterMeasure_zero_finite E hE, hE.encard_eq_coe_toFinset_card]
    simp
  · rw [hausdorffOuterMeasure_zero_infinite E hE, hE.encard_eq]
    simp

end D11.Ch22
