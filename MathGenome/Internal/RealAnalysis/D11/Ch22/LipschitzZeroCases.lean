import MathGenome.Internal.RealAnalysis.D11.Ch22.ZeroDimensionCounting
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.LipschitzZeroCases

/-! Lipschitz images, including exponent zero and zero Lipschitz constants.
All evaluations concern arbitrary sets and the shared outer measure. -/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

universe u v

namespace D11.Ch22

/-- In the current Mathlib, `mkMetric` uses nonempty covering sets, including
singletons. The shared `mkMetric'` bridge therefore identifies the native
measure on every subset, including at exponent zero. -/
private theorem outer_eq_native {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ≥0) (A : Set X) :
    hausdorffOuterMeasure s A = Measure.hausdorffMeasure (s : ℝ) A := by
  rw [hausdorffOuterMeasure_eq_mkMetric']
  exact congrFun (OuterMeasure.coe_mkMetric (fun r => r ^ (s : ℝ))) A

/-- A Lipschitz map defined only on `E`; source mass is measured in the ambient
space. In particular exponent zero is included. -/
theorem hausdorffOuterMeasure_lipschitz_image_le
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (L s : ℝ≥0) (_hL : 0 < L)
    (hf : LipschitzWith L f) (A : Set E) :
    hausdorffOuterMeasure s (f '' A) ≤ (L : ℝ≥0∞) ^ (s : ℝ) *
      hausdorffOuterMeasure s (Subtype.val '' A) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [outer_eq_native, outer_eq_native,
    (isometry_subtype_coe : Isometry (Subtype.val : E → X)).hausdorffMeasure_image (Or.inl s.coe_nonneg) A]
  exact hf.hausdorffMeasure_image_le s.coe_nonneg A

/-- A nonempty image under a zero-Lipschitz map is exactly one point. -/
theorem zero_lipschitz_image_singleton
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (hf : LipschitzWith 0 f)
    (A : Set E) (a : E) (ha : a ∈ A) : f '' A = {f a} := by
  apply Set.Subset.antisymm
  · rintro y ⟨b, _, rfl⟩
    apply Set.mem_singleton_iff.mpr
    apply edist_eq_zero.mp
    simpa using hf.edist_le_mul b a
  · exact singleton_subset_iff.mpr (mem_image_of_mem f ha)

theorem hausdorffOuterMeasure_zero_lipschitz_positive
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (hf : LipschitzWith 0 f)
    (A : Set E) (hA : A.Nonempty) (s : ℝ≥0) (hs : 0 < s) :
    hausdorffOuterMeasure s (f '' A) = 0 := by
  obtain ⟨a, ha⟩ := hA
  rw [zero_lipschitz_image_singleton E f hf A a ha, hausdorffOuterMeasure_apply]
  simp [hausdorffScaleContent_singleton s _ hs]

theorem hausdorffOuterMeasure_zero_lipschitz_counting
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (hf : LipschitzWith 0 f)
    (A : Set E) (hA : A.Nonempty) :
    hausdorffOuterMeasure 0 (f '' A) = 1 := by
  obtain ⟨a, ha⟩ := hA
  rw [zero_lipschitz_image_singleton E f hf A a ha,
    hausdorffOuterMeasure_zero_singleton]

theorem hausdorffOuterMeasure_empty_image
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (s : ℝ≥0) :
    f '' (∅ : Set E) = ∅ ∧ hausdorffOuterMeasure s (f '' (∅ : Set E)) = 0 := by
  simp

end D11.Ch22
