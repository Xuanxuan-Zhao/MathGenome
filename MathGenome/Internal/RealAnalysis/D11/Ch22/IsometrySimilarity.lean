import MathGenome.Internal.RealAnalysis.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.IsometrySimilarity

/-! Isometry invariance and similarity scaling for the shared Hausdorff outer
measure (paper.tex:6050–6056), including exponent zero and nonsurjective maps. -/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

universe u v

namespace D11.Ch22

/-- The native diameter-cost construction agrees on arbitrary subsets. The
native `mkMetric` here removes only empty covering slots, so in particular this
bridge retains cost one for a singleton at exponent zero. -/
private theorem hausdorffOuterMeasure_eq_native {X : Type u} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s E = Measure.hausdorffMeasure (s : ℝ) E := by
  rw [hausdorffOuterMeasure_eq_mkMetric']
  change OuterMeasure.mkMetric (fun r => r ^ (s : ℝ)) E = _
  rw [OuterMeasure.coe_mkMetric]
  rfl

/-- Isometric embeddings preserve all Hausdorff outer measures. -/
theorem hausdorffOuterMeasure_isometry_image {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (hf : Isometry f)
    (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s (f '' E) = hausdorffOuterMeasure s E := by
  let : MeasurableSpace X := borel X
  let : MeasurableSpace Y := borel Y
  have : BorelSpace X := ⟨rfl⟩
  have : BorelSpace Y := ⟨rfl⟩
  rw [hausdorffOuterMeasure_eq_native, hausdorffOuterMeasure_eq_native]
  exact hf.hausdorffMeasure_image (Or.inl s.coe_nonneg) E

/-- A positive distance multiplier scales `H^s` by its `s`th power. This
includes `s = 0`, empty sets, infinite outer masses, and embeddings into a
larger ambient space. -/
theorem hausdorffOuterMeasure_similarity_image {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (r : ℝ≥0) (hr : 0 < r)
    (hf : ∀ x y, dist (f x) (f y) = (r : ℝ) * dist x y)
    (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s (f '' E) =
      (r : ℝ≥0∞) ^ (s : ℝ) * hausdorffOuterMeasure s E := by
  let : MeasurableSpace X := borel X
  let : MeasurableSpace Y := borel Y
  have : BorelSpace X := ⟨rfl⟩
  have : BorelSpace Y := ⟨rfl⟩
  rw [hausdorffOuterMeasure_eq_native, hausdorffOuterMeasure_eq_native]
  have hLip : LipschitzWith r f :=
    LipschitzWith.of_dist_le_mul fun x y => (hf x y).le
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hAnti : AntilipschitzWith r⁻¹ f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    rw [hf, NNReal.coe_inv, inv_mul_cancel_left₀ hr']
  apply le_antisymm (hLip.hausdorffMeasure_image_le s.coe_nonneg E)
  have h := hAnti.le_hausdorffMeasure_image s.coe_nonneg E
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    (r : ℝ≥0∞) ^ (s : ℝ) * Measure.hausdorffMeasure (s : ℝ) E ≤
        (r : ℝ≥0∞) ^ (s : ℝ) *
          ((r⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (s : ℝ) *
            Measure.hausdorffMeasure (s : ℝ) (f '' E) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left h (show 0 ≤ (r : ℝ≥0∞) ^ (s : ℝ) from zero_le)
    _ = Measure.hausdorffMeasure (s : ℝ) (f '' E) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ s.coe_nonneg,
        ENNReal.coe_inv hr.ne', ENNReal.mul_inv_cancel hr0 ENNReal.coe_ne_top,
        ENNReal.one_rpow, one_mul]

end D11.Ch22
