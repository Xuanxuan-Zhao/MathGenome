import MathGenome.Internal.RealAnalysis.D11.Ch22.DimensionDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HolderImageBound

/-!
# Hölder images of arbitrary subsets

We use the native diameter-cover estimate only after identifying its outer
measure evaluation with the shared coefficient-one construction. In particular
this identification concerns every subset, not only measurable sets. Dimension
is estimated directly from its shared infimum formula. No finiteness or
nonemptiness assumption on the domain is used.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u v

namespace D11.Ch22

/-- The real-distance inequality implies the native extended-distance condition. -/
theorem holderOnWith_of_dist_le {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (α C : ℝ≥0)
    (hf : ∀ x ∈ E, ∀ y ∈ E,
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) :
    HolderOnWith C α f E := by
  intro x hx y hy
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  exact_mod_cast hf x hx y hy

/-- Equality on arbitrary sets with the native measure evaluated as an outer
measure. The chosen Borel measurable structure adds no hypothesis on the set. -/
theorem hausdorffOuterMeasure_eq_native {X : Type u} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s E = Measure.hausdorffMeasure (s : ℝ) E := by
  rw [hausdorffOuterMeasure_eq_mkMetric']
  exact congrFun (OuterMeasure.coe_mkMetric (fun r => r ^ (s : ℝ))) E

/-- The quantitative estimate also holds at exponent zero. This stronger
auxiliary version lets us take the infimum over all zero-mass exponents. -/
theorem hausdorffOuterMeasure_holder_image_le {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] {f : X → Y} {E : Set X} {α C : ℝ≥0}
    (hf : HolderOnWith C α f E) (hα : 0 < α) (s : ℝ≥0) :
    hausdorffOuterMeasure (s / α) (f '' E) ≤
      (C : ℝ≥0∞) ^ ((s / α : ℝ≥0) : ℝ) * hausdorffOuterMeasure s E := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  rw [hausdorffOuterMeasure_eq_native, hausdorffOuterMeasure_eq_native]
  have hmul : (α : ℝ) * ((s / α : ℝ≥0) : ℝ) = (s : ℝ) := by
    rw [NNReal.coe_div]
    exact mul_div_cancel₀ _ (show (α : ℝ) ≠ 0 from ne_of_gt hα)
  simpa only [hmul] using hf.hausdorffMeasure_image_le hα (s / α).coe_nonneg

/-- paper.tex:6066–6071: the full quantitative outer-measure conclusion. -/
theorem holder_measure_image_bound {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (α C : ℝ≥0)
    (hα : 0 < α) (_hαone : α ≤ 1) (_hC : 0 < C)
    (hf : ∀ x ∈ E, ∀ y ∈ E,
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ))
    (s : ℝ≥0) (_hs : 0 < s) :
    hausdorffOuterMeasure (s / α) (f '' E) ≤
      (C : ℝ≥0∞) ^ ((s / α : ℝ≥0) : ℝ) * hausdorffOuterMeasure s E :=
  hausdorffOuterMeasure_holder_image_le (holderOnWith_of_dist_le f E α C hf) hα s

/-- paper.tex:6066–6071: the dimension conclusion, including zero and infinity. -/
theorem holder_dimension_image_bound {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (α C : ℝ≥0)
    (hα : 0 < α) (_hαone : α ≤ 1) (_hC : 0 < C)
    (hf : ∀ x ∈ E, ∀ y ∈ E,
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) :
    hausdorffDimension (f '' E) ≤ hausdorffDimension E / (α : ℝ≥0∞) := by
  have hα0 : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  rw [hausdorffDimension_eq_iInf E, ENNReal.iInf_div_of_ne hα0 ENNReal.coe_ne_top]
  refine le_iInf fun s => ?_
  rw [ENNReal.iInf_div_of_ne hα0 ENNReal.coe_ne_top]
  refine le_iInf fun hs => ?_
  have himage : hausdorffOuterMeasure (s / α) (f '' E) = 0 := by
    apply le_antisymm _ bot_le
    calc
      hausdorffOuterMeasure (s / α) (f '' E) ≤
          (C : ℝ≥0∞) ^ ((s / α : ℝ≥0) : ℝ) * hausdorffOuterMeasure s E :=
        hausdorffOuterMeasure_holder_image_le (holderOnWith_of_dist_le f E α C hf) hα s
      _ = 0 := by rw [hs, mul_zero]
  simpa only [ENNReal.coe_div hα.ne'] using hausdorffDimension_le_of_zero (s / α) (f '' E) himage

end D11.Ch22
