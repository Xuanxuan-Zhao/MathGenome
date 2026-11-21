import MathGenome.Internal.RealAnalysis.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.ExponentThreshold

/-!
# The critical exponent of Hausdorff outer measure

The shared outer measure agrees on arbitrary subsets with Mathlib's Hausdorff
measure evaluation. This follows from the upstream `mkMetric'` bridge and
Mathlib's trimming identity for diameter costs; it requires no measurability of
the set. Thus the native zero-or-infinity theorem applies also at exponent zero,
where both covering definitions charge one for every nonempty set.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u

namespace D11.Ch22

/-- The exponent dichotomy for arbitrary subsets, including exponent zero. -/
theorem hausdorffOuterMeasure_zero_or_top {X : Type u} [MetricSpace X]
    (s t : ℝ≥0) (E : Set X) (hst : s < t) :
    hausdorffOuterMeasure t E = 0 ∨ hausdorffOuterMeasure s E = ∞ := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have hnative (q : ℝ≥0) :
      hausdorffOuterMeasure q E = Measure.hausdorffMeasure (q : ℝ) E := by
    rw [hausdorffOuterMeasure_eq_mkMetric']
    exact congrFun (OuterMeasure.coe_mkMetric (fun r => r ^ (q : ℝ))) E
  rw [hnative t, hnative s]
  exact Measure.hausdorffMeasure_zero_or_top (show (s : ℝ) < (t : ℝ) from hst) E

/-- paper.tex, D11.22.exponent_threshold: a finite mass at `s` implies zero
mass at every larger exponent. No measurability assumption on `E` is needed. -/
theorem hausdorffOuterMeasure_eq_zero_of_lt_top {X : Type u} [MetricSpace X]
    (s t : ℝ≥0) (E : Set X) (hst : s < t)
    (hfinite : hausdorffOuterMeasure s E < ∞) :
    hausdorffOuterMeasure t E = 0 := by
  rcases hausdorffOuterMeasure_zero_or_top s t E hst with hzero | htop
  · exact hzero
  · exact (hfinite.ne htop).elim

/-- The equivalent contrapositive: positive mass at `t` implies infinite mass
at every smaller nonnegative exponent. -/
theorem hausdorffOuterMeasure_eq_top_of_pos {X : Type u} [MetricSpace X]
    (s t : ℝ≥0) (E : Set X) (hst : s < t)
    (hpos : 0 < hausdorffOuterMeasure t E) :
    hausdorffOuterMeasure s E = ∞ := by
  rcases hausdorffOuterMeasure_zero_or_top s t E hst with hzero | htop
  · exact (hpos.ne' hzero).elim
  · exact htop

end D11.Ch22
