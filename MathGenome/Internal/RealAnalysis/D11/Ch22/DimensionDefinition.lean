import MathGenome.Internal.RealAnalysis.D11.Ch22.ExponentThreshold
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.DimensionDefinition

/-!
# Hausdorff dimension and its endpoints

The dimension is the infimum of the nonnegative zero exponents, with values
in `ℝ≥0∞` and with the empty set assigned zero. All masses are outer masses:
there is no measurable-space parameter or measurability assumption.

Above the infimum there is a smaller zero exponent. Below the infimum, a
finite mass would force zero mass at an intermediate exponent, contradicting
the infimum. These arguments also handle dimension infinity. No assertion is
made about mass at the critical exponent.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u

namespace D11.Ch22

/-- Hausdorff dimension in the shared coefficient-one diameter normalization. -/
def hausdorffDimension {X : Type u} [MetricSpace X] (E : Set X) : ℝ≥0∞ :=
  Specs.D11.Ch22.DimensionDefinition.dimensionValue E

@[simp]
theorem hausdorffDimension_empty {X : Type u} [MetricSpace X] :
    hausdorffDimension (∅ : Set X) = 0 := by
  classical
  simp [hausdorffDimension, Specs.D11.Ch22.DimensionDefinition.dimensionValue]

/-- The zero-exponent infimum formula remains valid on the empty set. -/
theorem hausdorffDimension_eq_iInf {X : Type u} [MetricSpace X] (E : Set X) :
    hausdorffDimension E =
      ⨅ (s : ℝ≥0) (_ : hausdorffOuterMeasure s E = 0), (s : ℝ≥0∞) := by
  classical
  by_cases hE : E = ∅
  · subst E
    rw [hausdorffDimension_empty]
    apply le_antisymm bot_le
    exact iInf₂_le (0 : ℝ≥0)
      (measure_empty (μ := hausdorffOuterMeasure (X := X) 0))
  · simp only [hausdorffDimension,
      Specs.D11.Ch22.DimensionDefinition.dimensionValue, ite_eq_right hE,
      hausdorffOuterMeasure]

theorem hausdorffDimension_le_of_zero {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) (hzero : hausdorffOuterMeasure s E = 0) :
    hausdorffDimension E ≤ s := by
  rw [hausdorffDimension_eq_iInf]
  exact iInf₂_le s hzero

/-- This gives the convention for an empty set of zero exponents explicitly. -/
theorem hausdorffDimension_eq_top_iff {X : Type u} [MetricSpace X] (E : Set X) :
    hausdorffDimension E = ∞ ↔ ∀ s : ℝ≥0, hausdorffOuterMeasure s E ≠ 0 := by
  constructor
  · intro hdim s hzero
    have hle := hausdorffDimension_le_of_zero s E hzero
    rw [hdim] at hle
    exact ENNReal.coe_ne_top (top_le_iff.mp hle)
  · intro h
    rw [hausdorffDimension_eq_iInf]
    apply top_unique
    exact le_iInf fun s => le_iInf fun hs => False.elim (h s hs)

/-- Every finite nonnegative exponent strictly above dimension has zero mass. -/
theorem hausdorffOuterMeasure_eq_zero_of_dimension_lt {X : Type u} [MetricSpace X]
    (t : ℝ≥0) (E : Set X) (h : hausdorffDimension E < t) :
    hausdorffOuterMeasure t E = 0 := by
  rw [hausdorffDimension_eq_iInf] at h
  rcases iInf_lt_iff.mp h with ⟨s, hs⟩
  rcases iInf_lt_iff.mp hs with ⟨hzero, hst⟩
  exact hausdorffOuterMeasure_eq_zero_of_lt_top s t E
    (ENNReal.coe_lt_coe.mp hst) (by rw [hzero]; exact ENNReal.zero_lt_top)

/-- Every finite nonnegative exponent strictly below dimension has infinite mass. -/
theorem hausdorffOuterMeasure_eq_top_of_lt_dimension {X : Type u} [MetricSpace X]
    (s : ℝ≥0) (E : Set X) (h : (s : ℝ≥0∞) < hausdorffDimension E) :
    hausdorffOuterMeasure s E = ∞ := by
  by_contra hfinite
  obtain ⟨t, hst, htdim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have htzero := hausdorffOuterMeasure_eq_zero_of_lt_top s t E
    (ENNReal.coe_lt_coe.mp hst) (lt_top_iff_ne_top.mpr hfinite)
  exact htdim.not_ge (hausdorffDimension_le_of_zero t E htzero)

/-- Infinite dimension forces infinite mass at every allowed exponent. -/
theorem hausdorffOuterMeasure_eq_top_of_dimension_eq_top {X : Type u} [MetricSpace X]
    (E : Set X) (h : hausdorffDimension E = ∞) (s : ℝ≥0) :
    hausdorffOuterMeasure s E = ∞ := by
  apply hausdorffOuterMeasure_eq_top_of_lt_dimension s E
  rw [h]
  exact ENNReal.coe_lt_top

/-- At dimension zero there is no smaller nonnegative exponent. -/
theorem hausdorffDimension_zero_no_lower_exponent {X : Type u} [MetricSpace X]
    (E : Set X) (h : hausdorffDimension E = 0) :
    ¬ ∃ s : ℝ≥0, (s : ℝ≥0∞) < hausdorffDimension E := by
  simp only [h, not_lt_zero, exists_false, not_false_eq_true]

end D11.Ch22
