import MathGenome.Internal.RealAnalysis.D11.Ch22.DimensionDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CountableStability

/-!
# Countable stability of Hausdorff dimension

Outer-mass monotonicity transfers zero exponents to subsets. For the upper
union bound, a finite exponent between the supremum and a purported larger
union dimension makes every member outer-null. Countable outer subadditivity
then contradicts that larger dimension. This also handles infinite dimensions
and the empty family without finiteness or measurability assumptions.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u v

namespace D11.Ch22

theorem hausdorffDimension_mono {X : Type u} [MetricSpace X] :
    Monotone (hausdorffDimension (X := X)) := by
  intro A B hAB
  rw [hausdorffDimension_eq_iInf B]
  refine le_iInf fun s => le_iInf fun hs => ?_
  exact hausdorffDimension_le_of_zero s A (measure_mono_null hAB hs)

/-- Countable unions, including empty indexed families. -/
theorem hausdorffDimension_iUnion {X : Type u} [MetricSpace X]
    {ι : Type v} [Countable ι] (E : ι → Set X) :
    hausdorffDimension (⋃ i, E i) = ⨆ i, hausdorffDimension (E i) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨s, hs, hsdim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hzero : hausdorffOuterMeasure s (⋃ i, E i) = 0 := by
      apply measure_iUnion_null
      intro i
      exact hausdorffOuterMeasure_eq_zero_of_dimension_lt s (E i)
        ((le_iSup (fun i => hausdorffDimension (E i)) i).trans_lt hs)
    exact hsdim.not_ge (hausdorffDimension_le_of_zero s _ hzero)
  · exact iSup_le fun i => hausdorffDimension_mono (subset_iUnion E i)

@[simp]
theorem hausdorffDimension_singleton {X : Type u} [MetricSpace X] (x : X) :
    hausdorffDimension ({x} : Set X) = 0 := by
  apply le_antisymm _ zero_le
  by_contra! h
  obtain ⟨s, hs, hsdim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hs' : (0 : ℝ≥0) < s := by exact_mod_cast hs
  have hzero : hausdorffOuterMeasure s ({x} : Set X) = 0 := by
    rw [hausdorffOuterMeasure_apply]
    simp [hausdorffScaleContent_singleton s _ hs' x]
  exact hsdim.not_ge (hausdorffDimension_le_of_zero s _ hzero)

theorem hausdorffDimension_eq_zero_of_countable {X : Type u} [MetricSpace X]
    (E : Set X) (hE : E.Countable) : hausdorffDimension E = 0 := by
  have : Countable E := hE.to_subtype
  have hcover : (⋃ x : E, ({(x : X)} : Set X)) = E := by
    ext x
    simp
  rw [← hcover, hausdorffDimension_iUnion]
  simp

end D11.Ch22
