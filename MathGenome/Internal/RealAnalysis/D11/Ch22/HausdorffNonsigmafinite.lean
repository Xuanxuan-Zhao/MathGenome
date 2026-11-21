import MathGenome.Internal.RealAnalysis.D11.Ch22.ExponentThreshold
import MathGenome.Internal.RealAnalysis.D11.Ch22.EuclideanUnitCubeBounds
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffNonsigmafinite

/-! # Lower-dimensional Hausdorff measure is not sigma-finite

A finite mass at exponent `s < n` forces zero outer mass at exponent `n`.
A countable cover by such sets would force zero n-dimensional outer mass
of the Euclidean unit cube, contradicting its lower bound one. This uses
the positive cube mass directly, without needing a volume normalization.
-/

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace D11.Ch22.HausdorffNonsigmafinite

open D11.Ch03

/-- Every Borel restriction of the shared Hausdorff outer measure fails
sigma-finiteness when its exponent is smaller than the ambient dimension. -/
theorem borel_restriction_not_sigmaFinite :
    Specs.D11.Ch22.HausdorffNonsigmafinite.borelRestrictionStatement := by
  intro n _ s hsn μ hμ hfinite
  let : SigmaFinite μ := hfinite
  have hzero (k : ℕ) :
      hausdorffOuterMeasure (n : ℝ≥0) (spanningSets μ k) = 0 := by
    apply hausdorffOuterMeasure_eq_zero_of_lt_top s (n : ℝ≥0) _ hsn
    change Specs.D11.Ch22.HausdorffOuterMeasure.outerMeasureValue s
      (spanningSets μ k) < ∞
    rw [← hμ _ (measurableSet_spanningSets μ k)]
    exact measure_spanningSets_lt_top μ k
  have huniv : hausdorffOuterMeasure (n : ℝ≥0) (univ : Set (Point n)) = 0 := by
    apply le_antisymm _ zero_le
    calc
      hausdorffOuterMeasure (n : ℝ≥0) (univ : Set (Point n)) =
          hausdorffOuterMeasure (n : ℝ≥0) (⋃ k, spanningSets μ k) := by
            rw [iUnion_spanningSets]
      _ ≤ ∑' k, hausdorffOuterMeasure (n : ℝ≥0) (spanningSets μ k) :=
        measure_iUnion_le _
      _ = 0 := by simp only [hzero, tsum_zero]
  have hcube := (EuclideanUnitCubeBounds.unit_cube_bounds n
    (Nat.pos_of_ne_zero (NeZero.ne n))).1
  have hle : hausdorffOuterMeasure (n : ℝ≥0)
      (closedBox (0 : Fin n → ℝ) 1) ≤ 0 := by
    calc
      _ ≤ hausdorffOuterMeasure (n : ℝ≥0) (univ : Set (Point n)) :=
        measure_mono (subset_univ _)
      _ = 0 := huniv
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) (hcube.trans hle)

/-- The native Borel Hausdorff measure has precisely the shared outer values,
including the nonempty-singleton cost at exponent zero. -/
theorem hausdorff_not_sigmaFinite :
    Specs.D11.Ch22.HausdorffNonsigmafinite.nativeStatement := by
  intro n _ s hsn
  apply borel_restriction_not_sigmaFinite n s hsn
  intro E _
  exact (EuclideanUnitCubeBounds.hausdorffOuterMeasure_eq_native s E).symm

end D11.Ch22.HausdorffNonsigmafinite
