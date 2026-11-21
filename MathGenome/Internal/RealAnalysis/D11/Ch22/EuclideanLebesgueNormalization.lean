import MathGenome.Internal.RealAnalysis.D11.Ch22.EuclideanUnitCubeBounds
import MathGenome.Internal.RealAnalysis.D11.Ch22.IsometrySimilarity
import MathGenome.Internal.RealAnalysis.D11.Ch03.VolumeUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.EuclideanLebesgueNormalization
import Mathlib.Analysis.Normed.Group.Bounded

/-! Euclidean normalization of coefficient-one Hausdorff measure.

Bounded sets fit inside an affine image of the unit cube. Similarity scaling
and the accepted cube bound give finite mass there. Only after proving this,
nonzero mass and translation invariance do we apply Euclidean invariant-measure
uniqueness. The one-dimensional cube mass fixes the scalar to one.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

namespace D11.Ch22.EuclideanLebesgueNormalization

open D11.Ch03

private theorem native_mass (n : ℕ) (E : Set (Point n)) :
    Measure.hausdorffMeasure (n : ℝ) E = hausdorffOuterMeasure (n : ℝ≥0) E := by
  simpa using (EuclideanUnitCubeBounds.hausdorffOuterMeasure_eq_native (n : ℝ≥0) E).symm

/-- Every bounded set fits in a translated positive dilation of the unit cube. -/
private theorem bounded_subset_affine_cube {n : ℕ} (E : Set (Point n))
    (hE : Bornology.IsBounded E) :
    ∃ (a : Point n) (r : ℝ≥0), 0 < r ∧
      E ⊆ (fun x => a + (r : ℝ) • x) '' closedBox (0 : Fin n → ℝ) 1 := by
  obtain ⟨R, hR, hbound⟩ := hE.exists_pos_norm_le
  let a : Point n := WithLp.toLp 2 (fun _ => -R)
  let r : ℝ≥0 := ⟨2 * R, by positivity⟩
  have hr : 0 < r := by change 0 < 2 * R; positivity
  refine ⟨a, r, hr, ?_⟩
  intro x hx
  let y : Point n := WithLp.toLp 2 (fun j => (x j + R) / (2 * R))
  refine ⟨y, ?_, ?_⟩
  · intro j
    have hj' : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
    have hj : |x j| ≤ R := hj'.trans (hbound x hx)
    change 0 ≤ (x j + R) / (2 * R) ∧ (x j + R) / (2 * R) ≤ 1
    constructor
    · exact div_nonneg (by linarith [(abs_le.mp hj).1]) (by positivity)
    · apply (div_le_one (by positivity : 0 < 2 * R)).mpr
      linarith [(abs_le.mp hj).2]
  · ext j
    change -R + (2 * R) * ((x j + R) / (2 * R)) = x j
    field_simp [hR.ne']
    ring

private theorem affine_cube_mass {n : ℕ} (a : Point n) (r : ℝ≥0) (hr : 0 < r) :
    hausdorffOuterMeasure (n : ℝ≥0)
        ((fun x => a + (r : ℝ) • x) '' closedBox (0 : Fin n → ℝ) 1) =
      (r : ℝ≥0∞) ^ (n : ℝ) *
        hausdorffOuterMeasure (n : ℝ≥0) (closedBox (0 : Fin n → ℝ) 1) := by
  apply hausdorffOuterMeasure_similarity_image _ r hr
  intro x y
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg]

/-- Finiteness is proved for arbitrary bounded subsets, before uniqueness. -/
private theorem bounded_mass_lt_top (n : ℕ) [NeZero n]
    (E : Set (Point n)) (hE : Bornology.IsBounded E) :
    hausdorffOuterMeasure (n : ℝ≥0) E < ∞ := by
  obtain ⟨a, r, hr, hsub⟩ := bounded_subset_affine_cube E hE
  have hcube : hausdorffOuterMeasure (n : ℝ≥0)
      (closedBox (0 : Fin n → ℝ) 1) < ∞ :=
    (EuclideanUnitCubeBounds.unit_cube_bounds n
      (Nat.pos_of_ne_zero (NeZero.ne n))).2.trans_lt ENNReal.ofReal_lt_top
  calc
    hausdorffOuterMeasure (n : ℝ≥0) E ≤
        hausdorffOuterMeasure (n : ℝ≥0)
          ((fun x => a + (r : ℝ) • x) '' closedBox (0 : Fin n → ℝ) 1) := measure_mono hsub
    _ = (r : ℝ≥0∞) ^ (n : ℝ) *
        hausdorffOuterMeasure (n : ℝ≥0) (closedBox (0 : Fin n → ℝ) 1) :=
      affine_cube_mass a r hr
    _ < ∞ := ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hcube

theorem borel_measure_properties :
    Specs.D11.Ch22.EuclideanLebesgueNormalization.borelMeasurePropertiesStatement := by
  intro n _
  refine ⟨fun E _ => native_mass n E, ?_, ?_, ?_⟩
  · intro hzero
    have h := (EuclideanUnitCubeBounds.unit_cube_bounds n
      (Nat.pos_of_ne_zero (NeZero.ne n))).1
    rw [← native_mass, hzero] at h
    simp at h
  · intro a E _
    rw [native_mass, native_mass]
    exact hausdorffOuterMeasure_isometry_image _ (isometry_add_left a) _ E
  · intro E _ hE
    rw [native_mass]
    exact bounded_mass_lt_top n E hE

theorem euclidean_lebesgue_normalization :
    Specs.D11.Ch22.EuclideanLebesgueNormalization.normalizationStatement := by
  intro n _
  obtain ⟨_hbridge, hne, hinv, hfin⟩ := borel_measure_properties n
  obtain ⟨b, ⟨hb, hscale⟩, _⟩ :=
    D11.Ch03.VolumeUniqueness.translation_invariant_uniqueness n
      (Measure.hausdorffMeasure (n : ℝ)) hne hinv hfin
  have hmass (E : Set (Point n)) :
      hausdorffOuterMeasure (n : ℝ≥0) E =
        ENNReal.ofReal b * Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n E := by
    rw [← native_mass, hscale, Measure.smul_apply, smul_eq_mul]
  have hb_one : n = 1 → b = 1 := by
    intro hn
    subst n
    have h := hmass (closedBox (0 : Fin 1 → ℝ) 1)
    norm_num only [Nat.cast_one] at h
    rw [EuclideanUnitCubeBounds.unit_interval_mass] at h
    have hvol : Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value 1
        (closedBox (0 : Fin 1 → ℝ) 1) = 1 := by
      change volume (closedBox (0 : Fin 1 → ℝ) 1) = 1
      rw [D11.Ch03.OuterVolume.volume_closedBox]
      simp [boxContent]
    rw [hvol, mul_one] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal hb.le] using ht.symm
  refine ⟨b⁻¹, inv_pos.mpr hb, fun hn => by rw [hb_one hn, inv_one], ?_⟩
  intro E _
  change Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n E =
    ENNReal.ofReal b⁻¹ * hausdorffOuterMeasure (n : ℝ≥0) E
  rw [hmass, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le),
    inv_mul_cancel₀ hb.ne', ENNReal.ofReal_one, one_mul]

end D11.Ch22.EuclideanLebesgueNormalization
