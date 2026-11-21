import MathGenome.Internal.RealAnalysis.D11.Ch22.EuclideanUnitCubeBounds
import MathGenome.Internal.RealAnalysis.D11.Ch22.IsometrySimilarity
import MathGenome.Internal.RealAnalysis.D11.Ch22.CountableStability
import MathGenome.Internal.RealAnalysis.D11.Ch22.ZeroDimensionCounting
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.EuclideanDimension
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! Ambient Euclidean dimension bounds, paper.tex:6111–6117.

The infimum characterizations identify our dimension with native dimension,
using the proved equality of outer masses on arbitrary subsets. Native
finite-dimensional dimension theorems therefore retain the l2 metric and have
no measurable-set restriction. Positive finite cube mass follows from the
upstream unit-cube estimates and positive similarity scaling. The embedding
is defined only on the cube subtype, so no extension theorem is hidden in the
hypotheses. -/

noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal

namespace D11.Ch22.EuclideanDimension
open D11.Ch03

/-- The zero-exponent-infimum bridge on arbitrary metric spaces. -/
theorem hausdorffDimension_eq_dimH {X : Type*} [MetricSpace X] (E : Set X) :
    hausdorffDimension E = dimH E := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  rw [hausdorffDimension_eq_iInf, dimH_eq_iInf]
  simp_rw [EuclideanUnitCubeBounds.hausdorffOuterMeasure_eq_native]

theorem ambient_bound : Specs.D11.Ch22.EuclideanDimension.ambientBoundStatement := by
  intro n _ E
  change hausdorffDimension E ≤ (n : ℝ≥0∞)
  rw [hausdorffDimension_eq_dimH]
  calc
    dimH E ≤ dimH (univ : Set (Point n)) := dimH_mono (subset_univ E)
    _ = (n : ℝ≥0∞) := by rw [Real.dimH_univ_eq_finrank]; simp [Point]

theorem open_set : Specs.D11.Ch22.EuclideanDimension.openSetStatement := by
  intro n _ U hU hne
  have hdim : hausdorffDimension U = (n : ℝ≥0∞) := by
    rw [hausdorffDimension_eq_dimH]
    obtain ⟨x, hx⟩ := hne
    simpa [Point] using (Real.dimH_of_mem_nhds (hU.mem_nhds hx))
  refine ⟨hdim, fun s hs => ?_⟩
  apply hausdorffOuterMeasure_eq_top_of_lt_dimension s U
  rw [hdim]
  exact_mod_cast hs

theorem higher_exponent : Specs.D11.Ch22.EuclideanDimension.higherExponentStatement := by
  intro n hn s hs
  apply hausdorffOuterMeasure_eq_zero_of_dimension_lt s
  exact (ambient_bound n hn univ).trans_lt (by exact_mod_cast hs)

private theorem dilate_unit_cube (k : ℕ) (r : ℝ≥0) (hr : 0 < r) :
    (fun x : Point k => (r : ℝ) • x) '' closedBox (0 : Fin k → ℝ) 1 =
      closedBox (0 : Fin k → ℝ) (fun _ => (r : ℝ)) := by
  have hr' : 0 < (r : ℝ) := hr
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    change 0 ≤ (r : ℝ) * y j ∧ (r : ℝ) * y j ≤ (r : ℝ)
    exact ⟨mul_nonneg r.coe_nonneg (hy j).1,
      (mul_le_mul_of_nonneg_left (hy j).2 r.coe_nonneg).trans_eq (mul_one _)⟩
  · intro hx
    refine ⟨(r : ℝ)⁻¹ • x, ?_, ?_⟩
    · intro j
      change 0 ≤ (r : ℝ)⁻¹ * x j ∧ (r : ℝ)⁻¹ * x j ≤ 1
      constructor
      · exact mul_nonneg (inv_nonneg.mpr r.coe_nonneg) (hx j).1
      · calc
          (r : ℝ)⁻¹ * x j ≤ (r : ℝ)⁻¹ * (r : ℝ) :=
            mul_le_mul_of_nonneg_left (hx j).2 (inv_nonneg.mpr r.coe_nonneg)
          _ = 1 := inv_mul_cancel₀ hr'.ne'
    · simp [smul_smul, hr'.ne']

/-- Every positive-side cube has positive finite mass at its own dimension. -/
theorem cube_mass (k : ℕ) (hk : 1 ≤ k) (r : ℝ≥0) (hr : 0 < r) :
    0 < hausdorffOuterMeasure (k : ℝ≥0)
      (closedBox (0 : Fin k → ℝ) (fun _ => (r : ℝ))) ∧
    hausdorffOuterMeasure (k : ℝ≥0)
      (closedBox (0 : Fin k → ℝ) (fun _ => (r : ℝ))) < ∞ := by
  have hscale := hausdorffOuterMeasure_similarity_image
    (fun x : Point k => (r : ℝ) • x) r hr
    (fun x y => by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg])
    (k : ℝ≥0) (closedBox (0 : Fin k → ℝ) 1)
  rw [dilate_unit_cube k r hr] at hscale
  rw [hscale]
  obtain ⟨hl, hu⟩ := EuclideanUnitCubeBounds.unit_cube_bounds k hk
  have hpos : 0 < hausdorffOuterMeasure (k : ℝ≥0) (closedBox (0 : Fin k → ℝ) 1) :=
    zero_lt_one.trans_le hl
  have hfin := hu.trans_lt ENNReal.ofReal_lt_top
  constructor
  · exact ENNReal.mul_pos (ENNReal.rpow_pos (by exact_mod_cast hr) ENNReal.coe_ne_top).ne' hpos.ne'
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) hfin

theorem embedded_cube : Specs.D11.Ch22.EuclideanDimension.embeddedCubeStatement := by
  intro n k _ hk _ r hr f hf
  let C : Set (Point k) := closedBox (0 : Fin k → ℝ) (fun _ => (r : ℝ))
  have hmass (s : ℝ≥0) : hausdorffOuterMeasure s (range f) = hausdorffOuterMeasure s C := by
    rw [← image_univ, hausdorffOuterMeasure_isometry_image f hf]
    rw [← hausdorffOuterMeasure_isometry_image (fun x : C => (x : Point k))
      isometry_subtype_coe s univ]
    simp
  obtain ⟨hp, hfin⟩ := cube_mass k hk r hr
  have hdim : hausdorffDimension (range f) = (k : ℝ≥0∞) := by
    rw [hausdorffDimension_eq_dimH]
    apply dimH_of_hausdorffMeasure_ne_zero_ne_top (d := (k : ℝ≥0))
    · rw [← EuclideanUnitCubeBounds.hausdorffOuterMeasure_eq_native, hmass]
      exact hp.ne'
    · rw [← EuclideanUnitCubeBounds.hausdorffOuterMeasure_eq_native, hmass]
      exact hfin.ne
  change hausdorffDimension (range f) = (k : ℝ≥0∞) ∧
    0 < hausdorffOuterMeasure (k : ℝ≥0) (range f) ∧
    hausdorffOuterMeasure (k : ℝ≥0) (range f) < ∞
  exact ⟨hdim, (hmass _).symm ▸ hp, (hmass _).symm ▸ hfin⟩

theorem singleton : Specs.D11.Ch22.EuclideanDimension.singletonStatement := by
  intro n x
  exact ⟨hausdorffDimension_singleton x, hausdorffOuterMeasure_zero_singleton x⟩

end D11.Ch22.EuclideanDimension
