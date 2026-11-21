import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorDimension
import MathGenome.Internal.RealAnalysis.D11.Ch22.CantorSharpHolder
import MathGenome.Internal.RealAnalysis.D11.Ch22.HolderImageBound

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace D11.Ch22.CantorDimension

open D11.Ch03.CantorConstruction
open CantorDigitSurjection

local notation "α" => Specs.D11.Ch22.CantorDigitSurjection.alpha_value
local notation "a" => Real.toNNReal Specs.D11.Ch22.CantorDigitSurjection.alpha_value
local notation "C" => D11.Ch03.CantorSet.C

lemma exponent_coe : (a : ℝ) = α := Real.coe_toNNReal α alpha_bounds.1.le

lemma interval_diameter (n : ℕ) (w : Fin n → Bool) :
    ediam (interval n w) = ENNReal.ofReal (1 / 3 : ℝ) ^ n := by
  simp [interval, Real.ediam_Icc, ENNReal.ofReal_pow, ENNReal.inv_pow]

lemma third_power : (ENNReal.ofReal (1 / 3 : ℝ)) ^ α = (2 : ℝ≥0∞)⁻¹ := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) (show 0 ≤ α from alpha_bounds.1.le)]
  have h : (1 / 3 : ℝ) ^ α = 1 / 2 := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, three_rpow_alpha]
  rw [h]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The level-n intervals have total critical cost exactly one. -/
lemma stage_cost (n : ℕ) :
    (∑ w : Fin n → Bool, ediam (interval n w) ^ α) = 1 := by
  simp only [interval_diameter]
  simp only [← ENNReal.rpow_natCast_mul, mul_comm (n : ℝ),
    ENNReal.rpow_mul, third_power]
  simp [← mul_pow, ENNReal.mul_inv_cancel]

lemma mass_upper : hausdorffOuterMeasure a C ≤ 1 := by
  rw [hausdorffOuterMeasure_eq_native, exponent_coe]
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / 3 : ℝ) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.ofReal_lt_one.mpr (by norm_num))
  have h := Measure.hausdorffMeasure_le_liminf_sum α C
    (fun n : ℕ => ENNReal.ofReal (1 / 3 : ℝ) ^ n) ht interval
    (Eventually.of_forall fun n w => (interval_diameter n w).le)
    (Eventually.of_forall fun n => ?_)
  · simpa only [stage_cost, liminf_const] using h
  · change _root_.cantorSet ⊆ ⋃ w : Fin n → Bool, interval n w
    rw [← Ch03.CantorSet.stage_intervals]
    exact iInter_subset _ n

lemma mass_lower : 1 ≤ hausdorffOuterMeasure a C := by
  have hα : 0 < a := Real.toNNReal_pos.mpr alpha_bounds.1
  have hα1 : a ≤ 1 := by
    exact_mod_cast (show (a : ℝ) ≤ 1 by rw [exponent_coe]; exact alpha_bounds.2.le)
  let f : ℝ → ℝ := Specs.D11.Ch03.CantorFunction.Gamma_value
  have hf : ∀ x ∈ C, ∀ y ∈ C,
      dist (f x) (f y) ≤ (1 : ℝ≥0) * dist x y ^ (a : ℝ) := by
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, exponent_coe,
      f, Specs.D11.Ch22.CantorDigitSurjection.F_value] using
      (CantorSharpHolder.sharp_holder ⟨y, hy⟩ ⟨x, hx⟩)
  have himage : f '' C = Icc (0 : ℝ) 1 := by
    rw [← F_range]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
  have h := holder_measure_image_bound f C a 1 hα hα1 (by norm_num) hf a hα
  have hunit : hausdorffOuterMeasure 1 (Icc (0 : ℝ) 1) = 1 := by
    rw [hausdorffOuterMeasure_eq_native]
    norm_num [hausdorffMeasure_real, Real.volume_Icc]
  simpa only [div_self hα.ne', ENNReal.coe_one, ENNReal.one_rpow,
    one_mul, himage, hunit] using h

theorem mass_bounds : Specs.D11.Ch22.CantorDimension.mass_bounds := by
  exact ⟨lt_of_lt_of_le (by norm_num) mass_lower, mass_upper⟩

theorem dimension : Specs.D11.Ch22.CantorDimension.dimension := by
  change hausdorffDimension C = ENNReal.ofReal α
  have hdim : hausdorffDimension C = (a : ℝ≥0∞) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro h
      have htop := hausdorffOuterMeasure_eq_top_of_lt_dimension a C h
      exact (lt_of_le_of_lt mass_upper (by simp : (1 : ℝ≥0∞) < ∞)).ne htop
    · apply le_of_not_gt
      intro h
      have hzero := hausdorffOuterMeasure_eq_zero_of_dimension_lt a C h
      have hpos : 0 < hausdorffOuterMeasure a C := lt_of_lt_of_le (by norm_num) mass_lower
      exact hpos.ne' hzero
  exact hdim

theorem lebesgue_null : Specs.D11.Ch22.CantorDimension.lebesgue_null :=
  D11.Ch03.CantorSet.C_lebesgue_null

end D11.Ch22.CantorDimension
