import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch09.IndependentRowObjects
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.FellerConverse

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace ProbabilityFoundations.Ch09.IndependentRows

variable {r : ℕ → ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

lemma normalized_sum_measurable (R : Row r Ω) (n : ℕ) :
    Measurable (sum R n) := by
  exact Finset.measurable_sum _ fun j _ => normalized_measurable R n j

/-- The positive quadratic defect of the real part of the exponential. -/
def cosineDefect (t y : ℝ) : ℝ := (t * y)^2 / 2 - (1 - Real.cos (t * y))

lemma cosineDefect_nonneg (t y : ℝ) : 0 ≤ cosineDefect t y := by
  have := Real.one_sub_sq_div_two_le_cos (x := t * y)
  unfold cosineDefect
  linarith

/-- At a frequency chosen for the tail threshold, a simple global tail bound
avoids a compactness argument for the strictly positive defect ratio. -/
lemma tail_le_cosineDefect {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    Set.indicator {y : ℝ | ε < |y|} (fun y => y^2) y ≤
      (ε^2 / 4) * cosineDefect (4 / ε) y := by
  by_cases hy : ε < |y|
  · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | ε < |y|} from hy)]
    have hs : ε^2 ≤ y^2 := by nlinarith [sq_abs y]
    have hc := Real.neg_one_le_cos (y * 4 / ε)
    have hp := mul_nonneg (sq_nonneg ε) (show 0 ≤ 1 + Real.cos (y * 4 / ε) by linarith)
    unfold cosineDefect
    have he : ε ≠ 0 := ne_of_gt hε
    field_simp
    nlinarith [sq_nonneg ε, sq_nonneg y]
  · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | ε < |y|} from hy)]
    exact mul_nonneg (by positivity) (cosineDefect_nonneg _ _)

lemma norm_exp_remainder_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ ≤ 3 * x^2 := by
  by_cases hx : |x| ≤ 1
  · have hb : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
    have h := Complex.norm_exp_sub_one_sub_id_le hb
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, sq_abs] at h
    nlinarith [sq_nonneg x]
  · have hx' : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ + ‖(x : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) + ‖(x : ℂ) * Complex.I‖ := by gcongr; exact norm_sub_le _ _
      _ = 2 + |x| := by simp only [Complex.norm_exp_ofReal_mul_I, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]; ring
      _ ≤ 3 * x^2 := by nlinarith [sq_abs x]

/-- The characteristic increment of one normalized entry. -/
def characteristicIncrement (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) : ℂ :=
  charFun ((R.μ n).map (normalized R n j)) t - 1

lemma integrable_exp_normalized (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    Integrable (fun ω => Complex.exp (((t * normalized R n j ω : ℝ) : ℂ) * Complex.I)) (R.μ n) := by
  have hm := normalized_measurable R n j
  apply Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
  filter_upwards [] with ω
  rw [Complex.norm_exp_ofReal_mul_I]

lemma characteristicIncrement_eq_integral (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    characteristicIncrement R n j t =
      ∫ ω, Complex.exp (((t * normalized R n j ω : ℝ) : ℂ) * Complex.I) - 1 -
        ((t * normalized R n j ω : ℝ) : ℂ) * Complex.I ∂R.μ n := by
  have he := integrable_exp_normalized R n j t
  have hl : Integrable (fun ω => ((t * normalized R n j ω : ℝ) : ℂ) * Complex.I) (R.μ n) :=
    ((normalized_integrable R n j).const_mul t).ofReal.mul_const _
  have hex : Integrable (fun ω => Complex.exp (((t * normalized R n j ω : ℝ) : ℂ) * Complex.I) - 1) (R.μ n) := he.sub (integrable_const _)
  rw [integral_sub hex hl, integral_sub he (integrable_const (1 : ℂ))]
  simp only [integral_mul_const, integral_complex_ofReal, integral_const_mul, normalized_centered,
    mul_zero, Complex.ofReal_zero, zero_mul, sub_zero, integral_const, probReal_univ,
    one_smul]
  unfold characteristicIncrement
  rw [charFun_apply_real, integral_map (normalized_measurable R n j).aemeasurable (by fun_prop)]
  simp only [Complex.ofReal_mul]

lemma norm_characteristicIncrement_le (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    ‖characteristicIncrement R n j t‖ ≤ (3 * t^2) * variance R n j := by
  rw [characteristicIncrement_eq_integral]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ ω, 3 * (t * normalized R n j ω)^2 ∂R.μ n := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · convert (normalized_square_integrable R n j).const_mul (3 * t^2) using 1
        funext ω; ring
      · exact Filter.Eventually.of_forall fun _ => norm_exp_remainder_le _
    _ = (3 * t^2) * variance R n j := by
      simp only [mul_pow, ← mul_assoc, integral_const_mul, variance]

lemma log_norm_one_add_error {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 + z‖ - z.re| ≤ ‖z‖^2 := by
  have h := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hz (by norm_num))
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
  calc
    _ = |(Complex.log (1 + z) - z).re| := by rw [Complex.sub_re, Complex.log_re]
    _ ≤ ‖Complex.log (1 + z) - z‖ := Complex.abs_re_le_norm _
    _ ≤ ‖z‖^2 * (1 - ‖z‖)⁻¹ / 2 := h
    _ ≤ ‖z‖^2 := by nlinarith [sq_nonneg ‖z‖]

lemma sum_norm_characteristicIncrement_sq_le (R : Row r Ω) (n : ℕ)
    (hpos : 0 < varianceSum R n) (t : ℝ) :
    ∑ j, ‖characteristicIncrement R n j t‖^2 ≤ (3 * t^2)^2 * maxVariance R n := by
  calc
    _ ≤ ∑ j, ((3 * t^2)^2 * maxVariance R n) * variance R n j := by
      apply Finset.sum_le_sum
      intro j _
      have hb := norm_characteristicIncrement_le R n j t
      have hm : ‖characteristicIncrement R n j t‖ ≤ (3 * t^2) * maxVariance R n :=
        hb.trans (mul_le_mul_of_nonneg_left (variance_le_max R n j) (by positivity))
      have hmul := mul_le_mul hm hb (norm_nonneg _) (mul_nonneg (by positivity) (maxVariance_nonneg R n))
      nlinarith [hmul]
    _ = (3 * t^2)^2 * maxVariance R n := by
      rw [← Finset.mul_sum, sum_variance_one R n hpos, mul_one]

lemma characteristicFunction_sum_eq_prod (R : Row r Ω) (n : ℕ) (t : ℝ) :
    charFun ((R.μ n).map (sum R n)) t = ∏ j, (1 + characteristicIncrement R n j t) := by
  have h := congrFun ((normalized_independent R n).charFun_map_fun_sum_eq_prod
    (fun j => (normalized_measurable R n j).aemeasurable)) t
  change charFun ((R.μ n).map (fun ω => ∑ j, normalized R n j ω)) t = _
  simpa only [Finset.prod_apply, characteristicIncrement, add_sub_cancel] using h

lemma log_norm_sum_error (R : Row r Ω) (n : ℕ) (t : ℝ)
    (hsmall : ∀ j, ‖characteristicIncrement R n j t‖ ≤ 1/2) :
    |Real.log ‖charFun ((R.μ n).map (sum R n)) t‖ -
      ∑ j, (characteristicIncrement R n j t).re| ≤
      ∑ j, ‖characteristicIncrement R n j t‖^2 := by
  have hn (j : Fin (r n)) : ‖1 + characteristicIncrement R n j t‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hz
    have he : characteristicIncrement R n j t = -1 := by linear_combination hz
    have := hsmall j
    rw [he] at this
    norm_num at this
  rw [characteristicFunction_sum_eq_prod, norm_prod, Real.log_prod (fun j _ => hn j),
    ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => log_norm_one_add_error (hsmall j))

lemma tendsto_sum_re_increment (R : Row r Ω)
    (hpos : ∀ n, 0 < varianceSum R n)
    (hmax : Tendsto (maxVariance R) atTop (𝓝 0)) (t : ℝ)
    (hcf : Tendsto (fun n => charFun ((R.μ n).map (sum R n)) t) atTop
      (𝓝 (Complex.exp ((-t^2 / 2 : ℝ) : ℂ)))) :
    Tendsto (fun n => ∑ j, (characteristicIncrement R n j t).re) atTop (𝓝 (-t^2/2)) := by
  have hbound : Tendsto (fun n => (3 * t^2) * maxVariance R n) atTop (𝓝 0) := by
    simpa using hmax.const_mul (3 * t^2)
  have hsmall : ∀ᶠ n in atTop, ∀ j, ‖characteristicIncrement R n j t‖ ≤ 1/2 := by
    filter_upwards [hbound.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hn j
    exact (norm_characteristicIncrement_le R n j t).trans
      ((mul_le_mul_of_nonneg_left (variance_le_max R n j) (by positivity)).trans hn.le)
  have herr : Tendsto (fun n => Real.log ‖charFun ((R.μ n).map (sum R n)) t‖ -
      ∑ j, (characteristicIncrement R n j t).re) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => (3 * t^2)^2 * maxVariance R n)
    · filter_upwards [hsmall] with n hn
      simpa only [Real.norm_eq_abs] using
        (log_norm_sum_error R n t hn).trans (sum_norm_characteristicIncrement_sq_le R n (hpos n) t)
    · simpa using hmax.const_mul ((3 * t^2)^2)
  have hlog : Tendsto (fun n => Real.log ‖charFun ((R.μ n).map (sum R n)) t‖) atTop
      (𝓝 (-t^2/2)) := by
    have hn : Tendsto (fun n => ‖charFun ((R.μ n).map (sum R n)) t‖) atTop
        (𝓝 (Real.exp (-t^2/2))) := by
      simpa only [Complex.norm_exp, Complex.ofReal_re] using hcf.norm
    simpa only [Function.comp_def, Real.log_exp] using
      (Real.continuousAt_log (ne_of_gt (Real.exp_pos _))).tendsto.comp hn
  simpa only [sub_sub_cancel, sub_zero] using hlog.sub herr

lemma integrable_cos_normalized (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    Integrable (fun ω => Real.cos (t * normalized R n j ω)) (R.μ n) := by
  simpa only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] using
    (integrable_exp_normalized R n j t).re

lemma re_characteristicIncrement (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    (characteristicIncrement R n j t).re =
      ∫ ω, Real.cos (t * normalized R n j ω) - 1 ∂R.μ n := by
  unfold characteristicIncrement
  rw [Complex.sub_re, Complex.one_re, charFun_apply_real,
    integral_map (normalized_measurable R n j).aemeasurable (by fun_prop)]
  have h := integral_re (integrable_exp_normalized R n j t)
  rw [integral_sub (integrable_cos_normalized R n j t) (integrable_const (1 : ℝ))]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  congr 1
  simp only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] at h
  simpa only [Complex.ofReal_mul] using h.symm

lemma integrable_cosineDefect (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    Integrable (fun ω => cosineDefect t (normalized R n j ω)) (R.μ n) := by
  have he : (fun ω => cosineDefect t (normalized R n j ω)) =
      (fun ω => (t^2/2) * (normalized R n j ω)^2 +
        (Real.cos (t * normalized R n j ω) - 1)) := by
    funext ω
    unfold cosineDefect
    ring
  rw [he]
  exact ((normalized_square_integrable R n j).const_mul _).add
    ((integrable_cos_normalized R n j t).sub (integrable_const _))

lemma integral_cosineDefect (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (t : ℝ) :
    (∫ ω, cosineDefect t (normalized R n j ω) ∂R.μ n) =
      (t^2/2) * variance R n j + (characteristicIncrement R n j t).re := by
  have he : (fun ω => cosineDefect t (normalized R n j ω)) =
      (fun ω => (t^2/2) * (normalized R n j ω)^2 +
        (Real.cos (t * normalized R n j ω) - 1)) := by
    funext ω
    unfold cosineDefect
    ring
  have hc : Integrable (fun ω => Real.cos (t * normalized R n j ω) - 1) (R.μ n) :=
    (integrable_cos_normalized R n j t).sub (integrable_const _)
  rw [he, integral_add ((normalized_square_integrable R n j).const_mul _) hc,
    integral_const_mul, ← re_characteristicIncrement]
  rfl

lemma sum_integral_cosineDefect (R : Row r Ω) (n : ℕ)
    (hpos : 0 < varianceSum R n) (t : ℝ) :
    (∑ j, ∫ ω, cosineDefect t (normalized R n j ω) ∂R.μ n) =
      t^2/2 + ∑ j, (characteristicIncrement R n j t).re := by
  simp_rw [integral_cosineDefect]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_variance_one R n hpos, mul_one]

lemma lindeberg_le_cosineDefect (R : Row r Ω) (n : ℕ)
    (hpos : 0 < varianceSum R n) {ε : ℝ} (hε : 0 < ε) :
    lindeberg R n ε ≤ (ε^2/4) *
      ((4/ε)^2/2 + ∑ j, (characteristicIncrement R n j (4/ε)).re) := by
  rw [← sum_integral_cosineDefect R n hpos, Finset.mul_sum]
  unfold lindeberg
  apply Finset.sum_le_sum
  intro j _
  rw [← integral_const_mul]
  apply integral_mono (lindeberg_integrable R n j ε)
    ((integrable_cosineDefect R n j (4/ε)).const_mul _)
  intro ω
  have h := tail_le_cosineDefect hε (normalized R n j ω)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h

/-- Feller's converse: Gaussian convergence plus asymptotically negligible
maximal normalized variance implies every strict Lindeberg tail tends to zero. -/
theorem feller_converse (R : Row r Ω)
    (hpos : ∀ n, 0 < varianceSum R n)
    (hweak : Tendsto (β := ProbabilityMeasure ℝ)
      (fun n => (⟨(R.μ n).map (sum R n), inferInstance⟩ : ProbabilityMeasure ℝ))
      atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)))
    (hmax : Tendsto (maxVariance R) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0) := by
  intro ε hε
  have hcf (t : ℝ) : Tendsto (fun n => charFun ((R.μ n).map (sum R n)) t) atTop
      (𝓝 (Complex.exp ((-t^2 / 2 : ℝ) : ℂ))) := by
    have h := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hweak t
    simpa only [ProbabilityMeasure.coe_mk, charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
      one_mul, zero_sub, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
      Complex.ofReal_ofNat, neg_div] using h
  have hreal := tendsto_sum_re_increment R hpos hmax (4/ε) (hcf (4/ε))
  apply squeeze_zero (fun n => lindeberg_nonneg R n ε)
    (fun n => lindeberg_le_cosineDefect R n (hpos n) hε)
  have hh := (hreal.const_add ((4/ε)^2/2)).const_mul (ε^2/4)
  have hz : (4/ε)^2/2 + -(4/ε)^2/2 = 0 := by ring
  simpa only [hz, mul_zero] using hh

end ProbabilityFoundations.Ch09.IndependentRows
