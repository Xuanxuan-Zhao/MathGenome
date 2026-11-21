import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.RealDistributionFunctions
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.TailAndTruncatedMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch07.InfiniteMomentExample

lemma magnitudeTail_eq_inverse (r : ℝ) :
    magnitudeTail r = 1 / (max r (Real.exp 1) * Real.log (max r (Real.exp 1))) := by
  unfold magnitudeTail
  split_ifs with hr
  · rw [max_eq_right hr.le, Real.log_exp]
    simp
  · rw [max_eq_left (le_of_not_gt hr)]

lemma one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  exact Real.one_lt_exp_iff.mpr zero_lt_one

lemma magnitudeTail_pos (r : ℝ) : 0 < magnitudeTail r := by
  rw [magnitudeTail_eq_inverse]
  have hr : 1 < max r (Real.exp 1) := one_lt_exp_one.trans_le (le_max_right _ _)
  exact one_div_pos.mpr (mul_pos (lt_trans zero_lt_one hr) (Real.log_pos hr))

lemma magnitudeTail_antitone : Antitone magnitudeTail := by
  intro r s hrs
  rw [magnitudeTail_eq_inverse, magnitudeTail_eq_inverse]
  have hpos : 0 < max r (Real.exp 1) :=
    (Real.exp_pos 1).trans_le (le_max_right _ _)
  have hlog : 0 < Real.log (max r (Real.exp 1)) :=
    Real.log_pos (one_lt_exp_one.trans_le (le_max_right _ _))
  have hmax : max r (Real.exp 1) ≤ max s (Real.exp 1) := max_le_max hrs le_rfl
  exact one_div_le_one_div_of_le (mul_pos hpos hlog)
    (mul_le_mul hmax (Real.log_le_log hpos hmax) hlog.le (hpos.le.trans hmax))

lemma continuous_magnitudeTail : Continuous magnitudeTail := by
  change Continuous (fun r : ℝ => magnitudeTail r)
  simp_rw [magnitudeTail_eq_inverse]
  have hmax : Continuous (fun r : ℝ => max r (Real.exp 1)) :=
    continuous_id.max continuous_const
  apply continuous_const.div (hmax.mul ?_) ?_
  · exact hmax.log (fun r => ne_of_gt ((Real.exp_pos 1).trans_le (le_max_right _ _)))
  · intro r
    exact mul_ne_zero (ne_of_gt ((Real.exp_pos 1).trans_le (le_max_right _ _)))
      (ne_of_gt (Real.log_pos (one_lt_exp_one.trans_le (le_max_right _ _))))

lemma magnitudeTail_at_exp_one : magnitudeTail (Real.exp 1) = (Real.exp 1)⁻¹ := by
  simp [magnitudeTail, Real.log_exp]

lemma magnitudeTail_at_zero : magnitudeTail 0 = (Real.exp 1)⁻¹ := by
  simp [magnitudeTail, Real.exp_pos]

lemma magnitudeTail_le_one (r : ℝ) : magnitudeTail r ≤ 1 := by
  rw [magnitudeTail_eq_inverse]
  have hm : 1 ≤ max r (Real.exp 1) := one_lt_exp_one.le.trans (le_max_right _ _)
  have hl : 1 ≤ Real.log (max r (Real.exp 1)) := by
    simpa using Real.log_le_log (Real.exp_pos 1) (le_max_right r (Real.exp 1))
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
    (one_le_mul_of_one_le_of_one_le hm hl)).trans_eq (by norm_num)

lemma cosine_defect_bounds (u : ℝ) :
    0 ≤ 1 - Real.cos u ∧ 1 - Real.cos u ≤ u ^ 2 / 2 ∧
      1 - Real.cos u ≤ 2 := by
  exact ⟨sub_nonneg.mpr (Real.cos_le_one u),
    by linarith [Real.one_sub_sq_div_two_le_cos (x := u)],
    by linarith [Real.neg_one_le_cos u]⟩

lemma tendsto_magnitudeTail : Tendsto magnitudeTail atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with r hr
  simp [magnitudeTail, not_lt.mpr hr, one_div]

lemma tendsto_mul_magnitudeTail :
    Tendsto (fun r : ℝ => r * magnitudeTail r) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with r hr
  have hr0 : r ≠ 0 := ne_of_gt ((Real.exp_pos 1).trans_le hr)
  simp [magnitudeTail, not_lt.mpr hr, one_div, hr0, mul_comm]

lemma magnitudeCDF_is_distributionFunction :
    ProbabilityFoundations.Ch01.IsRealDistributionFunction magnitudeCDF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s hrs
    by_cases hs : s < 0
    · have hr : r < 0 := lt_of_le_of_lt hrs hs
      simp [magnitudeCDF, hr, hs]
    · by_cases hr : r < 0
      · simpa [magnitudeCDF, hr, hs] using sub_nonneg.mpr (magnitudeTail_le_one s)
      · simpa [magnitudeCDF, hr, hs] using sub_le_sub_left (magnitudeTail_antitone hrs) 1
  · intro r
    by_cases hr : r < 0
    · have heq : magnitudeCDF =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [gt_mem_nhds hr] with s hs
        simp [magnitudeCDF, hs]
      exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt
    · have heq : magnitudeCDF =ᶠ[𝓝[≥] r] fun s => 1 - magnitudeTail s := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs0 : 0 ≤ s := (le_of_not_gt hr).trans hs
        simp [magnitudeCDF, not_lt.mpr hs0]
      exact ((continuous_const.sub continuous_magnitudeTail).continuousWithinAt).congr_of_eventuallyEq
        heq (by simp [magnitudeCDF, hr])
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with r hr
    simp [magnitudeCDF, hr]
  · have h : Tendsto (fun r : ℝ => 1 - magnitudeTail r) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub tendsto_magnitudeTail
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp [magnitudeCDF, not_lt.mpr hr]

/-- Construct the exact magnitude law by its right-continuous CDF. -/
theorem exists_magnitude_law :
    Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment.magnitudeLawType := by
  let hF := magnitudeCDF_is_distributionFunction
  let F : StieltjesFunction ℝ := ⟨magnitudeCDF, hF.1, hF.2.1⟩
  have hbot : Tendsto F atBot (𝓝 0) := hF.2.2.1
  have htop : Tendsto F atTop (𝓝 1) := hF.2.2.2
  have hleft : Function.leftLim F 0 = 0 := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp [F, magnitudeCDF, show r < 0 from hr]
  refine ⟨F.measure, F.isProbabilityMeasure hbot htop, ?_, ?_, ?_⟩
  · rw [F.measure_Iio hbot, hleft]
    simp
  · intro r hr
    rw [F.measure_Ioi htop]
    simp [F, magnitudeCDF, not_lt.mpr hr]
  · rw [F.measure_singleton, hleft]
    simp [F, magnitudeCDF, magnitudeTail_at_zero]

lemma integrable_characteristic_kernel (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Eventually.of_forall (fun x => by rw [Complex.norm_exp_ofReal_mul_I])

lemma characteristic_real_part (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x, Real.cos (t * x) ∂μ := by
  rw [charFun_apply_real]
  simp_rw [← Complex.ofReal_mul]
  have h := integral_re (integrable_characteristic_kernel μ t)
  simpa only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] using h.symm

lemma integrable_cosine (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Eventually.of_forall (fun x => Real.abs_cos_le_one _)

lemma integrable_truncated_second (μ : Measure ℝ) [IsFiniteMeasure μ]
    (R : ℝ) (_hR : 0 ≤ R) :
    IntegrableOn (fun x : ℝ => |x| ^ 2) {x : ℝ | |x| ≤ R} μ := by
  apply (integrable_const (R ^ 2 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (by measurability : MeasurableSet {x : ℝ | |x| ≤ R})] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (abs_nonneg x) hx 2

/-- The displayed estimate actually holds for the real part of every
probability characteristic function, without a symmetry assumption. -/
theorem characteristic_truncation_estimate :
    Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment.truncationEstimateType := by
  intro μ _ t ht
  let h := |t|
  have hh : 0 < h := ht
  let A := {x : ℝ | |x| ≤ 1 / h}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hc : Aᶜ = {x : ℝ | 1 / h < |x|} := by ext x; simp [A]
  have hd : Integrable (fun x : ℝ => 1 - Real.cos (t * x)) μ :=
    (integrable_const 1).sub (integrable_cosine μ t)
  have heq : 1 - (charFun μ t).re = ∫ x, 1 - Real.cos (t * x) ∂μ := by
    rw [integral_sub (integrable_const 1) (integrable_cosine μ t), characteristic_real_part]
    simp
  have hn : 0 ≤ 1 - (charFun μ t).re := by
    rw [heq]
    exact integral_nonneg (fun x => (cosine_defect_bounds (t * x)).1)
  have hlow : (∫ x in A, 1 - Real.cos (t * x) ∂μ) ≤
      (h ^ 2 / 2) * truncatedSecondMoment μ (1 / h) := by
    rw [truncatedSecondMoment, ← integral_const_mul]
    apply setIntegral_mono_on hd.integrableOn
      ((integrable_truncated_second μ (1 / h) (by positivity)).const_mul _) hA
    intro x _
    calc
      1 - Real.cos (t * x) ≤ (t * x) ^ 2 / 2 := (cosine_defect_bounds _).2.1
      _ = h ^ 2 / 2 * |x| ^ 2 := by dsimp [h]; rw [sq_abs, sq_abs]; ring
  have hhigh : (∫ x in Aᶜ, 1 - Real.cos (t * x) ∂μ) ≤
      2 * (μ {x : ℝ | 1 / h < |x|}).toReal := by
    calc
      _ ≤ ∫ _ in Aᶜ, (2 : ℝ) ∂μ :=
        setIntegral_mono_on hd.integrableOn (integrable_const 2) hA.compl
          (fun x _ => (cosine_defect_bounds _).2.2)
      _ = _ := by simp [hc, Measure.real, mul_comm]
  have hu : 1 - (charFun μ t).re ≤
      h ^ 2 / 2 * truncatedSecondMoment μ (1 / h) +
        2 * (μ {x : ℝ | 1 / h < |x|}).toReal := by
    rw [heq, ← integral_add_compl hA hd]
    exact add_le_add hlow hhigh
  refine ⟨div_nonneg hn hh.le, ?_⟩
  calc
    (1 - (charFun μ t).re) / h ≤
        (h ^ 2 / 2 * truncatedSecondMoment μ (1 / h) +
          2 * (μ {x : ℝ | 1 / h < |x|}).toReal) / h := div_le_div_of_nonneg_right hu hh.le
    _ = truncationBound μ h := by unfold truncationBound; field_simp

instance fairSignLaw_isProbabilityMeasure : IsProbabilityMeasure fairSignLaw := by
  constructor
  norm_num [fairSignLaw]
  simpa only [one_div] using ENNReal.add_halves 1

lemma fairSignLaw_neg_one : fairSignLaw {-1} = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [fairSignLaw]

lemma fairSignLaw_one : fairSignLaw {1} = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [fairSignLaw]

lemma signedLaw_eq_mixture (ν : Measure ℝ) [SFinite ν] :
    signedLaw ν = (2 : ℝ≥0∞)⁻¹ • Measure.map (fun x : ℝ => -x) ν +
      (2 : ℝ≥0∞)⁻¹ • ν := by
  unfold signedLaw fairSignLaw
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left]
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

instance signedLaw_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (signedLaw ν) := by
  unfold signedLaw
  infer_instance

lemma signedLaw_symmetric (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure.map (fun x : ℝ => -x) (signedLaw ν) = signedLaw ν := by
  rw [signedLaw_eq_mixture, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, neg_neg, Measure.map_id']
  rw [add_comm]

lemma signedLaw_magnitude (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Iio 0) = 0) :
    Measure.map (fun x : ℝ => |x|) (signedLaw ν) = ν := by
  have hn : ∀ᵐ x ∂ν, 0 ≤ x := by
    rw [ae_iff]
    simpa only [not_le, Iio] using hν
  have habs : Measure.map (fun x : ℝ => |x|) ν = ν := by
    calc
      _ = Measure.map id ν := by
        apply Measure.map_congr
        filter_upwards [hn] with x hx
        exact abs_of_nonneg hx
      _ = ν := Measure.map_id
  rw [signedLaw_eq_mixture, Measure.map_add _ _ (by fun_prop),
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, abs_neg]
  rw [habs, ← add_smul]
  have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
    simpa only [one_div] using ENNReal.add_halves 1
  rw [hhalf, one_smul]

lemma symmetric_characteristic_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.map (fun x : ℝ => -x) μ = μ) (t : ℝ) :
    (charFun μ t).im = 0 := by
  have heq := charFun_map_mul (μ := μ) (-1) t
  simp only [neg_one_mul] at heq
  rw [hμ, charFun_neg] at heq
  have him := congrArg Complex.im heq
  simp only [Complex.conj_im] at him
  linarith

/-- The pointwise estimate plus decay of its right side forces derivative zero.
This uses real-valuedness from symmetry, not existence of a first moment. -/
theorem hasDerivAt_zero_of_truncationBound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hreal : ∀ t, (charFun μ t).im = 0)
    (hbound : Tendsto (truncationBound μ) (𝓝[>] 0) (𝓝 0)) :
    HasDerivAt (charFun μ) 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, smul_zero]
  nth_rw 1 [← nhdsNE_sup_pure (0 : ℝ)]
  rw [tendsto_sup]
  constructor
  · have htabs : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using abs_pos.mpr (show t ≠ 0 from ht)
    apply squeeze_zero' (Eventually.of_forall (fun t => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _))) ?_ (hbound.comp htabs)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < |t| := abs_pos.mpr ht
    have he := characteristic_truncation_estimate μ t ht0
    have hn : (charFun μ t).re ≤ 1 := by
      have hc := norm_charFun_le_one (μ := μ) t
      exact (Complex.re_le_norm _).trans hc
    have hnorm : ‖charFun μ t - charFun μ 0‖ = 1 - (charFun μ t).re := by
      have hz : charFun μ 0 = 1 := by simp
      rw [hz, ← Complex.abs_re_eq_norm.mpr (by simp [hreal])]
      simp only [Complex.sub_re, Complex.one_re]
      rw [abs_of_nonpos (sub_nonpos.mpr hn)]
      ring
    simpa only [Function.comp_apply, hnorm, Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using he.2
  · simpa using tendsto_pure_nhds
      (fun t : ℝ => ‖t‖⁻¹ * ‖charFun μ t - charFun μ 0‖) 0

/-- The logarithmic tail is not integrable, by substituting `u = log r`
and reducing to the divergent integral of `1/u`. -/
lemma logarithmic_tail_integral_infinite :
    (∫⁻ r : ℝ in Ioi (Real.exp 1), ENNReal.ofReal (1 / (r * Real.log r))) = ∞ := by
  have hnot : ¬ IntegrableOn (fun r : ℝ => 1 / (r * Real.log r)) (Ioi (Real.exp 1)) := by
    intro hi
    have hi' : IntegrableOn (fun r : ℝ => r⁻¹ • (Real.log r)⁻¹) (Ioi (Real.exp 1)) := by
      simpa [one_div, mul_inv, smul_eq_mul, mul_comm] using hi
    have hinv := (integrableOn_comp_log_Ioi (fun u : ℝ => u⁻¹) (Real.exp_pos 1)).mp hi'
    exact not_integrableOn_Ioi_inv hinv
  by_contra hfinite
  apply hnot
  refine ⟨(measurable_const.div (measurable_id.mul Real.measurable_log)).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal ?_).mpr (lt_top_iff_ne_top.mpr hfinite)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr1 : 1 < r := one_lt_exp_one.trans hr
  exact (one_div_pos.mpr (mul_pos (zero_lt_one.trans hr1) (Real.log_pos hr1))).le

/-- The exact absolute tail forces an infinite first absolute moment. -/
theorem absolute_moment_infinite (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ r : ℝ, Real.exp 1 ≤ r →
      μ {x : ℝ | r < |x|} = ENNReal.ofReal (1 / (r * Real.log r))) :
    (∫⁻ x : ℝ, ENNReal.ofReal |x| ∂μ) = ∞ := by
  have hmoment := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (f := fun x : ℝ => |x|) (Eventually.of_forall abs_nonneg)
    (by fun_prop) (show (0 : ℝ) < 1 by norm_num)
  simp only [Real.rpow_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, one_mul, mul_one] at hmoment
  apply top_unique
  calc
    ∞ = ∫⁻ r : ℝ in Ioi (Real.exp 1), ENNReal.ofReal (1 / (r * Real.log r)) :=
      logarithmic_tail_integral_infinite.symm
    _ = ∫⁻ r : ℝ in Ioi (Real.exp 1), μ {x : ℝ | r < |x|} := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact (htail r hr.le).symm
    _ ≤ ∫⁻ r : ℝ in Ioi 0, μ {x : ℝ | r < |x|} :=
      lintegral_mono_set (Ioi_subset_Ioi (Real.exp_pos 1).le)
    _ = _ := hmoment.symm

lemma weighted_magnitudeTail_le_one (r : ℝ) (_hr : 0 ≤ r) :
    r * magnitudeTail r ≤ 1 := by
  by_cases hre : r < Real.exp 1
  · rw [magnitudeTail, ite_eq_left hre]
    exact (mul_le_mul_of_nonneg_right hre.le (inv_nonneg.mpr (Real.exp_pos 1).le)).trans_eq
      (mul_inv_cancel₀ (ne_of_gt (Real.exp_pos 1)))
  · have hre' : Real.exp 1 ≤ r := le_of_not_gt hre
    have hr0 : r ≠ 0 := ne_of_gt ((Real.exp_pos 1).trans_le hre')
    have hlog : 1 ≤ Real.log r := by simpa using Real.log_le_log (Real.exp_pos 1) hre'
    have heq : r * magnitudeTail r = (Real.log r)⁻¹ := by
      simp [magnitudeTail, hre, one_div, hr0, mul_comm]
    rw [heq]
    exact inv_le_one_of_one_le₀ hlog

/-- Continuous Cesàro convergence, proved here by rescaling to `(0,1]`
and dominated convergence with bound one. -/
lemma tendsto_weighted_tail_average :
    Tendsto (fun R : ℝ => (∫ r in (0 : ℝ)..R, r * magnitudeTail r) / R)
      atTop (𝓝 0) := by
  have hcont : Continuous (fun r : ℝ => r * magnitudeTail r) :=
    continuous_id.mul continuous_magnitudeTail
  have hdct : Tendsto (fun R : ℝ => ∫ u in Ioc (0 : ℝ) 1,
      (R * u) * magnitudeTail (R * u)) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (l := atTop)
      (F := fun R u : ℝ => (R * u) * magnitudeTail (R * u))
      (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1) ?_
    · simpa using h
    · exact Eventually.of_forall (fun R => (hcont.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hRu : 0 ≤ R * u := mul_nonneg hR hu.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hRu (magnitudeTail_pos _).le)]
      exact weighted_magnitudeTail_le_one _ hRu
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact tendsto_mul_magnitudeTail.comp ((tendsto_mul_const_atTop_of_pos hu.1).mpr tendsto_id)
  apply hdct.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun r : ℝ => r * magnitudeTail r) hR.ne']
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma truncatedSecondMoment_le_tail_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ r : ℝ, 0 ≤ r → μ {x : ℝ | r < |x|} = ENNReal.ofReal (magnitudeTail r))
    (R : ℝ) (hR : 0 < R) :
    truncatedSecondMoment μ R ≤ 2 * ∫ r in (0 : ℝ)..R, r * magnitudeTail r := by
  let Y : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |x|
  have hY : Measurable Y := by fun_prop
  have hcap := ProbabilityFoundations.Ch01.capped_moment μ Y hY 2 R (by norm_num) hR
  have hqi : IntegrableOn (fun r : ℝ => r * magnitudeTail r) (Ioo 0 R) :=
    (continuous_id.mul continuous_magnitudeTail).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hqpos : ∀ᵐ r ∂(volume.restrict (Ioo 0 R)), 0 ≤ r * magnitudeTail r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg hr.1.le (magnitudeTail_pos r).le
  have hcap' : (∫⁻ x, min (Y x) (ENNReal.ofReal R) ^ (2 : ℝ) ∂μ) =
      ENNReal.ofReal (2 * ∫ r in Ioo (0 : ℝ) R, r * magnitudeTail r) := by
    rw [hcap, ENNReal.ofReal_mul (by norm_num), ofReal_integral_eq_lintegral_ofReal hqi hqpos]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have he : {x : ℝ | ENNReal.ofReal r < Y x} = {x : ℝ | r < |x|} := by
      ext x
      simp only [Y, mem_ofPred_eq, ENNReal.ofReal_lt_ofReal_iff']
      exact and_iff_left_of_imp (fun h => hr.1.trans h)
    dsimp only
    rw [he, htail r hr.1.le]
    norm_num [ENNReal.ofReal_mul hr.1.le]
  have hfi := integrable_truncated_second μ R hR.le
  have htpos : ∀ᵐ x ∂(μ.restrict {x : ℝ | |x| ≤ R}), 0 ≤ |x| ^ 2 :=
    Eventually.of_forall (fun x => sq_nonneg _)
  have hlower : ENNReal.ofReal (truncatedSecondMoment μ R) ≤
      ENNReal.ofReal (2 * ∫ r in Ioo (0 : ℝ) R, r * magnitudeTail r) := by
    rw [truncatedSecondMoment, ofReal_integral_eq_lintegral_ofReal hfi htpos, ← hcap',
      ← lintegral_indicator (by measurability : MeasurableSet {x : ℝ | |x| ≤ R})]
    apply lintegral_mono
    intro x
    by_cases hx : |x| ≤ R
    · dsimp only
      rw [Set.indicator_of_mem (show x ∈ {x : ℝ | |x| ≤ R} from hx),
        min_eq_left (show Y x ≤ ENNReal.ofReal R from ENNReal.ofReal_le_ofReal hx)]
      change ENNReal.ofReal (|x| ^ 2) ≤ ENNReal.ofReal |x| ^ (2 : ℝ)
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg x)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | |x| ≤ R} from hx)]
      exact bot_le
  have hn : 0 ≤ 2 * ∫ r in Ioo (0 : ℝ) R, r * magnitudeTail r :=
    mul_nonneg (by norm_num) (integral_nonneg_of_ae hqpos)
  have hr := (ENNReal.ofReal_le_ofReal_iff hn).mp hlower
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR.le] at hr
  exact hr

lemma tendsto_normalized_truncatedSecondMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ r : ℝ, 0 ≤ r → μ {x : ℝ | r < |x|} = ENNReal.ofReal (magnitudeTail r)) :
    Tendsto (fun R : ℝ => truncatedSecondMoment μ R / R) atTop (𝓝 0) := by
  have htop : Tendsto (fun R : ℝ => 2 * ((∫ r in (0 : ℝ)..R, r * magnitudeTail r) / R))
      atTop (𝓝 0) := by simpa using tendsto_weighted_tail_average.const_mul 2
  apply squeeze_zero' ?_ ?_ htop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact div_nonneg (integral_nonneg (fun x => sq_nonneg _)) hR.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    convert div_le_div_of_nonneg_right (truncatedSecondMoment_le_tail_integral μ htail R hR) hR.le using 1
    ring

lemma tendsto_truncationBound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (htail : ∀ r : ℝ, 0 ≤ r → μ {x : ℝ | r < |x|} = ENNReal.ofReal (magnitudeTail r)) :
    Tendsto (truncationBound μ) (𝓝[>] 0) (𝓝 0) := by
  have hinv : Tendsto (fun h : ℝ => 1 / h) (𝓝[>] 0) atTop := by
    simpa only [one_div] using (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop)
  have hlim := ((tendsto_normalized_truncatedSecondMoment μ htail).comp hinv).const_mul (1 / 2 : ℝ)
  have htailLim := (tendsto_mul_magnitudeTail.comp hinv).const_mul 2
  have hsum : Tendsto (fun h : ℝ =>
      (1 / 2 : ℝ) * (truncatedSecondMoment μ (1 / h) / (1 / h)) +
        2 * ((1 / h) * magnitudeTail (1 / h))) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim.add htailLim
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  rw [truncationBound, htail (1 / h) (by positivity), ENNReal.toReal_ofReal (magnitudeTail_pos _).le]
  field_simp

/-- The complete counterexample, with its exact magnitude tail, atom,
independent fair sign, infinite moment, quantitative estimate, and derivative. -/
theorem differentiable_without_first_moment :
    Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment.exampleType := by
  obtain ⟨ν, hprob, hsupp, htail, hatom⟩ := exists_magnitude_law
  let : IsProbabilityMeasure ν := hprob
  have habs := signedLaw_magnitude ν hsupp
  have hsymm := signedLaw_symmetric ν
  have hμtail : ∀ r : ℝ, 0 ≤ r →
      signedLaw ν {x : ℝ | r < |x|} = ENNReal.ofReal (magnitudeTail r) := by
    intro r hr
    have hh := congrArg (fun ρ : Measure ℝ => ρ (Ioi r)) habs
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at hh
    exact hh.trans (htail r hr)
  have hreal : ∀ t, (charFun (signedLaw ν) t).im = 0 :=
    symmetric_characteristic_real _ hsymm
  have hlimit := tendsto_truncationBound (signedLaw ν) hμtail
  refine ⟨ν, hprob, hsupp, htail, hatom, inferInstance, fairSignLaw_neg_one,
    fairSignLaw_one, ?_, ?_, ?_, inferInstance, habs, hsymm, ?_, hreal,
    characteristic_truncation_estimate (signedLaw ν), hlimit,
    hasDerivAt_zero_of_truncationBound (signedLaw ν) hreal hlimit⟩
  · exact ProbabilityTheory.indepFun_prod measurable_id measurable_id
  · exact measurePreserving_fst.map_eq
  · exact measurePreserving_snd.map_eq
  · apply absolute_moment_infinite
    intro r hr
    rw [hμtail r ((Real.exp_pos 1).le.trans hr)]
    simp [magnitudeTail, not_lt.mpr hr]

end ProbabilityFoundations.Ch07.InfiniteMomentExample
