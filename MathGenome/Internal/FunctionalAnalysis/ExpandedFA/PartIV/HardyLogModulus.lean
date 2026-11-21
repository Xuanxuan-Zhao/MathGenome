import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLogModulus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PositiveHarmonic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Boundary logarithmic integrability, Poisson majorization, and the Hardy
exponential factor from `fa2:p4:hardy-factorization`. The proof first constructs
exponentials of boundary logarithms truncated from below. Bounded analytic
division gives the cutoff majorization without assuming boundary nonvanishing;
monotone convergence then proves nonvanishing and logarithmic integrability. -/

noncomputable section
open MeasureTheory Filter Set Metric Complex
open scoped Real Topology ENNReal

namespace ExpandedFA.PartIV.HardyLogModulus
open HardyDiskSpec

lemma norm_circlePoint (t : BoundaryCircle) : ‖circlePoint t‖ = 1 :=
  HardyDisk.norm_fourier_point 1 t

lemma continuous_circlePoint : Continuous circlePoint :=
  (fourier (T := 2 * π) 1).continuous

lemma circlePoint_sub_ne_zero {z : ℂ} (hz : z ∈ disk) (t : BoundaryCircle) :
    circlePoint t - z ≠ 0 := by
  intro he
  have he' : z = circlePoint t := (sub_eq_zero.mp he).symm
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  rw [he', norm_circlePoint] at hz'
  exact lt_irrefl _ hz'

lemma continuous_kernel {z : ℂ} (hz : z ∈ disk) :
    Continuous (fun t => (circlePoint t + z) / (circlePoint t - z)) :=
  (continuous_circlePoint.add continuous_const).div
    (continuous_circlePoint.sub continuous_const) (circlePoint_sub_ne_zero hz)

lemma integrable_kernel_mul {h : BoundaryCircle → ℝ} (hh : Integrable h circleMeasure)
    {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun t => ((circlePoint t + z) / (circlePoint t - z)) *
      (h t : ℂ)) circleMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_kernel hz).norm).bddAbove
  exact hh.ofReal.bdd_mul (continuous_kernel hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => hC ⟨t, rfl⟩)

lemma hasDerivAt_kernel {z : ℂ} (hz : z ∈ disk) (t : BoundaryCircle) :
    HasDerivAt (fun w => (circlePoint t + w) / (circlePoint t - w))
      (2 * circlePoint t / (circlePoint t - z) ^ 2) z := by
  have hd := ((hasDerivAt_id' z).const_add (circlePoint t)).div
    ((hasDerivAt_id' z).const_sub (circlePoint t)) (circlePoint_sub_ne_zero hz t)
  convert hd using 1
  simp [sub_sub, ← two_mul]

theorem integral_holomorphic : Spec.IntegralHolomorphic := by
  intro h hh w hw
  let r : ℝ := (1 + ‖w‖) / 2
  have hw' : ‖w‖ < 1 := by simpa [disk] using hw
  have hwr : ‖w‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hmem : ball (0 : ℂ) r ∈ 𝓝 w := isOpen_ball.mem_nhds (by simpa using hwr)
  have hsub : ball (0 : ℂ) r ⊆ disk := by
    intro x hx
    simpa [disk] using lt_trans (by simpa using hx : ‖x‖ < r) hr
  have hdist (x : ℂ) (hx : x ∈ ball (0 : ℂ) r) (t : BoundaryCircle) :
      1 - r ≤ ‖circlePoint t - x‖ := by
    have hx' : ‖x‖ < r := by simpa using hx
    have hn := norm_sub_norm_le (circlePoint t) x
    rw [norm_circlePoint] at hn
    linarith
  have hd : 0 < 1 - r := sub_pos.mpr hr
  have hmeas : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (fun t => ((circlePoint t + x) / (circlePoint t - x)) *
        (h t : ℂ)) circleMeasure := by
    filter_upwards [hmem] with x hx
    exact (integrable_kernel_mul hh (hsub hx)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t =>
      (2 * circlePoint t / (circlePoint t - w) ^ 2) * (h t : ℂ)) circleMeasure := by
    have hc : Continuous (fun t => 2 * circlePoint t / (circlePoint t - w) ^ 2) :=
      (continuous_const.mul continuous_circlePoint).div
        ((continuous_circlePoint.sub continuous_const).pow 2)
        (fun t => pow_ne_zero _ (circlePoint_sub_ne_zero hw t))
    exact hc.aestronglyMeasurable.mul hh.ofReal.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂circleMeasure, ∀ x ∈ ball (0 : ℂ) r,
      ‖(2 * circlePoint t / (circlePoint t - x) ^ 2) * (h t : ℂ)‖ ≤
        (2 / (1 - r) ^ 2) * ‖h t‖ := by
    filter_upwards with t x hx
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [norm_div, norm_mul, norm_pow, norm_circlePoint, norm_ofNat, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hd)
      (by nlinarith [hdist x hx t, norm_nonneg (circlePoint t - x)])
  have hdiff : ∀ᵐ t ∂circleMeasure, ∀ x ∈ ball (0 : ℂ) r,
      HasDerivAt (fun z => ((circlePoint t + z) / (circlePoint t - z)) * (h t : ℂ))
        ((2 * circlePoint t / (circlePoint t - x) ^ 2) * (h t : ℂ)) x := by
    filter_upwards with t x hx
    exact (hasDerivAt_kernel (hsub hx) t).mul_const (h t : ℂ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => ((circlePoint t + x) / (circlePoint t - x)) * (h t : ℂ))
    (F' := fun x t => (2 * circlePoint t / (circlePoint t - x) ^ 2) * (h t : ℂ))
    (bound := fun t => (2 / (1 - r) ^ 2) * ‖h t‖) hmem hmeas
    (integrable_kernel_mul hh hw) hmeas' hbound (hh.norm.const_mul _) hdiff).2.differentiableAt.differentiableWithinAt

theorem exponential_holomorphic : Spec.ExponentialHolomorphic := by
  intro h hh c
  exact (integral_holomorphic h hh).cexp.const_mul c

theorem exponential_nonzero : Spec.ExponentialNonzero := by
  intro h c hc z
  exact mul_ne_zero hc (Complex.exp_ne_zero _)

lemma kernel_re (z : ℂ) (t : BoundaryCircle) :
    (((circlePoint t + z) / (circlePoint t - z)) : ℂ).re =
      (1 - ‖z‖ ^ 2) / ‖circlePoint t - z‖ ^ 2 := by
  have hp := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z))
    (circlePoint t)
  simpa [poissonKernel, herglotzRieszKernel, norm_circlePoint] using hp.symm

lemma logarithmicIntegral_re {h : BoundaryCircle → ℝ} (hh : Integrable h circleMeasure)
    {z : ℂ} (hz : z ∈ disk) :
    (logarithmicIntegral h z).re = poissonLog h z := by
  change Complex.reCLM (∫ t, ((circlePoint t + z) / (circlePoint t - z)) *
    (h t : ℂ) ∂circleMeasure) = _
  rw [← Complex.reCLM.integral_comp_comm (integrable_kernel_mul hh hz)]
  simp only [Complex.reCLM_apply, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    kernel_re, poissonLog]

theorem exponential_norm : Spec.ExponentialNorm := by
  intro h hh c hc z hz
  simp only [exponentialFactor, norm_mul, hc, one_mul, Complex.norm_exp,
    logarithmicIntegral_re hh hz]

theorem positive_log_integrable : Spec.PositiveLogIntegrable := by
  intro f
  have hb : Integrable (boundary f : BoundaryCircle → ℂ) circleMeasure :=
    (Lp.memLp (boundary f)).integrable (by norm_num)
  have hm : AEStronglyMeasurable (boundaryLog f) circleMeasure :=
    hb.aestronglyMeasurable.norm.aemeasurable.log.aestronglyMeasurable
  refine hb.norm.mono' (hm.aemeasurable.max aemeasurable_const).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (Real.log_le_self (norm_nonneg _)) (norm_nonneg _)

lemma abs_log_sub_log_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have haux (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
      Real.log x - Real.log y ≤ |x - y| := by
    have hx' : 0 < x := by linarith
    have hy' : 0 < y := by linarith
    calc
      Real.log x - Real.log y = Real.log (x / y) :=
        (Real.log_div hx'.ne' hy'.ne').symm
      _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx' hy')
      _ = (x - y) / y := by rw [sub_div, div_self hy'.ne']
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy'.le
      _ ≤ |x - y| := div_le_self (abs_nonneg _) hy
  refine abs_le.mpr ⟨?_, haux a b ha hb⟩
  have hh := haux b a hb ha
  rw [abs_sub_comm b a] at hh
  linarith

def positiveLog (z : ℂ) : ℝ := Real.log (max ‖z‖ 1)

lemma positiveLog_eq (z : ℂ) : positiveLog z = max (Real.log ‖z‖) 0 := by
  by_cases h : ‖z‖ ≤ 1
  · simp [positiveLog, max_eq_right h,
      max_eq_right (Real.log_nonpos (norm_nonneg _) h)]
  · simp [positiveLog, max_eq_left (le_of_not_ge h),
      max_eq_left (Real.log_nonneg (le_of_not_ge h))]

lemma positiveLog_zero : positiveLog 0 = 0 := by simp [positiveLog]

lemma positiveLog_lipschitz : LipschitzWith 1 positiveLog := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hc : LipschitzWith 1 (fun z : ℂ => max ‖z‖ 1) :=
    lipschitzWith_one_norm.max_const 1
  calc
    dist (positiveLog z) (positiveLog w) ≤ dist (max ‖z‖ 1) (max ‖w‖ 1) := by
      simpa only [positiveLog, Real.dist_eq] using
        abs_log_sub_log_le (le_max_right ‖z‖ 1) (le_max_right ‖w‖ 1)
    _ ≤ (1 : ℝ) * dist z w := by simpa using hc.dist_le_mul z w

theorem positive_log_radial_convergence : Spec.PositiveLogRadialConvergence := by
  intro f
  obtain ⟨g, hg, ht⟩ := HardyDisk.radial_convergence f
  let L : BoundaryL2 → Lp ℝ 2 circleMeasure :=
    positiveLog_lipschitz.compLp positiveLog_zero
  refine ⟨fun r => L (g r), L (boundary f), ?_, ?_, ?_⟩
  · filter_upwards [positiveLog_lipschitz.coeFn_compLp positiveLog_zero
      (boundary f)] with t ht
    simpa [L, Function.comp_def, positiveLog_eq, boundaryLog] using ht
  · intro r hr0 hr1
    filter_upwards [positiveLog_lipschitz.coeFn_compLp positiveLog_zero (g r),
      hg r hr0 hr1] with t ht hgt
    simpa [L, Function.comp_def, hgt, positiveLog_eq, circlePoint] using ht
  · exact (positiveLog_lipschitz.continuous_compLp positiveLog_zero).continuousAt.tendsto.comp ht

/-- The normalized Poisson density on the coefficient model's boundary circle. -/
def poissonWeight (z : ℂ) (t : BoundaryCircle) : ℝ :=
  (1 - ‖z‖ ^ 2) / ‖circlePoint t - z‖ ^ 2

lemma continuous_poissonWeight {z : ℂ} (hz : z ∈ disk) :
    Continuous (poissonWeight z) := by
  unfold poissonWeight
  exact continuous_const.div ((continuous_circlePoint.sub continuous_const).norm.pow 2)
    (fun t => pow_ne_zero _ (norm_ne_zero_iff.mpr (circlePoint_sub_ne_zero hz t)))

lemma poissonWeight_nonneg {z : ℂ} (hz : z ∈ disk) (t : BoundaryCircle) :
    0 ≤ poissonWeight z t := by
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  unfold poissonWeight
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

lemma integral_poissonWeight {z : ℂ} (hz : z ∈ disk) :
    ∫ t, poissonWeight z t ∂circleMeasure = 1 := by
  have hconst : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) disk :=
    ⟨differentiableOn_const _, continuousOn_const⟩
  have hp := hconst.circleAverage_poissonKernel_smul' hz
  rw [← HardyDisk.circle_integral_eq_average] at hp
  have hi : (∫ t, (poissonWeight z t : ℂ) ∂circleMeasure) = 1 := by
    simpa only [sub_zero, HardyDisk.norm_fourier_point, one_pow, Complex.real_smul, mul_one,
      circlePoint, poissonWeight] using hp
  apply Complex.ofReal_injective
  calc
    ((∫ t, poissonWeight z t ∂circleMeasure : ℝ) : ℂ) =
        ∫ t, (poissonWeight z t : ℂ) ∂circleMeasure :=
      (_root_.integral_complex_ofReal).symm
    _ = 1 := hi
    _ = ((1 : ℝ) : ℂ) := rfl

lemma integrable_poissonWeight_mul {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun t => poissonWeight z t * h t) circleMeasure := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_poissonWeight hz).norm).bddAbove
  exact hh.bdd_mul (continuous_poissonWeight hz).aestronglyMeasurable
    (Eventually.of_forall fun t => hC ⟨t, rfl⟩)

/-- Jensen's exponential inequality, proved by integrating its tangent line.
Only the displayed density and exponential are required to be integrable. -/
lemma exp_poissonLog_le {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure)
    (he : Integrable (fun t => Real.exp (h t)) circleMeasure)
    {z : ℂ} (hz : z ∈ disk) :
    Real.exp (poissonLog h z) ≤
      ∫ t, poissonWeight z t * Real.exp (h t) ∂circleMeasure := by
  let A := poissonLog h z
  have ht (t : BoundaryCircle) :
      poissonWeight z t * (Real.exp A * (1 + (h t - A))) ≤
        poissonWeight z t * Real.exp (h t) := by
    apply mul_le_mul_of_nonneg_left _ (poissonWeight_nonneg hz t)
    calc
      Real.exp A * (1 + (h t - A)) ≤ Real.exp A * Real.exp (h t - A) := by
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (h t - A)])
          (Real.exp_pos A).le
      _ = Real.exp (h t) := by rw [← Real.exp_add]; congr 1; ring
  have hleft : Integrable (fun t => poissonWeight z t *
      (Real.exp A * (1 + (h t - A)))) circleMeasure := by
    exact integrable_poissonWeight_mul
      (((integrable_const (1 : ℝ)).add (hh.sub (integrable_const A))).const_mul _) hz
  have hle := integral_mono hleft (integrable_poissonWeight_mul he hz) ht
  have hval : (∫ t, poissonWeight z t * (Real.exp A * (1 + (h t - A)))
      ∂circleMeasure) = Real.exp A := by
    have hP : Integrable (poissonWeight z) circleMeasure := by
      exact (continuous_poissonWeight hz).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPh := integrable_poissonWeight_mul hh hz
    calc
      _ = ∫ t, Real.exp A * (poissonWeight z t +
          (poissonWeight z t * h t - A * poissonWeight z t)) ∂circleMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = Real.exp A * ((∫ t, poissonWeight z t ∂circleMeasure) +
          ((∫ t, poissonWeight z t * h t ∂circleMeasure) -
            A * ∫ t, poissonWeight z t ∂circleMeasure)) := by
        rw [integral_const_mul]
        congr 1
        have hs := integral_add hP (hPh.sub (hP.const_mul A))
        have hd := integral_sub hPh (hP.const_mul A)
        simp only [Pi.sub_apply] at hs hd
        rw [hs, hd, integral_const_mul]
      _ = Real.exp A := by
        rw [integral_poissonWeight hz]
        change Real.exp A * (1 + (A - A * 1)) = Real.exp A
        ring
  rw [hval] at hle
  exact hle

lemma poissonWeight_radial_symm (r : ℝ) (t u : BoundaryCircle) :
    poissonWeight ((r : ℂ) * circlePoint t) u =
      poissonWeight ((r : ℂ) * circlePoint u) t := by
  unfold poissonWeight
  congr 1
  · simp only [norm_mul, norm_circlePoint, mul_one]
  · have he : Complex.normSq (circlePoint u - (r : ℂ) * circlePoint t) =
        Complex.normSq (circlePoint t - (r : ℂ) * circlePoint u) := by
      rw [Complex.normSq_sub, Complex.normSq_sub]
      simp only [map_mul, Complex.normSq_eq_norm_sq,
        norm_circlePoint, one_pow, mul_one, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simpa only [Complex.normSq_eq_norm_sq] using he

lemma continuous_radial_poissonWeight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun p : BoundaryCircle × BoundaryCircle =>
      poissonWeight ((r : ℂ) * circlePoint p.1) p.2) := by
  have hc1 : Continuous (fun p : BoundaryCircle × BoundaryCircle => circlePoint p.1) :=
    continuous_circlePoint.comp continuous_fst
  have hc2 : Continuous (fun p : BoundaryCircle × BoundaryCircle => circlePoint p.2) :=
    continuous_circlePoint.comp continuous_snd
  unfold poissonWeight
  exact (continuous_const.sub ((continuous_const.mul hc1).norm.pow 2)).div
    ((hc2.sub (continuous_const.mul hc1)).norm.pow 2)
    (fun p => pow_ne_zero _ (norm_ne_zero_iff.mpr (circlePoint_sub_ne_zero
      (HardyDisk.radial_point_mem_disk hr0 hr1 p.1) p.2)))

lemma integrable_radial_poissonWeight_mul {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun p : BoundaryCircle × BoundaryCircle =>
      poissonWeight ((r : ℂ) * circlePoint p.1) p.2 * h p.2)
      (circleMeasure.prod circleMeasure) := by
  have hc := continuous_radial_poissonWeight hr0 hr1
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  exact (hh.comp_snd circleMeasure).bdd_mul hc.aestronglyMeasurable
    (Eventually.of_forall fun p => hC ⟨p, rfl⟩)

/-- Averaging the Poisson extension on any concentric circle preserves mass. -/
lemma integral_radial_poissonLog {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t, poissonLog h ((r : ℂ) * circlePoint t) ∂circleMeasure) =
      ∫ t, h t ∂circleMeasure := by
  change (∫ t, ∫ u, poissonWeight ((r : ℂ) * circlePoint t) u * h u
    ∂circleMeasure ∂circleMeasure) = _
  rw [integral_integral_swap (integrable_radial_poissonWeight_mul hh hr0 hr1)]
  apply integral_congr_ae
  filter_upwards with u
  simp_rw [poissonWeight_radial_symm, integral_mul_const]
  have hz : (r : ℂ) * circlePoint u ∈ disk := HardyDisk.radial_point_mem_disk hr0 hr1 u
  rw [integral_poissonWeight hz, one_mul]

/-- The pointwise square bound used to construct the Hardy exponential. -/
lemma exponential_sq_le_poisson {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure)
    (he : Integrable (fun t => Real.exp (2 * h t)) circleMeasure)
    {c : ℂ} (hc : ‖c‖ = 1) {z : ℂ} (hz : z ∈ disk) :
    ‖exponentialFactor h c z‖ ^ 2 ≤
      poissonLog (fun t => Real.exp (2 * h t)) z := by
  rw [exponential_norm h hh c hc z hz, ← Real.exp_nat_mul]
  have hlin : poissonLog (fun t => 2 * h t) z = 2 * poissonLog h z := by
    unfold poissonLog
    simp_rw [mul_left_comm _ (2 : ℝ), integral_const_mul]
  have hj := exp_poissonLog_le (hh.const_mul 2) he hz
  change Real.exp (poissonLog (fun t => 2 * h t) z) ≤
    poissonLog (fun t => Real.exp (2 * h t)) z at hj
  rw [hlin] at hj
  exact hj

lemma boundaryL2_norm_sq (g : BoundaryL2) :
    ‖g‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 ∂circleMeasure := by
  have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) g
  rw [L2.inner_def] at hi
  simp_rw [inner_self_eq_norm_sq_to_K] at hi
  simp only [← RCLike.ofReal_pow] at hi
  rw [_root_.integral_ofReal] at hi
  exact_mod_cast hi.symm

/-- The exponential of an integrable boundary density with integrable squared
exponential is an actual element of the canonical coefficient Hardy space. -/
theorem exponential_hardy_membership {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure)
    (he : Integrable (fun t => Real.exp (2 * h t)) circleMeasure)
    {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ o : H2, Set.EqOn (eval o) (exponentialFactor h c) disk ∧
      ‖o‖ ≤ Real.sqrt (∫ t, Real.exp (2 * h t) ∂circleMeasure) := by
  have hF := exponential_holomorphic h hh c
  apply HardyDisk.hardy_of_circleBound hF (Real.sqrt_nonneg _)
  intro r hr0 hr1
  let g := HardyDisk.circleValuesLp (exponentialFactor h c) hF.continuousOn r hr0 hr1
  have hg : (g : BoundaryCircle → ℂ) =ᵐ[circleMeasure]
      fun t => exponentialFactor h c ((r : ℂ) * circlePoint t) :=
    HardyDisk.circleValuesLp_coe _ _ r hr0 hr1
  refine ⟨g, hg, Real.le_sqrt_of_sq_le ?_⟩
  rw [boundaryL2_norm_sq]
  have hi := (integrable_radial_poissonWeight_mul he hr0 hr1).integral_prod_left
  change Integrable (fun t => poissonLog (fun u => Real.exp (2 * h u))
    ((r : ℂ) * circlePoint t)) circleMeasure at hi
  have hgint := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp
    (Lp.memLp g)
  calc
    _ ≤ ∫ t, poissonLog (fun u => Real.exp (2 * h u))
        ((r : ℂ) * circlePoint t) ∂circleMeasure := by
      apply integral_mono_ae hgint hi
      filter_upwards [hg] with t ht
      rw [ht]
      exact exponential_sq_le_poisson hh he hc (HardyDisk.radial_point_mem_disk hr0 hr1 t)
    _ = _ := integral_radial_poissonLog he hr0 hr1

lemma exp_two_log_norm_ae (g : BoundaryL2)
    (hne : ∀ᵐ t ∂circleMeasure, g t ≠ 0) :
    (fun t => Real.exp (2 * Real.log ‖g t‖)) =ᵐ[circleMeasure]
      fun t => ‖g t‖ ^ 2 := by
  filter_upwards [hne] with t ht
  change Real.exp (((2 : ℕ) : ℝ) * Real.log ‖g t‖) = ‖g t‖ ^ 2
  rw [Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr ht)]

/-- Hardy membership for the displayed formula with arbitrary L² boundary data.
The boundary modulus assertion is a separate limit theorem. -/
theorem boundary_exponential_hardy (g : BoundaryL2)
    (hh : Integrable (fun t => Real.log ‖g t‖) circleMeasure)
    (hne : ∀ᵐ t ∂circleMeasure, g t ≠ 0) (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ o : H2,
      Set.EqOn (eval o) (exponentialFactor (fun t => Real.log ‖g t‖) c) disk ∧
      ‖o‖ ≤ ‖g‖ := by
  have hs : Integrable (fun t => ‖g t‖ ^ 2) circleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have he : Integrable (fun t => Real.exp (2 * Real.log ‖g t‖)) circleMeasure :=
    hs.congr (exp_two_log_norm_ae g hne).symm
  obtain ⟨o, ho, hn⟩ := exponential_hardy_membership hh he hc
  refine ⟨o, ho, ?_⟩
  rw [integral_congr_ae (exp_two_log_norm_ae g hne), ← boundaryL2_norm_sq,
    Real.sqrt_sq (norm_nonneg g)] at hn
  exact hn

/-- Transfer of continuous boundary data to the geometric-circle Poisson integral. -/
lemma poissonLog_eq_geometric (f : C(BoundaryCircle, ℝ)) {z : ℂ} (hz : z ∈ disk) :
    poissonLog f z = ∫ ζ : _root_.Circle,
      PositiveHarmonic.circlePoissonKernel z ζ *
        f ((AddCircle.homeomorphCircle (by positivity : 2 * π ≠ 0)).symm ζ)
      ∂PositiveHarmonic.circleHaar := by
  let e := AddCircle.homeomorphCircle (by positivity : 2 * π ≠ 0)
  have hz' : z ∈ PositiveHarmonic.unitDisk := by simpa [disk, PositiveHarmonic.unitDisk] using hz
  have hf : Continuous (fun ζ : _root_.Circle =>
      PositiveHarmonic.circlePoissonKernel z ζ * f (e.symm ζ)) :=
    (PositiveHarmonic.continuous_circlePoissonKernel hz').mul
      (f.continuous.comp e.symm.continuous)
  rw [PositiveHarmonic.circleHaar_eq_map, integral_map
    AddCircle.continuous_toCircle.measurable.aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with t
  have he : AddCircle.toCircle t = e t := (AddCircle.homeomorphCircle_apply _ t).symm
  change poissonWeight z t * f t =
    PositiveHarmonic.circlePoissonKernel z (AddCircle.toCircle t) *
      f (e.symm (AddCircle.toCircle t))
  rw [he, e.symm_apply_apply]
  congr 1
  simp only [poissonWeight, PositiveHarmonic.circlePoissonKernel, e,
    AddCircle.homeomorphCircle_apply, circlePoint, fourier_one]

lemma poissonLog_tendsto_continuous (f : C(BoundaryCircle, ℝ))
    {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) (t : BoundaryCircle) :
    Tendsto (fun n => poissonLog f ((r n : ℂ) * circlePoint t)) atTop (𝓝 (f t)) := by
  let e := AddCircle.homeomorphCircle (by positivity : 2 * π ≠ 0)
  let F : C(_root_.Circle, ℝ) := ⟨fun ζ => f (e.symm ζ), f.continuous.comp e.symm.continuous⟩
  have hr (n : ℕ) : |r n| < 1 := by rw [abs_of_nonneg (hr0 n)]; exact hr1 n
  have ht := PositiveHarmonic.poissonTest_tendsto hr hrlim F (e t)
  have hcp : ((e t : _root_.Circle) : ℂ) = circlePoint t := by
    simp only [e, AddCircle.homeomorphCircle_apply, circlePoint, fourier_one]
  simp only [F, ContinuousMap.coe_mk, e.symm_apply_apply] at ht
  simp only [hcp] at ht
  convert ht using 1
  funext n
  exact poissonLog_eq_geometric f (HardyDisk.radial_point_mem_disk (hr0 n) (hr1 n) t)

lemma norm_poissonLog_le {h : BoundaryCircle → ℝ} (_hh : Integrable h circleMeasure)
    {z : ℂ} (hz : z ∈ disk) :
    ‖poissonLog h z‖ ≤ poissonLog (fun t => ‖h t‖) z := by
  calc
    _ ≤ ∫ t, ‖poissonWeight z t * h t‖ ∂circleMeasure := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_mul, Real.norm_of_nonneg (poissonWeight_nonneg hz t)]
      rfl

lemma integrable_radial_poissonLog {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun t => poissonLog h ((r : ℂ) * circlePoint t)) circleMeasure :=
  (integrable_radial_poissonWeight_mul hh hr0 hr1).integral_prod_left

lemma integral_norm_radial_poissonLog_le {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t, ‖poissonLog h ((r : ℂ) * circlePoint t)‖ ∂circleMeasure) ≤
      ∫ t, ‖h t‖ ∂circleMeasure := by
  calc
    _ ≤ ∫ t, poissonLog (fun u => ‖h u‖) ((r : ℂ) * circlePoint t) ∂circleMeasure :=
      integral_mono (integrable_radial_poissonLog hh hr0 hr1).norm
        (integrable_radial_poissonLog hh.norm hr0 hr1)
        (fun t => norm_poissonLog_le hh (HardyDisk.radial_point_mem_disk hr0 hr1 t))
    _ = _ := integral_radial_poissonLog hh.norm hr0 hr1

lemma norm_poissonLog_continuous_le (f : C(BoundaryCircle, ℝ))
    {z : ℂ} (hz : z ∈ disk) : ‖poissonLog f z‖ ≤ ‖f‖ := by
  have hf : Integrable (f : BoundaryCircle → ℝ) circleMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ poissonLog (fun t => ‖f t‖) z := norm_poissonLog_le hf hz
    _ ≤ ∫ t, poissonWeight z t * ‖f‖ ∂circleMeasure := by
      apply integral_mono (integrable_poissonWeight_mul hf.norm hz)
        ((continuous_poissonWeight hz).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _) |>.mul_const _)
      intro t
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (poissonWeight_nonneg hz t)
    _ = _ := by rw [integral_mul_const, integral_poissonWeight hz, one_mul]

lemma integral_error_poissonLog_continuous_tendsto (f : C(BoundaryCircle, ℝ))
    {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t, ‖poissonLog f ((r n : ℂ) * circlePoint t) - f t‖
      ∂circleMeasure) atTop (𝓝 0) := by
  have hf : Integrable (f : BoundaryCircle → ℝ) circleMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht : ∀ t, Tendsto (fun n => ‖poissonLog f ((r n : ℂ) * circlePoint t) - f t‖)
      atTop (𝓝 0) := by
    intro t
    simpa using ((poissonLog_tendsto_continuous f hr0 hr1 hrlim t).sub_const (f t)).norm
  have hdom (n : ℕ) : ∀ᵐ t ∂circleMeasure,
      ‖‖poissonLog f ((r n : ℂ) * circlePoint t) - f t‖‖ ≤ 2 * ‖f‖ := by
    filter_upwards with t
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by
      have h1 := norm_poissonLog_continuous_le f (HardyDisk.radial_point_mem_disk (hr0 n) (hr1 n) t)
      change ‖poissonLog f ((r n : ℂ) * circlePoint t)‖ ≤ ‖f‖ at h1
      have h2 := f.norm_coe_le_norm t
      linarith)
  simpa using tendsto_integral_of_dominated_convergence (fun _ => 2 * ‖f‖)
    (fun n => ((integrable_radial_poissonLog hf (hr0 n) (hr1 n)).sub hf).norm.aestronglyMeasurable)
    (integrable_const _) hdom (Eventually.of_forall ht)

lemma poissonLog_sub {h k : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) (hk : Integrable k circleMeasure)
    {z : ℂ} (hz : z ∈ disk) :
    poissonLog (fun t => h t - k t) z = poissonLog h z - poissonLog k z := by
  unfold poissonLog
  simp_rw [mul_sub]
  exact integral_sub (integrable_poissonWeight_mul hh hz) (integrable_poissonWeight_mul hk hz)

lemma integral_error_poissonLog_le {h k : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) (hk : Integrable k circleMeasure)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t, ‖poissonLog h ((r : ℂ) * circlePoint t) - h t‖ ∂circleMeasure) ≤
      2 * (∫ t, ‖h t - k t‖ ∂circleMeasure) +
        (∫ t, ‖poissonLog k ((r : ℂ) * circlePoint t) - k t‖ ∂circleMeasure) := by
  have hhk : Integrable (fun t => h t - k t) circleMeasure := hh.sub hk
  have hP := (integrable_radial_poissonLog hhk hr0 hr1).norm
  have hkP := ((integrable_radial_poissonLog hk hr0 hr1).sub hk).norm
  have hpoint (t : BoundaryCircle) :
      ‖poissonLog h ((r : ℂ) * circlePoint t) - h t‖ ≤
        ‖poissonLog (fun u => h u - k u) ((r : ℂ) * circlePoint t)‖ +
          ‖poissonLog k ((r : ℂ) * circlePoint t) - k t‖ + ‖h t - k t‖ := by
    have hz : (r : ℂ) * circlePoint t ∈ disk := HardyDisk.radial_point_mem_disk hr0 hr1 t
    calc
      _ = ‖(poissonLog (fun u => h u - k u) ((r : ℂ) * circlePoint t) +
          (poissonLog k ((r : ℂ) * circlePoint t) - k t)) + (k t - h t)‖ := by
        rw [poissonLog_sub hh hk hz]
        congr 1
        ring
      _ ≤ _ := by
        apply (norm_add_le _ _).trans
        rw [norm_sub_rev (k t) (h t)]
        exact add_le_add (norm_add_le
          (poissonLog (fun u => h u - k u) ((r : ℂ) * circlePoint t))
          (poissonLog k ((r : ℂ) * circlePoint t) - k t)) le_rfl
  have hle := integral_mono (((integrable_radial_poissonLog hh hr0 hr1).sub hh).norm)
    ((hP.add hkP).add hhk.norm) hpoint
  have hadd := integral_add (hP.add hkP) hhk.norm
  have hadd' := integral_add hP hkP
  simp only [Pi.add_apply, Pi.sub_apply] at hle hadd hadd'
  rw [hadd, hadd'] at hle
  have hc := integral_norm_radial_poissonLog_le hhk hr0 hr1
  linarith

/-- L¹ approximation by Poisson integrals. This uses density of continuous
functions and the norm-one estimate, so no pointwise differentiation theorem
is assumed for integrable data. -/
lemma integral_error_poissonLog_tendsto {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t, ‖poissonLog h ((r n : ℂ) * circlePoint t) - h t‖
      ∂circleMeasure) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨f, hf⟩ := (ContinuousMap.toLp_denseRange ℝ circleMeasure ℝ
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).exists_dist_lt (hh.toL1 h)
      (by positivity : 0 < ε / 4)
  have happ : (∫ t, ‖h t - f t‖ ∂circleMeasure) < ε / 4 := by
    have he : (∫ t, ‖h t - f t‖ ∂circleMeasure) =
        dist (hh.toL1 h) (ContinuousMap.toLp 1 circleMeasure ℝ f) := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [hh.coeFn_toL1,
        ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) circleMeasure f] with t ht hft
      rw [ht, hft, dist_eq_norm]
    rw [he]
    exact hf
  have hfi : Integrable (f : BoundaryCircle → ℝ) circleMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  filter_upwards [(integral_error_poissonLog_continuous_tendsto f hr0 hr1 hrlim).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))] with n hn
  rw [dist_zero_right, Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have hb := integral_error_poissonLog_le hh hfi (hr0 n) (hr1 n)
  linarith

lemma poissonLog_tendstoInMeasure {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) :
    TendstoInMeasure circleMeasure
      (fun n t => poissonLog h ((r n : ℂ) * circlePoint t)) atTop h := by
  let p : ℕ → Lp ℝ 1 circleMeasure := fun n =>
    (integrable_radial_poissonLog hh (hr0 n) (hr1 n)).toL1 _
  have hpc (n : ℕ) : (p n : BoundaryCircle → ℝ) =ᵐ[circleMeasure]
      (fun t => poissonLog h ((r n : ℂ) * circlePoint t)) :=
    (integrable_radial_poissonLog hh (hr0 n) (hr1 n)).coeFn_toL1
  have hconv : Tendsto p atTop (𝓝 (hh.toL1 h)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hd (n : ℕ) : dist (p n) (hh.toL1 h) =
        ∫ t, ‖poissonLog h ((r n : ℂ) * circlePoint t) - h t‖ ∂circleMeasure := by
      rw [L1.dist_eq_integral_dist]
      apply integral_congr_ae
      filter_upwards [hpc n, hh.coeFn_toL1] with t ht hht
      rw [ht, hht, dist_eq_norm]
    simp_rw [hd]
    exact integral_error_poissonLog_tendsto hh hr0 hr1 hrlim
  exact ((tendstoInMeasure_of_tendsto_Lp hconv).congr_left hpc).congr_right hh.coeFn_toL1

/-- The boundary modulus of the constructed Hardy exponential is the prescribed
modulus. A common a.e. subsequence of the L¹ Poisson and L² Hardy limits suffices. -/
theorem boundary_exponential_realization : Spec.BoundaryExponentialRealization := by
  intro g hh hne c hc
  obtain ⟨o, ho, _⟩ := boundary_exponential_hardy g hh hne c hc
  refine ⟨o, ho, ?_⟩
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have hd : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have := (div_le_one (by positivity : 0 < (n : ℝ) + 2)).mpr hd
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa [r] using tendsto_const_nhds.sub hinv
  obtain ⟨k, hk, hPk⟩ := (poissonLog_tendstoInMeasure hh hr0 hr1 hrlim).exists_seq_tendsto_ae
  obtain ⟨v, hv, hvlim⟩ := HardyDisk.radial_convergence o
  have hrt : Tendsto (fun n => r (k n)) atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim.comp hk.tendsto_atTop, Eventually.of_forall fun n => hr1 (k n)⟩
  obtain ⟨l, hl, hvl⟩ := (tendstoInMeasure_of_tendsto_Lp (hvlim.comp hrt)).exists_seq_tendsto_ae
  have hvalues (n : ℕ) :
      (v (r (k (l n))) : BoundaryCircle → ℂ) =ᵐ[circleMeasure] fun t =>
        exponentialFactor (fun u => Real.log ‖g u‖) c ((r (k (l n)) : ℂ) * circlePoint t) := by
    filter_upwards [hv (r (k (l n))) (hr0 _) (hr1 _)] with t ht
    rw [ht]
    exact ho (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)
  filter_upwards [hPk, hvl, ae_all_iff.mpr hvalues, hne] with t hPt hvt hvals hgt
  have hnorm := hvt.norm
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hPt.comp hl.tendsto_atTop)
  have hn (n : ℕ) : ‖v (r (k (l n))) t‖ =
      Real.exp (poissonLog (fun u => Real.log ‖g u‖)
        ((r (k (l n)) : ℂ) * circlePoint t)) := by
    rw [hvals n]
    exact exponential_norm _ hh c hc _ (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)
  have hexp' : Tendsto (fun n => ‖v (r (k (l n))) t‖) atTop
      (𝓝 (Real.exp (Real.log ‖g t‖))) := hexp.congr' (Eventually.of_forall fun n => (hn n).symm)
  have heq := tendsto_nhds_unique hnorm hexp'
  rw [Real.exp_log (norm_pos_iff.mpr hgt)] at heq
  exact heq


/-- The logarithm truncated from below before taking a boundary limit. -/
def truncatedLog (g : BoundaryL2) (N : ℕ) (t : BoundaryCircle) : ℝ :=
  Real.log (max ‖g t‖ (Real.exp (-(N : ℝ))))

lemma truncatedLog_lower (g : BoundaryL2) (N : ℕ) (t : BoundaryCircle) :
    -(N : ℝ) ≤ truncatedLog g N t := by
  simpa [truncatedLog] using Real.log_le_log (Real.exp_pos (-(N : ℝ)))
    (le_max_right ‖g t‖ (Real.exp (-(N : ℝ))))

lemma truncatedLog_integrable (g : BoundaryL2) (N : ℕ) :
    Integrable (truncatedLog g N) circleMeasure := by
  have hε : 0 < Real.exp (-(N : ℝ)) := Real.exp_pos _
  have hε1 : Real.exp (-(N : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  have hg : Integrable (g : BoundaryCircle → ℂ) circleMeasure :=
    (Lp.memLp g).integrable (by norm_num)
  have hm : AEStronglyMeasurable (truncatedLog g N) circleMeasure :=
    (hg.aestronglyMeasurable.norm.aemeasurable.max aemeasurable_const).log.aestronglyMeasurable
  apply (hg.norm.add (integrable_const ((N : ℝ) + 1))).mono' hm
  filter_upwards with t
  change |truncatedLog g N t| ≤ ‖g t‖ + ((N : ℝ) + 1)
  apply abs_le.mpr
  constructor
  · have hl := truncatedLog_lower g N t
    linarith [norm_nonneg (g t)]
  · calc
      truncatedLog g N t ≤ max ‖g t‖ (Real.exp (-(N : ℝ))) :=
        Real.log_le_self (le_max_of_le_right hε.le)
      _ ≤ ‖g t‖ + ((N : ℝ) + 1) := by
        apply max_le
        · linarith [Nat.cast_nonneg (α := ℝ) N]
        · linarith [norm_nonneg (g t), Nat.cast_nonneg (α := ℝ) N]

lemma exp_two_truncatedLog_integrable (g : BoundaryL2) (N : ℕ) :
    Integrable (fun t => Real.exp (2 * truncatedLog g N t)) circleMeasure := by
  have hsq : Integrable (fun t => ‖g t‖ ^ 2) circleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hm : AEStronglyMeasurable (fun t => Real.exp (2 * truncatedLog g N t))
      circleMeasure :=
    ((truncatedLog_integrable g N).aestronglyMeasurable.const_mul 2).aemeasurable.exp.aestronglyMeasurable
  apply (hsq.add (integrable_const (1 : ℝ))).mono' hm
  filter_upwards with t
  change ‖Real.exp (2 * truncatedLog g N t)‖ ≤ ‖g t‖ ^ 2 + 1
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hε : 0 < Real.exp (-(N : ℝ)) := Real.exp_pos _
  have hε1 : Real.exp (-(N : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  have he : Real.exp (2 * truncatedLog g N t) =
      (max ‖g t‖ (Real.exp (-(N : ℝ)))) ^ 2 := by
    unfold truncatedLog
    change Real.exp (((2 : ℕ) : ℝ) * _) = _
    rw [Real.exp_nat_mul,
      Real.exp_log (lt_of_lt_of_le hε (le_max_right _ _))]
  rw [he]
  rcases le_total ‖g t‖ (Real.exp (-(N : ℝ))) with h|h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖g t‖]
  · rw [max_eq_left h]
    linarith

lemma truncatedLog_poisson_lower (g : BoundaryL2) (N : ℕ) {z : ℂ} (hz : z ∈ disk) :
    -(N : ℝ) ≤ poissonLog (truncatedLog g N) z := by
  have hP : Integrable (poissonWeight z) circleMeasure :=
    (continuous_poissonWeight hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono := integral_mono (hP.mul_const (-(N : ℝ)))
    (integrable_poissonWeight_mul (truncatedLog_integrable g N) hz)
    (fun t => mul_le_mul_of_nonneg_left (truncatedLog_lower g N t)
      (poissonWeight_nonneg hz t))
  rw [integral_mul_const, integral_poissonWeight hz, one_mul] at hmono
  exact hmono

lemma truncated_exponential_lower (g : BoundaryL2) (N : ℕ) {z : ℂ} (hz : z ∈ disk) :
    Real.exp (-(N : ℝ)) ≤ ‖exponentialFactor (truncatedLog g N) 1 z‖ := by
  rw [exponential_norm _ (truncatedLog_integrable g N) 1 (by simp) z hz]
  exact Real.exp_le_exp.mpr (truncatedLog_poisson_lower g N hz)

/-- The boundary modulus of the Hardy exponential for a general real density. -/
theorem exponential_boundary_modulus {h : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure)
    (he : Integrable (fun t => Real.exp (2 * h t)) circleMeasure)
    {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ o : H2, Set.EqOn (eval o) (exponentialFactor h c) disk ∧
      ∀ᵐ t ∂circleMeasure, ‖boundary o t‖ = Real.exp (h t) := by
  obtain ⟨o, ho, _⟩ := exponential_hardy_membership hh he hc
  refine ⟨o, ho, ?_⟩
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have hd : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have := (div_le_one (by positivity : 0 < (n : ℝ) + 2)).mpr hd
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa [r] using tendsto_const_nhds.sub hinv
  obtain ⟨k, hk, hPk⟩ := (poissonLog_tendstoInMeasure hh hr0 hr1 hrlim).exists_seq_tendsto_ae
  obtain ⟨v, hv, hvlim⟩ := HardyDisk.radial_convergence o
  have hrt : Tendsto (fun n => r (k n)) atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim.comp hk.tendsto_atTop, Eventually.of_forall fun n => hr1 (k n)⟩
  obtain ⟨l, hl, hvl⟩ := (tendstoInMeasure_of_tendsto_Lp (hvlim.comp hrt)).exists_seq_tendsto_ae
  have hvalues (n : ℕ) :
      (v (r (k (l n))) : BoundaryCircle → ℂ) =ᵐ[circleMeasure] fun t =>
        exponentialFactor (h) c ((r (k (l n)) : ℂ) * circlePoint t) := by
    filter_upwards [hv (r (k (l n))) (hr0 _) (hr1 _)] with t ht
    rw [ht]
    exact ho (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)
  filter_upwards [hPk, hvl, ae_all_iff.mpr hvalues] with t hPt hvt hvals
  have hnorm := hvt.norm
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hPt.comp hl.tendsto_atTop)
  have hn (n : ℕ) : ‖v (r (k (l n))) t‖ =
      Real.exp (poissonLog (h)
        ((r (k (l n)) : ℂ) * circlePoint t)) := by
    rw [hvals n]
    exact exponential_norm _ hh c hc _ (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)
  have hexp' : Tendsto (fun n => ‖v (r (k (l n))) t‖) atTop
      (𝓝 (Real.exp (h t))) := hexp.congr' (Eventually.of_forall fun n => (hn n).symm)
  exact tendsto_nhds_unique hnorm hexp'

lemma truncated_exponential_realization (g : BoundaryL2) (N : ℕ) :
    ∃ o : H2, Set.EqOn (eval o) (exponentialFactor (truncatedLog g N) 1) disk ∧
      ∀ᵐ t ∂circleMeasure, ‖boundary o t‖ = max ‖g t‖ (Real.exp (-(N : ℝ))) := by
  obtain ⟨o, ho, hb⟩ := exponential_boundary_modulus
    (truncatedLog_integrable g N) (exp_two_truncatedLog_integrable g N) (c := 1) (by simp)
  refine ⟨o, ho, ?_⟩
  filter_upwards [hb] with t ht
  rw [ht, truncatedLog, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))]


lemma exists_subseq_radial_ae (f : H2) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (hrlim : Tendsto r atTop (𝓝 1)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ t ∂circleMeasure,
      Tendsto (fun n => eval f ((r (k n) : ℂ) * circlePoint t)) atTop
        (𝓝 (boundary f t)) := by
  have hc : Tendsto (fun n => boundary (HardyDisk.radialCoefficients (r n) f))
      atTop (𝓝 (boundary f)) :=
    boundary.continuous.continuousAt.tendsto.comp
      ((HardyDisk.radialCoefficients_tendsto f).comp hrlim)
  obtain ⟨k, hk, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hc).exists_seq_tendsto_ae
  refine ⟨k, hk, ?_⟩
  have hv (n : ℕ) :
      (boundary (HardyDisk.radialCoefficients (r (k n)) f) : BoundaryCircle → ℂ) =ᵐ[circleMeasure]
      (fun t => eval f ((r (k n) : ℂ) * circlePoint t)) :=
    HardyDisk.radial_boundary_values f (hr0 _) (hr1 _)
  filter_upwards [hkae, ae_all_iff.mpr hv] with t ht hvt
  exact ht.congr' (Eventually.of_forall fun n => hvt n)

lemma boundary_mul_of_eval_mul {f g h : H2}
    (he : ∀ z ∈ disk, eval h z = eval f z * eval g z) :
    ∀ᵐ t ∂circleMeasure, boundary h t = boundary f t * boundary g t := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have hd : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have := (div_le_one (by positivity : 0 < (n : ℝ) + 2)).mpr hd
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa [r] using tendsto_const_nhds.sub hinv
  obtain ⟨k, hk, hfk⟩ := exists_subseq_radial_ae f hr0 hr1 hrlim
  obtain ⟨l, hl, hgl⟩ := exists_subseq_radial_ae g (fun n => hr0 (k n))
    (fun n => hr1 (k n)) (hrlim.comp hk.tendsto_atTop)
  obtain ⟨j, hj, hhj⟩ := exists_subseq_radial_ae h (fun n => hr0 (k (l n)))
    (fun n => hr1 (k (l n)))
    ((hrlim.comp hk.tendsto_atTop).comp hl.tendsto_atTop)
  filter_upwards [hfk, hgl, hhj] with t hft hgt hht
  have htprod := ((hft.comp hl.tendsto_atTop).comp hj.tendsto_atTop).mul
    (hgt.comp hj.tendsto_atTop)
  apply tendsto_nhds_unique hht
  exact htprod.congr' (Eventually.of_forall fun n =>
    (he _ (HardyDisk.radial_point_mem_disk (hr0 _) (hr1 _) t)).symm)

lemma evaluation_norm_le_of_boundary_norm_le {f : H2} {C : ℝ}
    (hb : ∀ᵐ t ∂circleMeasure, ‖boundary f t‖ ≤ C)
    {z : ℂ} (hz : z ∈ disk) : ‖eval f z‖ ≤ C := by
  have hP : Integrable (poissonWeight z) circleMeasure :=
    (continuous_poissonWeight hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (fun t => poissonWeight z t * ‖boundary f t‖) circleMeasure :=
    integrable_poissonWeight_mul ((Lp.memLp (boundary f)).integrable (by norm_num)).norm hz
  have hp := HardyDisk.poisson_evaluation f z hz
  rw [← hp]
  change ‖∫ t, (poissonWeight z t : ℂ) * boundary f t ∂circleMeasure‖ ≤ C
  calc
    _ ≤ ∫ t, ‖(poissonWeight z t : ℂ) * boundary f t‖ ∂circleMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ t, poissonWeight z t * ‖boundary f t‖ ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      simp [Complex.norm_real, Real.norm_of_nonneg (poissonWeight_nonneg hz t)]
    _ ≤ ∫ t, poissonWeight z t * C ∂circleMeasure := by
      apply integral_mono_ae hi (hP.mul_const C)
      filter_upwards [hb] with t ht
      exact mul_le_mul_of_nonneg_left ht (poissonWeight_nonneg hz t)
    _ = C := by rw [integral_mul_const, integral_poissonWeight hz, one_mul]

lemma hardy_quotient_of_lower_bound (f o : H2) {δ : ℝ} (hδ : 0 < δ)
    (ho : ∀ z ∈ disk, δ ≤ ‖eval o z‖) :
    ∃ q : H2, ∀ z ∈ disk, eval q z = eval f z / eval o z := by
  have hone : ∀ z ∈ disk, eval o z ≠ 0 := fun z hz =>
    norm_pos_iff.mp (hδ.trans_le (ho z hz))
  let bval : Disk → ℂ := fun z => (eval o z)⁻¹
  have hdiff : DifferentiableOn ℂ (zeroExtend bval) disk :=
    ((HardyDisk.analytic_evaluation o).differentiableOn.inv hone).congr
      (fun z hz => by simp [zeroExtend, hz, bval])
  let b : HInfinity := ⟨bval, hdiff, δ⁻¹, fun z => by
    change ‖(eval o z)⁻¹‖ ≤ δ⁻¹
    rw [norm_inv]
    exact (inv_le_inv₀ (hδ.trans_le (ho z z.property)) hδ).mpr (ho z z.property)⟩
  obtain ⟨q, hq, _⟩ := HardyDisk.multiplier_exists b f
  refine ⟨q, fun z hz => ?_⟩
  calc
    eval q z = zeroExtend b.val z * eval f z := hq hz
    _ = _ := by simp [b, bval, zeroExtend, hz, div_eq_mul_inv, mul_comm]

lemma quotient_bound_of_boundary_comparison (f o : H2) {δ : ℝ} (hδ : 0 < δ)
    (ho : ∀ z ∈ disk, δ ≤ ‖eval o z‖)
    (hbo : ∀ᵐ t ∂circleMeasure, δ ≤ ‖boundary o t‖)
    (hbf : ∀ᵐ t ∂circleMeasure, ‖boundary f t‖ ≤ ‖boundary o t‖) :
    ∀ z ∈ disk, ‖eval f z / eval o z‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := hardy_quotient_of_lower_bound f o hδ ho
  have hmul : ∀ᵐ t ∂circleMeasure, boundary f t = boundary q t * boundary o t := by
    apply boundary_mul_of_eval_mul
    intro z hz
    rw [hq z hz, div_mul_cancel₀]
    exact norm_pos_iff.mp (hδ.trans_le (ho z hz))
  have hqb : ∀ᵐ t ∂circleMeasure, ‖boundary q t‖ ≤ 1 := by
    filter_upwards [hmul, hbo, hbf] with t ht hot hft
    rw [ht, norm_mul] at hft
    exact (mul_le_iff_le_one_left (hδ.trans_le hot)).mp hft
  intro z hz
  rw [← hq z hz]
  exact evaluation_norm_le_of_boundary_norm_le hqb hz

lemma truncated_exponential_majorization (f : H2) (N : ℕ) {z : ℂ} (hz : z ∈ disk) :
    ‖eval f z‖ ≤ Real.exp (poissonLog (truncatedLog (boundary f) N) z) := by
  obtain ⟨o, ho, hbo⟩ := truncated_exponential_realization (boundary f) N
  have hδ : 0 < Real.exp (-(N : ℝ)) := Real.exp_pos _
  have hlow : ∀ w ∈ disk, Real.exp (-(N : ℝ)) ≤ ‖eval o w‖ := by
    intro w hw
    rw [ho hw]
    exact truncated_exponential_lower (boundary f) N hw
  have hbδ : ∀ᵐ t ∂circleMeasure, Real.exp (-(N : ℝ)) ≤ ‖boundary o t‖ := by
    filter_upwards [hbo] with t ht
    rw [ht]
    exact le_max_right _ _
  have hbcmp : ∀ᵐ t ∂circleMeasure, ‖boundary f t‖ ≤ ‖boundary o t‖ := by
    filter_upwards [hbo] with t ht
    rw [ht]
    exact le_max_left _ _
  have hq := quotient_bound_of_boundary_comparison f o hδ hlow hbδ hbcmp z hz
  have honorm : ‖eval o z‖ = Real.exp (poissonLog (truncatedLog (boundary f) N) z) := by
    rw [ho hz]
    exact exponential_norm _ (truncatedLog_integrable _ _) 1 (by simp) z hz
  rw [norm_div] at hq
  have hm := (div_le_one (hδ.trans_le (hlow z hz))).mp hq
  rwa [honorm] at hm

lemma truncated_log_majorization (f : H2) (N : ℕ) {z : ℂ} (hz : z ∈ disk)
    (hfz : eval f z ≠ 0) :
    Real.log ‖eval f z‖ ≤ poissonLog (truncatedLog (boundary f) N) z := by
  have hm := Real.log_le_log (norm_pos_iff.mpr hfz) (truncated_exponential_majorization f N hz)
  rwa [Real.log_exp] at hm



lemma poissonWeight_uniform_pos {z : ℂ} (hz : z ∈ disk) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, δ ≤ poissonWeight z t := by
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  have ha : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hb : 0 < 1 + ‖z‖ := by positivity
  refine ⟨(1 - ‖z‖ ^ 2) / (1 + ‖z‖) ^ 2, div_pos ha (sq_pos_of_pos hb), ?_⟩
  intro t
  apply div_le_div_of_nonneg_left ha.le
    (sq_pos_of_pos (norm_pos_iff.mpr (circlePoint_sub_ne_zero hz t)))
  have hn := norm_sub_le (circlePoint t) z
  rw [norm_circlePoint] at hn
  nlinarith [norm_nonneg (circlePoint t - z)]

lemma positiveLog_integrable_L2 (g : BoundaryL2) :
    Integrable (fun t => max (Real.log ‖g t‖) 0) circleMeasure := by
  have hb : Integrable (g : BoundaryCircle → ℂ) circleMeasure :=
    (Lp.memLp g).integrable (by norm_num)
  have hm : AEStronglyMeasurable (fun t => Real.log ‖g t‖) circleMeasure :=
    hb.aestronglyMeasurable.norm.aemeasurable.log.aestronglyMeasurable
  refine hb.norm.mono' (hm.aemeasurable.max aemeasurable_const).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (Real.log_le_self (norm_nonneg _)) (norm_nonneg _)

lemma truncatedLog_le_positiveLog (g : BoundaryL2) (N : ℕ) (t : BoundaryCircle) :
    truncatedLog g N t ≤ max (Real.log ‖g t‖) 0 := by
  have hε1 : Real.exp (-(N : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  rcases le_total ‖g t‖ (Real.exp (-(N : ℝ))) with h | h
  · rw [truncatedLog, max_eq_right h, Real.log_exp]
    exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg N)) (le_max_right _ _)
  · rw [truncatedLog, max_eq_left h]
    exact le_max_left _ _

/-- A lower logarithmic estimate at one point controls the entire negative
boundary logarithm after truncation. -/
lemma truncated_negative_integrals_bounded (g : BoundaryL2)
    {z : ℂ} (hz : z ∈ disk) {A : ℝ}
    (hbound : ∀ N : ℕ, A ≤ poissonLog (truncatedLog g N) z) :
    ∃ C : ℝ, ∀ N : ℕ,
      (∫ t, (max (Real.log ‖g t‖) 0 - truncatedLog g N t) ∂circleMeasure) ≤ C := by
  obtain ⟨δ, hδ, hδP⟩ := poissonWeight_uniform_pos hz
  let p : BoundaryCircle → ℝ := fun t => max (Real.log ‖g t‖) 0
  have hp : Integrable p circleMeasure := positiveLog_integrable_L2 g
  refine ⟨(poissonLog p z - A) / δ, ?_⟩
  intro N
  have hq : Integrable (fun t => p t - truncatedLog g N t) circleMeasure :=
    hp.sub (truncatedLog_integrable g N)
  have hq0 (t : BoundaryCircle) : 0 ≤ p t - truncatedLog g N t :=
    sub_nonneg.mpr (truncatedLog_le_positiveLog g N t)
  have hineq : δ * (∫ t, (p t - truncatedLog g N t) ∂circleMeasure) ≤
      poissonLog p z - poissonLog (truncatedLog g N) z := by
    rw [← integral_const_mul, ← poissonLog_sub hp (truncatedLog_integrable g N) hz]
    exact integral_mono (hq.const_mul _) (integrable_poissonWeight_mul hq hz)
      (fun t => mul_le_mul_of_nonneg_right (hδP t) (hq0 t))
  apply (le_div_iff₀ hδ).mpr
  change (∫ t, (p t - truncatedLog g N t) ∂circleMeasure) * δ ≤ _
  have hb := hbound N
  nlinarith

lemma exists_nonzero_evaluation {f : H2} (hf : f ≠ 0) :
    ∃ z ∈ disk, eval f z ≠ 0 := by
  by_contra! h
  apply hf
  apply HardyDisk.evaluation_injective f 0
  intro z hz
  rw [h z hz]
  simp [eval]

lemma truncatedLog_antitone (g : BoundaryL2) (t : BoundaryCircle) :
    Antitone (fun N => truncatedLog g N t) := by
  intro N M hNM
  apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))
  apply max_le_max le_rfl
  exact Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hNM))

lemma truncatedLog_eventually_eq {g : BoundaryL2} {t : BoundaryCircle} (ht : g t ≠ 0) :
    ∀ᶠ N : ℕ in atTop, truncatedLog g N t = Real.log ‖g t‖ := by
  have hlim : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds (norm_pos_iff.mpr ht))] with N hN
  exact congrArg Real.log (max_eq_left hN.le)

lemma log_integrable_of_truncated_negative_bound (g : BoundaryL2)
    (hbound : ∃ C : ℝ, ∀ N : ℕ,
      (∫ t, (max (Real.log ‖g t‖) 0 - truncatedLog g N t) ∂circleMeasure) ≤ C) :
    Integrable (fun t => Real.log ‖g t‖) circleMeasure ∧
      ∀ᵐ t ∂circleMeasure, g t ≠ 0 := by
  obtain ⟨C, hC⟩ := hbound
  let p : BoundaryCircle → ℝ := fun t => max (Real.log ‖g t‖) 0
  let q : ℕ → BoundaryCircle → ℝ := fun N t => p t - truncatedLog g N t
  let Q : BoundaryCircle → ℝ≥0∞ := fun t => ⨆ N : ℕ, ENNReal.ofReal (q N t)
  have hp : Integrable p circleMeasure := positiveLog_integrable_L2 g
  have hq (N : ℕ) : Integrable (q N) circleMeasure := hp.sub (truncatedLog_integrable g N)
  have hq0 (N : ℕ) (t : BoundaryCircle) : 0 ≤ q N t :=
    sub_nonneg.mpr (truncatedLog_le_positiveLog g N t)
  have hqm (N : ℕ) : AEMeasurable (fun t => ENNReal.ofReal (q N t)) circleMeasure :=
    (hq N).aemeasurable.ennreal_ofReal
  have hQm : AEMeasurable Q circleMeasure := .iSup hqm
  have hQI : (∫⁻ t, Q t ∂circleMeasure) ≤ ENNReal.ofReal C := by
    rw [lintegral_iSup' hqm]
    · apply iSup_le
      intro N
      rw [← ofReal_integral_eq_lintegral_ofReal (hq N) (Eventually.of_forall (hq0 N))]
      exact ENNReal.ofReal_le_ofReal (hC N)
    · filter_upwards with t N M hNM
      exact ENNReal.ofReal_le_ofReal
        (sub_le_sub_left (truncatedLog_antitone g t hNM) _)
  have hQfinite : (∫⁻ t, Q t ∂circleMeasure) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQI
  have hQae : ∀ᵐ t ∂circleMeasure, Q t < ∞ := ae_lt_top' hQm hQfinite
  have hne : ∀ᵐ t ∂circleMeasure, g t ≠ 0 := by
    filter_upwards [hQae] with t ht
    intro hzero
    have hN (N : ℕ) : ENNReal.ofReal (N : ℝ) ≤ Q t := by
      have hqN : q N t = (N : ℝ) := by
        simp [q, p, truncatedLog, hzero, max_eq_right (Real.exp_pos (-(N : ℝ))).le]
      rw [← hqN]
      exact le_iSup (fun N : ℕ => ENNReal.ofReal (q N t)) N
    obtain ⟨N, hNlt⟩ := exists_nat_gt (Q t).toReal
    have hle := ENNReal.toReal_mono ht.ne (hN N)
    rw [ENNReal.toReal_ofReal (Nat.cast_nonneg N)] at hle
    exact (not_lt_of_ge hle) hNlt
  refine ⟨?_, hne⟩
  have hQi : Integrable (fun t => (Q t).toReal) circleMeasure :=
    integrable_toReal_of_lintegral_ne_top hQm hQfinite
  have hlogm : AEStronglyMeasurable (fun t => Real.log ‖g t‖) circleMeasure :=
    (Lp.aestronglyMeasurable g).norm.aemeasurable.log.aestronglyMeasurable
  apply (hp.add hQi).mono' hlogm
  filter_upwards [hQae, hne] with t hQt hgt
  obtain ⟨N, hN⟩ := (truncatedLog_eventually_eq hgt).exists
  have hle : p t - Real.log ‖g t‖ ≤ (Q t).toReal := by
    rw [← hN]
    exact (ENNReal.ofReal_le_iff_le_toReal hQt.ne).mp
      (le_iSup (fun N : ℕ => ENNReal.ofReal (q N t)) N)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  apply abs_le.mpr
  constructor
  · have hp0 : 0 ≤ p t := le_max_right _ _
    linarith
  · have hplog : Real.log ‖g t‖ ≤ p t := le_max_left _ _
    linarith


/-- Nonzero Hardy functions have integrable boundary logarithms and nonvanishing
boundary values almost everywhere.  The cutoff estimates control their negative
parts without assuming this conclusion in the exponential construction. -/
theorem boundary_log_integrable : Spec.BoundaryLogIntegrable := by
  intro f hf
  obtain ⟨z, hz, hfz⟩ := exists_nonzero_evaluation hf
  exact log_integrable_of_truncated_negative_bound (boundary f)
    (truncated_negative_integrals_bounded (boundary f) hz
      (fun N => truncated_log_majorization f N hz hfz))

lemma truncatedLog_norm_le_of_ne_zero (g : BoundaryL2) (N : ℕ) {t : BoundaryCircle}
    (ht : g t ≠ 0) : ‖truncatedLog g N t‖ ≤ ‖Real.log ‖g t‖‖ := by
  rcases le_total (Real.exp (-(N : ℝ))) ‖g t‖ with h|h
  · simp [truncatedLog, max_eq_left h]
  · rw [truncatedLog, max_eq_right h, Real.log_exp]
    have hl := Real.log_le_log (norm_pos_iff.mpr ht) h
    rw [Real.log_exp] at hl
    have hN : -(N : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg N)
    simp only [Real.norm_eq_abs, abs_of_nonpos hN,
      abs_of_nonpos (hl.trans hN), neg_neg]
    linarith

lemma truncatedLog_tendsto_of_ne_zero (g : BoundaryL2) {t : BoundaryCircle}
    (ht : g t ≠ 0) :
    Tendsto (fun N => truncatedLog g N t) atTop (𝓝 (Real.log ‖g t‖)) := by
  have hε : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have heq : (fun N => truncatedLog g N t) =ᶠ[atTop] (fun _ : ℕ => Real.log ‖g t‖) := by
    filter_upwards [hε.eventually (gt_mem_nhds (norm_pos_iff.mpr ht))] with N hN
    simp [truncatedLog, max_eq_left hN.le]
  exact tendsto_const_nhds.congr' heq.symm

lemma poissonLog_truncated_tendsto (g : BoundaryL2)
    (hh : Integrable (fun t => Real.log ‖g t‖) circleMeasure)
    (hne : ∀ᵐ t ∂circleMeasure, g t ≠ 0) {z : ℂ} (hz : z ∈ disk) :
    Tendsto (fun N => poissonLog (truncatedLog g N) z) atTop
      (𝓝 (poissonLog (fun t => Real.log ‖g t‖) z)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t => poissonWeight z t * ‖Real.log ‖g t‖‖)
  · intro N
    exact (integrable_poissonWeight_mul (truncatedLog_integrable g N) hz).aestronglyMeasurable
  · exact integrable_poissonWeight_mul hh.norm hz
  · intro N
    filter_upwards [hne] with t ht
    change ‖poissonWeight z t * truncatedLog g N t‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg (poissonWeight_nonneg hz t)]
    exact mul_le_mul_of_nonneg_left (truncatedLog_norm_le_of_ne_zero g N ht)
      (poissonWeight_nonneg hz t)
  · filter_upwards [hne] with t ht
    exact (truncatedLog_tendsto_of_ne_zero g ht).const_mul (poissonWeight z t)

lemma log_majorization_of_boundary_log_integrable
    (hboundary : Spec.BoundaryLogIntegrable) : Spec.LogMajorization := by
  intro f hf z hz hfz
  obtain ⟨hh, hne⟩ := hboundary f hf
  exact ge_of_tendsto (poissonLog_truncated_tendsto (boundary f) hh hne hz)
    (Eventually.of_forall fun N => truncated_log_majorization f N hz hfz)


/-- Poisson majorization of the integrable boundary logarithm. -/
theorem log_majorization : Spec.LogMajorization :=
  log_majorization_of_boundary_log_integrable boundary_log_integrable

/-- Converts the logarithmic statement to the pointwise statement that includes
zeros. This is an assembly lemma, not a proof of logarithmic majorization. -/
lemma exponentialMajorization_of_logMajorization (hlog : Spec.LogMajorization) :
    Spec.ExponentialMajorization := by
  intro f hf z hz
  by_cases hzero : eval f z = 0
  · simp only [hzero, norm_zero]
    exact (Real.exp_pos _).le
  · exact Real.le_exp_of_log_le (hlog f hf z hz hzero)

lemma quotient_bound_of_majorization {f : H2} {c : ℂ} (hc : ‖c‖ = 1)
    (hh : Integrable (boundaryLog f) circleMeasure) {z : ℂ} (hz : z ∈ disk)
    (hbound : ‖eval f z‖ ≤ Real.exp (poissonLog (boundaryLog f) z)) :
    ‖eval f z / exponentialFactor (boundaryLog f) c z‖ ≤ 1 := by
  rw [norm_div, exponential_norm (boundaryLog f) hh c hc z hz]
  exact (div_le_one (Real.exp_pos _)).mpr hbound

/-- Assembly of the factor construction from the boundary logarithm,
majorization, and general exponential realization theorems. -/
lemma factorConstruction_of_boundary_theorems
    (hboundary : Spec.BoundaryLogIntegrable) (hlog : Spec.LogMajorization)
    (hrealize : Spec.BoundaryExponentialRealization) : Spec.FactorConstruction := by
  intro f hf c hc
  obtain ⟨hh, hne⟩ := hboundary f hf
  have hc' : c ≠ 0 := by
    intro he
    simp [he] at hc
  refine ⟨exponential_holomorphic (boundaryLog f) hh c,
    fun z _ => exponential_nonzero (boundaryLog f) c hc' z, ?_⟩
  obtain ⟨o, ho, hmod⟩ := hrealize (boundary f) hh hne c hc
  exact ⟨o, ho, hmod, fun z hz => quotient_bound_of_majorization hc hh hz
    (exponentialMajorization_of_logMajorization hlog f hf z hz)⟩

/-- The majorization also holds at interior zeros in its exponential form. -/
theorem exponential_majorization : Spec.ExponentialMajorization :=
  exponentialMajorization_of_logMajorization log_majorization

/-- The displayed exponential is zero-free holomorphic, belongs to the canonical
Hardy space with the prescribed boundary modulus, and divides f with bound one. -/
theorem factor_construction : Spec.FactorConstruction :=
  factorConstruction_of_boundary_theorems boundary_log_integrable log_majorization
    boundary_exponential_realization

end ExpandedFA.PartIV.HardyLogModulus
