import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.SmoothNonanalyticExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter MeasureTheory Polynomial Real
open scoped Topology ContDiff
namespace D13Unified.SmoothNonanalytic

def g : ℝ → ℝ := Specs.D13Unified.Ch06.SmoothNonanalyticExample.gValue

def x : ℝ → ℝ := Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue

lemma g_of_pos {t : ℝ} (ht : 0 < t) : g t = exp (-1 / t ^ 2) := by
  simp [g, Specs.D13Unified.Ch06.SmoothNonanalyticExample.gValue, ht]

lemma g_of_nonpos {t : ℝ} (ht : t ≤ 0) : g t = 0 := by
  simp [g, Specs.D13Unified.Ch06.SmoothNonanalyticExample.gValue, not_lt.mpr ht]

lemma g_nonneg (t : ℝ) : 0 ≤ g t := by
  by_cases ht : 0 < t
  · rw [g_of_pos ht]; exact (exp_pos _).le
  · rw [g_of_nonpos (le_of_not_gt ht)]

lemma g_le_glue {t : ℝ} (ht : t < 1) : g t ≤ expNegInvGlue t := by
  by_cases hp : 0 < t
  · rw [g_of_pos hp, expNegInvGlue, ite_eq_right hp.not_ge]
    apply exp_le_exp.mpr
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos hp
    have hsq : t ^ 2 ≤ t := by nlinarith
    have hi := (one_div_le_one_div_of_le ht2 hsq)
    calc
      -1 / t ^ 2 = -(1 / t ^ 2) := by ring
      _ ≤ -(1 / t) := neg_le_neg hi
      _ = -t⁻¹ := by rw [one_div]
  · rw [g_of_nonpos (le_of_not_gt hp), expNegInvGlue.zero_of_nonpos (le_of_not_gt hp)]

/-- Exponential flatness dominates every polynomial singularity. Compare
with the already proved Mathlib flat function exp(-1/t), for 0<t<1. -/
lemma polynomial_limit (p : ℝ[X]) :
    Tendsto (fun t => p.eval t⁻¹ * g t) (𝓝 0) (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using
    (expNegInvGlue.tendsto_polynomial_inv_mul_zero p).norm)
  · filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (g_nonneg t),
      abs_of_nonneg (expNegInvGlue.nonneg t)]
    exact mul_le_mul_of_nonneg_left (g_le_glue ht) (abs_nonneg _)

/-- Differentiation preserves polynomial times the forcing. -/
lemma polynomial_hasDeriv (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (fun r => p.eval r⁻¹ * g r)
      ((2 * X ^ 3 * p - X ^ 2 * p.derivative).eval t⁻¹ * g t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [g_of_nonpos ht.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds ht] with r hr
    rw [g_of_nonpos hr.le, mul_zero]
  · rw [g_of_nonpos le_rfl, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((polynomial_limit (p * X)).mono_left inf_le_left).congr fun r => ?_
    simp [slope_def_field, g_of_nonpos le_rfl, div_eq_mul_inv, mul_right_comm]
  · have hd := ((p.hasDerivAt t⁻¹).mul
        (((hasDerivAt_id t⁻¹).pow 2).neg.exp)).comp t (hasDerivAt_inv ht.ne')
    convert hd.congr_of_eventuallyEq ?_ using 1
    · simp [g_of_pos ht, div_eq_mul_inv, inv_pow]
      ring
    · filter_upwards [lt_mem_nhds ht] with r hr
      simp [g_of_pos hr, div_eq_mul_inv, inv_pow]

lemma polynomial_contDiff (p : ℝ[X]) :
    ContDiff ℝ ∞ (fun t => p.eval t⁻¹ * g t) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) (⊤ : ℕ∞)
  induction m generalizing p with
  | zero => exact contDiff_zero.2 (show Differentiable ℝ _ from fun t =>
      (polynomial_hasDeriv p t).differentiableAt).continuous
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨fun t => (polynomial_hasDeriv p t).differentiableAt,
      by simp, ?_⟩
    convert! ih (2 * X ^ 3 * p - X ^ 2 * p.derivative) using 2
    exact (polynomial_hasDeriv p _).deriv

/-- Smoothness of the exact one-sided forcing in the paper. -/
theorem smooth : Specs.D13Unified.Ch06.SmoothNonanalyticExample.smoothExpected := by
  change ContDiff ℝ ∞ g
  simpa using polynomial_contDiff 1

lemma iterated_polynomial (n : ℕ) :
    ∃ p : ℝ[X], iteratedDeriv n g = fun t => p.eval t⁻¹ * g t := by
  induction n with
  | zero => exact ⟨1, by ext t; simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨2 * X ^ 3 * p - X ^ 2 * p.derivative, ?_⟩
    rw [iteratedDeriv_succ, hp]
    exact funext fun t => (polynomial_hasDeriv p t).deriv

theorem polynomial_derivatives :
    Specs.D13Unified.Ch06.SmoothNonanalyticExample.polynomialDerivativesExpected := by
  intro n
  obtain ⟨p, hp⟩ := iterated_polynomial n
  exact ⟨p, fun t ht => by change iteratedDeriv n g t = _; simp only [hp, g_of_pos ht]⟩

theorem derivative_limits :
    Specs.D13Unified.Ch06.SmoothNonanalyticExample.derivativeLimitsExpected := by
  intro n
  obtain ⟨p, hp⟩ := iterated_polynomial n
  change Tendsto (iteratedDeriv n g) _ _
  rw [hp]
  exact (polynomial_limit p).mono_left nhdsWithin_le_nhds

theorem flat_forcing :
    Specs.D13Unified.Ch06.SmoothNonanalyticExample.flatForcingExpected := by
  intro n
  obtain ⟨p, hp⟩ := iterated_polynomial n
  change iteratedDeriv n g 0 = 0
  simp only [hp, g_of_nonpos le_rfl, mul_zero]

lemma x_hasDeriv (t : ℝ) : HasDerivAt x (g t) t := by
  have hc : Continuous g := smooth.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma deriv_x : deriv x = g := funext fun t => (x_hasDeriv t).deriv

lemma x_smooth : ContDiff ℝ ∞ x := by
  apply contDiff_infty_iff_deriv.2
  exact ⟨fun t => (x_hasDeriv t).differentiableAt, deriv_x.symm ▸ smooth⟩

lemma x_zero : x 0 = 0 := by simp [x, Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue]

theorem smooth_ivp : Specs.D13Unified.Ch06.SmoothNonanalyticExample.smoothIVPExpected :=
  ⟨x_smooth, x_zero, x_hasDeriv⟩

/-- This is precisely the scalar variation-of-constants theorem with a=0. -/
theorem unique_ivp : Specs.D13Unified.Ch06.SmoothNonanalyticExample.uniqueIVPExpected := by
  intro I hs
  have h := ScalarLinear.variation_of_constants I (fun _ : ℝ => (0 : ℝ)) g 0 0
    continuousOn_const smooth.continuous.continuousOn hs
  have hv : ScalarLinear.variation (fun _ : ℝ => (0 : ℝ)) g 0 0 = x := by
    ext t
    simp [ScalarLinear.variation, ScalarLinear.primitive, x,
      Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue, g]
  rw [hv] at h
  exact h

theorem flat_solution : Specs.D13Unified.Ch06.SmoothNonanalyticExample.flatSolutionExpected := by
  intro n
  change iteratedDeriv n x 0 = 0
  cases n with
  | zero => simpa using x_zero
  | succ n => rw [iteratedDeriv_succ', deriv_x]; exact flat_forcing n

theorem positive_solution :
    Specs.D13Unified.Ch06.SmoothNonanalyticExample.positiveSolutionExpected := by
  intro t ht
  apply intervalIntegral.integral_pos ht smooth.continuous.continuousOn
  · intro r _; exact g_nonneg r
  · refine ⟨t, ⟨ht.le, le_rfl⟩, ?_⟩
    change 0 < g t
    rw [g_of_pos ht]
    exact exp_pos _

theorem zero_taylor : Specs.D13Unified.Ch06.SmoothNonanalyticExample.zeroTaylorExpected := by
  have hf : ∀ n : ℕ, iteratedDeriv n
      Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue 0 = 0 := flat_solution
  constructor
  · intro n; rw [hf n, zero_div]
  · intro t
    simp only [hf, zero_div, zero_mul]
    exact hasSum_zero

theorem taylor_failure :
    Specs.D13Unified.Ch06.SmoothNonanalyticExample.taylorFailureExpected := by
  intro ε hε
  refine ⟨ε / 2, ?_, ?_⟩
  · rw [abs_of_pos (half_pos hε)]; exact half_lt_self hε
  · intro hs
    have heq := hs.unique (zero_taylor.2 (ε / 2))
    exact (positive_solution (ε / 2) (half_pos hε)).ne' heq

theorem nonanalytic : Specs.D13Unified.Ch06.SmoothNonanalyticExample.nonanalyticExpected := by
  intro ha
  have hp := ha.hasFPowerSeriesAt
  have hz : FormalMultilinearSeries.ofScalars ℝ
      (fun n => iteratedDeriv n
        Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue 0 / (n.factorial : ℝ)) = 0 := by
    have hf : ∀ n : ℕ, iteratedDeriv n
        Specs.D13Unified.Ch06.SmoothNonanalyticExample.xValue 0 = 0 := flat_solution
    ext n
    simp [hf]
  rw [hz] at hp
  have he := hp.eventually_eq_zero
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  have hpos := positive_solution (ε / 2) (half_pos hε)
  have heq := he (show dist (ε / 2) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  exact hpos.ne' heq

end D13Unified.SmoothNonanalytic
