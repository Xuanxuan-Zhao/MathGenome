import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.JordanEstimate
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PiecewiseC1Length
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace D12Complex.JordanEstimate

/-- The upper semicircle is the canonical path defined in the independent Spec. -/
abbrev semicircle := upperSemicircle

lemma semicircle_speed (r t : ℝ) (hr : 0 ≤ r) :
    ‖deriv (upperSemicircle r : ℝ → ℂ) t‖ = r := by
  change ‖deriv (circleMap 0 r) t‖ = r
  simp [deriv_circleMap, norm_circleMap_zero, abs_of_nonneg hr]

lemma exp_norm_on_semicircle (r c t : ℝ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * upperSemicircle r t)‖ =
      Real.exp (-c * r * Real.sin t) := by
  rw [Complex.norm_exp]
  change Real.exp ((Complex.I * (c : ℂ) * circleMap 0 r t).re) = _
  congr 1
  simp [Complex.mul_re, Complex.mul_im, circleMap_zero_im]
  ring

/-- The elementary exponential majorant on half the angular interval. -/
lemma half_integral_bound (a : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.exp (-a * Real.sin t)) ≤
      Real.pi / (2 * a) := by
  let k := -a * (2 / Real.pi)
  have hk : k < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos ha)
    (div_pos (by norm_num) Real.pi_pos)
  have hmajor : (∫ t in (0 : ℝ)..Real.pi / 2, Real.exp (-a * Real.sin t)) ≤
      ∫ t in (0 : ℝ)..Real.pi / 2, Real.exp (k * t) := by
    apply intervalIntegral.integral_mono_on Real.pi_div_two_pos.le
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro t ht
    apply Real.exp_le_exp.mpr
    have hs := Real.mul_le_sin ht.1 ht.2
    dsimp [k]
    nlinarith
  have heval : (∫ t in (0 : ℝ)..Real.pi / 2, Real.exp (k * t)) =
      (1 - Real.exp (k * (Real.pi / 2))) / (-k) := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp hk.ne,
      integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
    ring
  have hbound : (1 - Real.exp (k * (Real.pi / 2))) / (-k) ≤ 1 / (-k) := by
    apply div_le_div_of_nonneg_right _ (neg_nonneg.mpr hk.le)
    linarith [Real.exp_pos (k * (Real.pi / 2))]
  calc
    _ ≤ _ := hmajor
    _ = _ := heval
    _ ≤ _ := hbound
    _ = Real.pi / (2 * a) := by dsimp [k]; field_simp

lemma angular_integral_bound (a : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..Real.pi, Real.exp (-a * Real.sin t)) ≤ Real.pi / a := by
  have hcont : Continuous (fun t => Real.exp (-a * Real.sin t)) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (a := 0) (b := Real.pi / 2))
    (hcont.intervalIntegrable (μ := volume) (a := Real.pi / 2) (b := Real.pi))
  have hsymm : (∫ t in Real.pi / 2..Real.pi, Real.exp (-a * Real.sin t)) =
      ∫ t in (0 : ℝ)..Real.pi / 2, Real.exp (-a * Real.sin t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun t => Real.exp (-a * Real.sin t)) (a := Real.pi / 2) (b := Real.pi) Real.pi
    simpa only [Real.sin_pi_sub, sub_self, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] using h
  rw [← hsplit, hsymm]
  have hb := half_integral_bound a ha
  calc
    _ ≤ 2 * (Real.pi / (2 * a)) := by linarith
    _ = Real.pi / a := by ring

theorem jordan_estimate : Specs.D12Complex.Ch08.JordanEstimate.jordan_estimate_type := by
  intro r c hr hc q hq
  let γ := upperSemicircle r
  let M := γ.traceSupNorm q
  have hM : 0 ≤ M := (norm_nonneg (q (γ 0))).trans
    (PiecewiseC1Length.norm_le_traceSupNorm γ q hq ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, rfl⟩)
  have hqp : ContinuousOn (fun t => q (γ t)) (Icc 0 Real.pi) :=
    hq.comp γ.path.continuousOn (fun t ht => ⟨t, ht, rfl⟩)
  have hf : ContinuousOn (fun z => Complex.exp (Complex.I * (c : ℂ) * z) * q z) γ.trace :=
    (by fun_prop : Continuous (fun z : ℂ => Complex.exp (Complex.I * (c : ℂ) * z))).continuousOn.mul hq
  have hcont : Continuous (fun t => Real.exp (-c * r * Real.sin t)) := by fun_prop
  calc
    _ ≤ ∫ t in (0 : ℝ)..Real.pi,
        ‖Complex.exp (Complex.I * (c : ℂ) * γ t) * q (γ t)‖ * ‖deriv (γ : ℝ → ℂ) t‖ :=
      (PiecewiseC1Length.contour_estimates γ _ hf).1
    _ = ∫ t in (0 : ℝ)..Real.pi, Real.exp (-c * r * Real.sin t) * ‖q (γ t)‖ * r := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [norm_mul, semicircle_speed r t hr.le, exp_norm_on_semicircle]
    _ ≤ ∫ t in (0 : ℝ)..Real.pi, Real.exp (-c * r * Real.sin t) * M * r := by
      apply intervalIntegral.integral_mono_on Real.pi_pos.le
        (((hcont.continuousOn.mul hqp.norm).mul_const r).intervalIntegrable_of_Icc Real.pi_pos.le)
        ((hcont.mul_const M |>.mul_const r).intervalIntegrable 0 Real.pi)
      intro t ht
      apply mul_le_mul_of_nonneg_right _ hr.le
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact PiecewiseC1Length.norm_le_traceSupNorm γ q hq ⟨t, ht, rfl⟩
    _ = (r * M) * (∫ t in (0 : ℝ)..Real.pi, Real.exp (-c * r * Real.sin t)) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
      ring
    _ ≤ (r * M) * (Real.pi / (c * r)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr.le hM)
      simpa only [neg_mul] using angular_integral_bound (c * r) (mul_pos hc hr)
    _ = (Real.pi / c) * M := by field_simp

theorem jordan_integral_tendsto_zero :
    Specs.D12Complex.Ch08.JordanEstimate.jordan_integral_tendsto_zero_type := by
  intro c hc q hq hlim
  apply squeeze_zero_norm' (a := fun r => (Real.pi / c) * (upperSemicircle r).traceSupNorm (q r))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact jordan_estimate r c hr hc (q r) (hq r hr)
  · simpa using hlim.const_mul (Real.pi / c)
end D12Complex.JordanEstimate
