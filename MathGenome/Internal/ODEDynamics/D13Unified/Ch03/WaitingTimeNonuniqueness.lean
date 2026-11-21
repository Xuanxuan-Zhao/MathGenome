import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.WaitingTimeNonuniqueness
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The waiting-time nonuniqueness example (paper.tex, d13:03:nonunique).
The join is proved by matching the two within derivatives. Continuity of
`2 * max (t-a) 0` supplies C¹ regularity. For the failure of local Lipschitz
control, positive states `x = y²` give quotients `2/y`, arbitrarily large
with arbitrarily small positive `y`.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.WaitingTime
open Specs.D13Unified.Ch03.WaitingTimeNonuniqueness

@[simp] theorem equation_eval (t x : ℝ) : equation.eval t x = field x := by
  rw [ODE.eval_of_mem equation (mem_univ _)]
  rfl

@[simp] theorem curve_of_le {a t : ℝ} (h : t ≤ a) : curve a t = 0 := by
  simp [curve, h]

theorem curve_of_ge {a t : ℝ} (h : a ≤ t) : curve a t = (t - a) ^ 2 := by
  rcases h.eq_or_lt with rfl | h
  · simp [curve]
  · simp [curve, not_le.mpr h]

theorem field_continuous : fieldContinuousExpected := by
  unfold fieldContinuousExpected field
  fun_prop

private theorem polynomial_derivative (a t : ℝ) :
    HasDerivAt (fun r : ℝ => (r - a) ^ 2) (2 * (t - a)) t := by
  simpa using ((hasDerivAt_id t).sub_const a).fun_pow 2

theorem curve_join_derivative : joinDerivativeExpected := by
  intro a
  have hl : HasDerivWithinAt (curve a) 0 (Iic a) a := by
    apply (hasDerivAt_const a (0 : ℝ)).hasDerivWithinAt.congr_of_mem
    · intro t ht
      exact curve_of_le ht
    · exact (show a ≤ a from le_rfl)
  have hr : HasDerivWithinAt (curve a) 0 (Ici a) a := by
    have hp : HasDerivAt (fun r : ℝ => (r - a) ^ 2) 0 a := by
      simpa using polynomial_derivative a a
    apply hp.hasDerivWithinAt.congr_of_mem
    · intro t ht
      exact curve_of_ge ht
    · exact (show a ≤ a from le_rfl)
  have hu := hl.union hr
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hu

theorem curve_hasDerivAt : curveDerivativeExpected := by
  intro a t
  rcases lt_trichotomy t a with h | rfl | h
  · have hc : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have he : curve a =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds h] with r hr
      exact curve_of_le hr.le
    simpa only [max_eq_right (sub_nonpos.mpr h.le), mul_zero] using
      hc.congr_of_eventuallyEq he
  · simpa using curve_join_derivative t
  · have he : curve a =ᶠ[𝓝 t] (fun r => (r - a) ^ 2) := by
      filter_upwards [eventually_gt_nhds h] with r hr
      exact curve_of_ge hr.le
    simpa only [max_eq_left (sub_nonneg.mpr h.le)] using
      (polynomial_derivative a t).congr_of_eventuallyEq he

private theorem curve_contDiff (a : ℝ) : ContDiff ℝ 1 (curve a) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (curve_hasDerivAt a t).differentiableAt, ?_⟩
  have hd : deriv (curve a) = fun t => 2 * max (t - a) 0 := by
    funext t
    exact (curve_hasDerivAt a t).deriv
  rw [hd]
  fun_prop

private theorem field_curve (a t : ℝ) : field (curve a t) = 2 * max (t - a) 0 := by
  by_cases h : t ≤ a
  · simp [curve_of_le h, field, max_eq_right (sub_nonpos.mpr h)]
  · have h' : 0 ≤ t - a := sub_nonneg.mpr (le_of_not_ge h)
    rw [curve_of_ge (le_of_not_ge h)]
    simp [field, abs_of_nonneg (sq_nonneg (t - a)), Real.sqrt_sq h', max_eq_left h']

theorem curve_global_ivp : globalIVPExpected := by
  intro a ha
  refine ⟨⟨(curve_contDiff a).contDiffOn, ?_, ?_⟩, mem_univ _, curve_of_le ha⟩
  · intro t ht
    exact mem_univ _
  · intro t ht
    rw [equation_eval, field_curve]
    exact curve_hasDerivAt a t

theorem zero_global_ivp : zeroGlobalIVPExpected := by
  refine ⟨⟨contDiff_const.contDiffOn, ?_, ?_⟩, mem_univ _, rfl⟩
  · intro t ht
    exact mem_univ _
  · intro t ht
    simpa [field] using hasDerivAt_const t (0 : ℝ)

theorem curves_distinct : distinctExpected := by
  intro a b hab heq
  have h := congrFun heq b
  rw [curve_of_ge hab.le, curve_of_le le_rfl] at h
  nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]

theorem curve_ne_zero : distinctFromZeroExpected := by
  intro a heq
  have h := congrFun heq (a + 1)
  rw [curve_of_ge (by linarith)] at h
  norm_num at h

theorem nonunique_global_ivp : nonuniqueExpected := by
  exact ⟨curve 0, curve 1, curve_global_ivp 0 le_rfl,
    curve_global_ivp 1 (by norm_num), curves_distinct 0 1 (by norm_num)⟩

theorem field_quotient : quotientExpected := by
  intro x hx
  have hs := Real.sqrt_pos.mpr hx
  have hs2 := Real.sq_sqrt hx.le
  simp only [field, abs_zero, Real.sqrt_zero, mul_zero, sub_zero,
    abs_of_pos hx, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le)]
  apply (div_eq_div_iff (ne_of_gt hx) (ne_of_gt hs)).mpr
  nlinarith

theorem quotient_unbounded : quotientUnboundedExpected := by
  intro ε hε M
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hM : 0 < |M| + 1 := by positivity
  obtain ⟨y, hy, hymin⟩ := exists_between
    (lt_min hs (div_pos (by norm_num : (0 : ℝ) < 1) hM))
  have hys : y < Real.sqrt ε := (lt_min_iff.mp hymin).1
  have hym : y < 1 / (|M| + 1) := (lt_min_iff.mp hymin).2
  have hprod : y * (|M| + 1) < 1 := (lt_div_iff₀ hM).mp hym
  refine ⟨y ^ 2, sq_pos_of_pos hy, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt hε.le]
  · rw [field_quotient _ (sq_pos_of_pos hy), Real.sqrt_sq hy.le]
    apply (lt_div_iff₀ hy).mpr
    have hle : M * y ≤ |M| * y :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hy.le
    nlinarith

theorem no_local_state_bound : noLocalBoundExpected := by
  intro a b L ha hb hL hbound
  obtain ⟨x, hx, hxb, hquot⟩ := quotient_unbounded b hb L
  have hxb' : x ∈ Metric.ball (0 : ℝ) b := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx] using hxb
  have h := hbound 0 (Metric.mem_ball_self ha) x hxb' 0 (Metric.mem_ball_self hb)
  simp only [equation_eval, Real.norm_eq_abs, sub_zero] at h
  have hq : |field x - field 0| / |x| ≤ L :=
    (div_le_iff₀ (abs_pos.mpr (ne_of_gt hx))).mpr h
  exact (not_lt_of_ge hq) hquot

theorem not_locally_lipschitz : notLocallyLipschitzExpected := by
  intro h
  obtain ⟨a, b, L, ha, hb, hL, _, hbound⟩ := h 0 0 (mem_univ _)
  exact no_local_state_bound a b L ha hb hL hbound

end D13Unified.WaitingTime
