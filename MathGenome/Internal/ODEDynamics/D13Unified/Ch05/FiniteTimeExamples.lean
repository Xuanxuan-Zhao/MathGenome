import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.ScalarLinear
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.QuadraticBlowup
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.FiniteTimeExamples
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch05.FiniteTimeExamples
open Specs.D13Unified.Ch05.FiniteTimeExamples
open D13Unified.Ch04.QuadraticBlowup

@[simp] lemma growthODE_eval (t x : ℝ) : growthODE.eval t x = x := by
  simp [ODE.eval, growthODE]

lemma growth_deriv (ξ t : ℝ) : HasDerivAt (growthCurve ξ) (growthCurve ξ t) t := by
  convert! (Real.hasDerivAt_exp t).const_mul ξ using 1

lemma growth_ivp (ξ : ℝ) : IsClassicalIVPOn growthODE wholeTime (growthCurve ξ) 0 ξ := by
  refine ⟨(classical_iff_solutionOn _ _ _).mpr ?_, mem_univ _, ?_⟩
  · exact ⟨fun t _ => (growth_deriv ξ t).continuousAt.continuousWithinAt,
      fun _ _ => mem_univ _, fun t _ => by
        simpa only [growthODE_eval] using (growth_deriv ξ t).hasDerivWithinAt⟩
  · simp [growthCurve]

theorem growth_solutions : growthSolutionsExpected := by
  intro ξ
  refine ⟨growth_ivp ξ, ?_⟩
  intro J y hy
  have hlin : ScalarLinear.IsIVP J.toTimeInterval (fun _ => 1) (fun _ => 0) 0 ξ y := by
    refine ⟨hy.1.1.continuousOn, hy.2.1, hy.2.2, ?_⟩
    intro t ht
    simpa only [growthODE_eval, one_mul, add_zero] using (hy.1.2.2 t ht).hasDerivWithinAt
  have hg : ScalarLinear.IsIVP J.toTimeInterval (fun _ => 1) (fun _ => 0) 0 ξ
      (growthCurve ξ) := by
    refine ⟨fun t _ => (growth_deriv ξ t).continuousAt.continuousWithinAt,
      hy.2.1, ?_, ?_⟩
    · simp [growthCurve]
    · intro t _
      simpa only [one_mul, add_zero] using (growth_deriv ξ t).hasDerivWithinAt
  exact (ScalarLinear.eq_variation_of_isIVP _ _ _ _ _ continuousOn_const
    continuousOn_const hlin).trans
      (ScalarLinear.eq_variation_of_isIVP _ _ _ _ _ continuousOn_const
        continuousOn_const hg).symm

theorem difference : differenceExpected := by
  intro ε t
  simp [growthCurve]

theorem compact_convergence : compactConvergenceExpected := by
  intro a b
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have he : 0 < Real.exp b := Real.exp_pos b
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hη he)] with ε hε t ht
  have hε' : |ε| < η / Real.exp b := by simpa [Real.dist_eq] using hε
  have hb := Real.exp_le_exp.mpr ht.2
  rw [difference, Real.dist_eq, zero_sub, abs_neg, abs_mul, abs_of_pos (Real.exp_pos t)]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg ε)).trans_lt
    ((lt_div_iff₀ he).mp hε')

/-- Every nonzero perturbation eventually exceeds any prescribed size on
nonnegative time. This supplies a witness for the failure of uniformity. -/
lemma growth_unbounded (ε : ℝ) (hε : ε ≠ 0) (M : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ M < |growthCurve ε t - growthCurve 0 t| := by
  have hlim : Tendsto (fun t : ℝ => |ε| * Real.exp t) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (abs_pos.mpr hε)
  obtain ⟨t, ht⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (eventually_gt_atTop M))).exists
  refine ⟨t, ht.1, ?_⟩
  rw [difference, abs_mul, abs_of_pos (Real.exp_pos t)]
  exact ht.2

theorem non_uniform : nonUniformExpected := by
  intro h
  have hev := Metric.tendstoUniformlyOn_iff.mp h 1 zero_lt_one
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hε := hball (y := δ / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)]
    linarith)
  obtain ⟨t, ht, hgt⟩ := growth_unbounded (δ / 2) (by positivity) 1
  have hlt := hε t ht
  rw [Real.dist_eq, zero_sub, abs_neg] at hlt
  linarith

/-- The denominator stays positive on a fixed finite interval for all data in
one neighborhood of zero, including negative and zero data. -/
lemma quadratic_interval_contains (a b ξ : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b)
    (hξ : |ξ| < 1 / (|a| + |b| + 1)) :
    Icc a b ⊆ (quadraticInterval 0 ξ).carrier := by
  have hC : 0 < |a| + |b| + 1 := by positivity
  have hp : |ξ| * (|a| + |b| + 1) < 1 := (lt_div_iff₀ hC).mp hξ
  intro t ht
  have htabs : |t| ≤ |a| + |b| := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hprod : |ξ * t| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (by linarith : |t| ≤ |a| + |b| + 1)
      (abs_nonneg ξ)).trans_lt hp
  have hupper : t * ξ < 1 := by linarith [le_abs_self (ξ * t)]
  by_cases hpos : 0 < ξ
  · simpa [quadraticInterval, hpos] using (lt_div_iff₀ hpos).mpr hupper
  · by_cases hneg : ξ < 0
    · simpa [quadraticInterval, hpos, hneg] using (div_lt_iff_of_neg hneg).mpr hupper
    · simp [quadraticInterval, hpos, hneg]

theorem quadratic_common_interval : quadraticCommonIntervalExpected := by
  intro a b ha hb
  refine ⟨1 / (|a| + |b| + 1), by positivity, ?_⟩
  intro ξ hξ
  have hsub := quadratic_interval_contains a b ξ ha hb hξ
  refine ⟨?_, ?_, ?_⟩
  · rw [(solution 0 ξ).2.1]
    exact hsub
  · refine ⟨ha.trans hb, ?_, fun _ _ => mem_univ _, ?_⟩
    · intro t ht
      exact (curve_hasDerivAt 0 ξ (hsub ht)).continuousAt.continuousWithinAt
    · intro t ht
      simpa only [quadraticODE_eval] using
        (curve_hasDerivAt 0 ξ (hsub ht)).hasDerivWithinAt
  · simp [quadraticCurve]

theorem quadratic_finite_lifespan : quadraticFiniteLifespanExpected := by
  intro ξ hξ
  refine ⟨?_, one_div_pos.mpr hξ, ?_⟩
  · rw [(solution 0 ξ).2.1]
    simp [quadraticInterval, hξ]
  · have hlim : Tendsto (quadraticCurve 0 ξ) (𝓝[<] (1 / ξ)) atTop := by
      simpa only [zero_add] using (endpoints 0 ξ).1 hξ
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((solution 0 ξ).2.2.1 (by simpa [quadraticInterval, hξ] using ht)).symm

end D13Unified.Ch05.FiniteTimeExamples
