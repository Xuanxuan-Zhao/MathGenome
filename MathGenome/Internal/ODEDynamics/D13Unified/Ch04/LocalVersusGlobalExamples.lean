import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.LocalVersusGlobalExamples
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.QuadraticBlowup
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.LinearGrowth
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace D13Unified.Ch04.LocalVersusGlobalExamples
open Specs.D13Unified.Ch04.LocalVersusGlobalExamples

@[simp] lemma sineSquareODE_eval (t x : ℝ) :
    sineSquareODE.eval t x = Real.sin (x ^ 2) := by
  simp [ODE.eval, sineSquareODE]

theorem quadratic_example : quadraticExpected := by
  refine ⟨QuadraticBlowup.regularity.2, ?_⟩
  intro s ξ hξ
  have hI : (QuadraticBlowup.quadraticInterval s ξ).carrier = Iio (s + 1 / ξ) := by
    simp [QuadraticBlowup.quadraticInterval, hξ]
  refine ⟨(QuadraticBlowup.solution s ξ).1, hI,
    (QuadraticBlowup.endpoints s ξ).1 hξ, ?_⟩
  intro y hs hy hm
  obtain ⟨hd, he⟩ := (QuadraticBlowup.maximality s ξ).2 y hs hy hm
  refine ⟨hd.trans hI, ?_⟩
  apply ((QuadraticBlowup.endpoints s ξ).1 hξ).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (he (by rw [hd, hI]; exact ht)).symm

theorem sine_regularity : sineRegularityExpected := by
  have h : ContDiff ℝ ∞ (fun z : ℝ × ℝ => sineSquareODE.eval z.1 z.2) := by
    simpa only [sineSquareODE_eval] using (contDiff_snd.pow 2).sin
  exact ⟨h, sineSquareODE.locallyLipschitzInState_of_contDiffOn
    (h.of_le (by simp)).contDiffOn⟩

theorem sine_bounded : sineBoundedExpected := by
  intro x
  exact Real.abs_sin_le_one _

theorem sine_derivative : sineDerivativeExpected := by
  intro x
  convert ((hasDerivAt_id x).pow 2).sin using 1 <;> simp <;> ring

theorem sine_derivative_unbounded : sineDerivativeUnboundedExpected := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2)
  let x := Real.sqrt ((n : ℝ) * (2 * Real.pi))
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = (n : ℝ) * (2 * Real.pi) :=
    Real.sq_sqrt (by positivity)
  have hbig : M < x := by
    have hp := Real.two_le_pi
    have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt (sq_nonneg M) hn
    nlinarith
  refine ⟨x, ?_⟩
  rw [(sine_derivative x).deriv, hx2, Real.cos_nat_mul_two_pi, mul_one,
    abs_of_nonneg (by positivity : 0 ≤ 2 * x)]
  linarith

theorem sine_not_globally_lipschitz : sineNotGloballyLipschitzExpected := by
  rintro ⟨L, hL⟩
  obtain ⟨x, hx⟩ := sine_derivative_unbounded L
  have hb : ‖deriv (fun y : ℝ => Real.sin (y ^ 2)) x‖ ≤ (L : ℝ) :=
    norm_deriv_le_of_lipschitz hL
  exact (not_lt_of_ge hb) hx

theorem sine_global : sineGlobalExpected := by
  have hg : ∀ x : Solution sineSquareODE,
      Specs.D13Unified.Ch01.SolutionConcepts.maximalValue x →
      Specs.D13Unified.Ch01.SolutionConcepts.globalValue x := by
    apply LinearGrowth.global_existence sineSquareODE sine_regularity.2 rfl
    intro B hB
    refine ⟨1, 0, zero_le_one, le_rfl, ?_⟩
    intro r hr y
    simpa only [sineSquareODE_eval, Real.norm_eq_abs, zero_mul, add_zero] using sine_bounded y
  refine ⟨hg, ?_⟩
  intro s ξ
  obtain ⟨hc, hs, hξ, hm, _, hrestrict, _⟩ :=
    ODE.canonical_solution sineSquareODE sine_regularity.2 s ξ (mem_univ _)
  let x : Solution sineSquareODE :=
    ⟨Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue sineSquareODE s ξ,
      Specs.D13Unified.Ch04.MaximalSolutionMap.solutionCurveValue sineSquareODE s ξ, hc⟩
  exact ⟨x, hs, hξ, hg x hm, hrestrict⟩

end D13Unified.Ch04.LocalVersusGlobalExamples
