import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.ScalarError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalTaylor
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import Mathlib.Tactic.FieldSimp

/-! The single-step Taylor estimate used in W73. Regularity is required only
on an open neighborhood of the certified interval, and the output point is
not assumed to belong to that interval. -/
namespace NumAnalysis206.Newton
open Set NumAnalysis206.Approximation

private theorem open_interval_jet {f : ℝ → ℝ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    IntervalJet a b 2 f (fun j => iteratedDeriv j f) := by
  refine ⟨by intro t ht; simp, ?_, ?_⟩
  · intro j hj
    have hc := hf.continuousOn_iteratedDerivWithin (m := j)
      (by exact_mod_cast hj) hU.uniqueDiffOn
    exact (hc.congr (iteratedDerivWithin_of_isOpen hU).symm).mono hsub
  · intro j hj t ht
    have hd := hf.differentiableOn_iteratedDerivWithin (m := j)
      (by exact_mod_cast hj) hU.uniqueDiffOn
    have hd' : DifferentiableOn ℝ (iteratedDeriv j f) U :=
      hd.congr (iteratedDerivWithin_of_isOpen hU).symm
    dsimp only
    rw [iteratedDeriv_succ]
    exact ((hd' t (hsub ht)).differentiableAt (hU.mem_nhds (hsub ht))).hasDerivAt.hasDerivWithinAt

private theorem stopped_scalar_eq (f : ℝ → ℝ) (x : ℝ) :
    Specs.NumAnalysis206.Newton.stopAtRootValue f
      (Specs.NumAnalysis206.Newton.scalarNewtonValue f) x =
      Specs.NumAnalysis206.Newton.scalarNewtonValue f x := by
  by_cases hx : f x = 0
  · simp [Specs.NumAnalysis206.Newton.stopAtRootValue,
      Specs.NumAnalysis206.Newton.scalarNewtonValue, hx]
  · exact stopAtRoot_of_nonroot f (Specs.NumAnalysis206.Newton.scalarNewtonValue f) x hx

/-- Every input in the certified interval has a valid Newton step and the
quadratic error bound. This is a one-step result, without an invariance assumption. -/
theorem scalarNewton_step_error : Specs.NumAnalysis206.Newton.ScalarError.stepError := by
  intro f p R m M U hR hU hsub hf hp hm hslope hcurv x hx
  have hden : deriv f x ≠ 0 := by
    have hpos := hm.trans_le (hslope x hx)
    exact abs_pos.mp hpos
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num) x (hsub hx)).differentiableAt
      (hU.mem_nhds (hsub hx))
  refine ⟨⟨hdiff, hden⟩, ?_⟩
  have hab : p - R ≤ p + R := by linarith
  have hpI : p ∈ Icc (p - R) (p + R) := ⟨by linarith, by linarith⟩
  have hjet := open_interval_jet hU hsub hf
  have hTaylor := jet_taylor_bound hab (by norm_num : 1 ≤ 2) hjet hx hpI
    (fun t ht => by
      have htI : t ∈ Icc (p - R) (p + R) :=
        uIcc_subset_Icc hx hpI ht
      simpa [iteratedDeriv_succ] using hcurv t htI)
  have hsum : jetTaylorSum (fun j => iteratedDeriv j f) 2 x p =
      f x + deriv f x * (p - x) := by
    simp [jetTaylorSum, NumAnalysis206.Approximation.IntervalTaylorSpec.sumValue,
      Finset.sum_range_succ, iteratedDeriv_succ]
  have hrem : |f x + deriv f x * (p - x)| ≤ M * |x - p| ^ 2 / 2 := by
    simpa only [hsum, hp, zero_sub, abs_neg, abs_sub_comm p x,
      show (2 : ℕ).factorial = 2 from rfl, Nat.cast_ofNat] using hTaylor
  have heq : Specs.NumAnalysis206.Newton.scalarNewtonValue f x - p =
      -(f x + deriv f x * (p - x)) / deriv f x := by
    unfold Specs.NumAnalysis206.Newton.scalarNewtonValue
    field_simp [hden]
    ring
  rw [heq, abs_div, abs_neg]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcurv p hpI)
  calc
    |f x + deriv f x * (p - x)| / |deriv f x| ≤
        (M * |x - p| ^ 2 / 2) / m :=
      div_le_div₀ (by positivity) hrem hm (hslope x hx)
    _ = M * |x - p| ^ 2 / (2 * m) := by ring

/-- Successful root stopping agrees with the exact Newton expression and
inherits its single-step certificate. -/
theorem scalarNewton_stopped_step_error :
    Specs.NumAnalysis206.Newton.ScalarError.stoppedStepError := by
  intro f p R m M U hR hU hsub hf hp hm hslope hcurv x hx
  obtain ⟨hv, he⟩ := scalarNewton_step_error f p R m M U hR hU hsub hf hp hm hslope hcurv x hx
  refine ⟨Or.inr hv, ?_⟩
  rw [stopped_scalar_eq]
  exact he

/-- When the second derivative bound is zero, a single step reaches the root. -/
theorem scalarNewton_step_zero_curvature :
    Specs.NumAnalysis206.Newton.ScalarError.zeroCurvature := by
  intro f p R m U hR hU hsub hf hp hm hslope hcurv x hx
  have he := (scalarNewton_step_error f p R m 0 U hR hU hsub hf hp hm hslope hcurv x hx).2
  have hz : Specs.NumAnalysis206.Newton.scalarNewtonValue f x = p := by
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa using he) (abs_nonneg _)
  refine ⟨hz, ?_⟩
  rw [stopped_scalar_eq, hz]

end NumAnalysis206.Newton
