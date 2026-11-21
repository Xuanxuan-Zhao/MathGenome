import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.SmoothFlatExample
import MathGenome.Internal.MultivariableAnalysis.D04.C03.TaylorPeano
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff
namespace D04
abbrev flatFunction : ℝ → ℝ := Specs.D04.C03.SmoothFlatExample.Model.flatFunction

@[simp] theorem flatFunction_zero : flatFunction 0 = 0 := by
  simp [flatFunction, Specs.D04.C03.SmoothFlatExample.Model.flatFunction]

theorem flatFunction_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    flatFunction x = Real.exp (-1 / x^2) := by
  simp [flatFunction, Specs.D04.C03.SmoothFlatExample.Model.flatFunction, hx]

theorem flatFunction_eq_glue : flatFunction = fun x : ℝ => expNegInvGlue (x^2) := by
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · rw [flatFunction_of_ne_zero hx]
    simp [expNegInvGlue, (sq_pos_of_ne_zero hx).not_ge, div_eq_mul_inv]

theorem flatFunction_contDiff : ContDiff ℝ ∞ flatFunction := by
  rw [flatFunction_eq_glue]
  exact expNegInvGlue.contDiff.comp (contDiff_id.pow 2)

theorem flatFunction_smooth : SmoothOn Set.univ flatFunction := by
  exact (smoothOn_iff_contDiffOn Set.univ flatFunction isOpen_univ).mpr
    flatFunction_contDiff.contDiffOn

theorem flatFunction_pos (x : ℝ) (hx : x ≠ 0) : 0 < flatFunction x := by
  rw [flatFunction_of_ne_zero hx]
  exact Real.exp_pos _

-- The inverse squared distance goes to +infinity on both sides of zero.
theorem tendsto_inv_sq_zero : Tendsto (fun x : ℝ => (x^2)⁻¹) (𝓝[≠] 0) atTop := by
  have h := (tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)).comp
    (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℝ))
  change Tendsto (fun x : ℝ => ‖x⁻¹‖^2) (𝓝[≠] 0) atTop at h
  simpa only [Real.norm_eq_abs, sq_abs, inv_pow] using h

theorem flatFunction_integer_decay (N : ℤ) :
    Tendsto (fun x : ℝ => |x| ^ (-N) * Real.exp (-1 / x^2)) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((N : ℝ) / 2) 1 (by norm_num)).comp tendsto_inv_sq_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : x ≠ 0 := hx
  have habs : 0 < |x| := abs_pos.mpr hx
  have he : ((x^2)⁻¹) ^ ((N : ℝ) / 2) = |x| ^ (-N) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul habs.le,
      ← Real.rpow_mul habs.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-2 : ℝ) * ((N : ℝ) / 2) = ((-N : ℤ) : ℝ) by push_cast; ring]
    exact Real.rpow_intCast _ _
  simp only [Function.comp_apply, he, neg_mul, one_mul, neg_div, one_div]

/-- Multiplication by any inverse monomial still has zero limit. -/
theorem flatFunction_monomial_decay (n : ℕ) :
    Tendsto (fun x : ℝ => (x⁻¹)^n * flatFunction x) (𝓝 0) (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => (x⁻¹)^n * flatFunction x) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply (flatFunction_integer_decay (n : ℤ)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [flatFunction_of_ne_zero hx]
    simp [norm_mul, norm_pow, norm_inv, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), zpow_neg, zpow_natCast, inv_pow]
  have hc : ContinuousAt (fun x : ℝ => (x⁻¹)^n * flatFunction x) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    simpa using hp
  simpa using hc.tendsto

/-- Finite polynomial expansion reduces the limit to inverse monomials. -/
theorem flatFunction_polynomial_decay (p : Polynomial ℝ) :
    Tendsto (fun x : ℝ => p.eval x⁻¹ * flatFunction x) (𝓝 0) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    simpa [Polynomial.eval_monomial, mul_assoc] using
      (flatFunction_monomial_decay n).const_mul c
  | add p q hp hq =>
    simpa [Polynomial.eval_add, add_mul] using hp.add hq

/-- The recurrence is valid also at zero, by the difference quotient and decay. -/
theorem flatFunction_polynomial_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => p.eval x⁻¹ * flatFunction x)
      ((2 * Polynomial.X^3 * p - Polynomial.X^2 * p.derivative).eval x⁻¹ * flatFunction x) x := by
  by_cases hx : x = 0
  · subst x
    rw [flatFunction_zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((flatFunction_polynomial_decay (p * Polynomial.X)).mono_left
      nhdsWithin_le_nhds).congr (fun y => ?_)
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have hd := ((p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx)).mul
      (((hasDerivAt_inv hx).pow 2).neg.exp)
    have he : (fun y : ℝ => p.eval y⁻¹ * Real.exp (-(y⁻¹)^2)) =ᶠ[𝓝 x]
        (fun y : ℝ => p.eval y⁻¹ * flatFunction y) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      rw [flatFunction_of_ne_zero hy]
      simp [div_eq_mul_inv, inv_pow]
    convert hd.congr_of_eventuallyEq he.symm using 1
    rw [flatFunction_of_ne_zero hx]
    simp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv, inv_pow, neg_mul,
      one_mul]
    ring

/-- A polynomial representation of each actual iterated derivative, globally. -/
theorem flatFunction_iteratedDeriv_representation (j : ℕ) :
    ∃ p : Polynomial ℝ, iteratedDeriv j flatFunction =
      fun x : ℝ => p.eval x⁻¹ * flatFunction x := by
  induction j with
  | zero => exact ⟨1, by ext x; simp⟩
  | succ j ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨2 * Polynomial.X^3 * p - Polynomial.X^2 * p.derivative, ?_⟩
    rw [iteratedDeriv_succ, hp]
    funext x
    exact (flatFunction_polynomial_hasDerivAt p x).deriv

theorem flatFunction_derivatives_zero (j : ℕ) : iteratedDeriv j flatFunction 0 = 0 := by
  obtain ⟨p, hp⟩ := flatFunction_iteratedDeriv_representation j
  simp [hp]

theorem flatFunction_derivative_polynomial (j : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ, x ≠ 0 →
      iteratedDeriv j flatFunction x = p.eval x⁻¹ * Real.exp (-1 / x^2) := by
  obtain ⟨p, hp⟩ := flatFunction_iteratedDeriv_representation j
  exact ⟨p, fun x hx => by simp only [hp, flatFunction_of_ne_zero hx]⟩

/-- The finite polynomial is the existing chapter-3 Taylor object. -/
theorem flatFunction_taylor_zero (k : ℕ) (h : ℝ) :
    taylorPolynomial k flatFunction 0 h = 0 := by
  rw [taylorPolynomial_scalar]
  simp [flatFunction_derivatives_zero]

/-- The Taylor series converges everywhere, with sum zero. -/
theorem flatFunction_taylor_series (x : ℝ) :
    HasSum (fun j : ℕ => iteratedDeriv j flatFunction 0 / (j.factorial : ℝ) * x^j) 0 := by
  simp [flatFunction_derivatives_zero]

/-- Every neighborhood contains a point where the function is positive. -/
theorem flatFunction_not_locally_zero : ¬ ∀ᶠ x in 𝓝 (0 : ℝ), flatFunction x = 0 := by
  intro hz
  have hz' : ∀ᶠ x : ℝ in 𝓝[≠] 0, flatFunction x = 0 :=
    hz.filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hne⟩ := (hz'.and (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ≠ 0)).exists
  exact (flatFunction_pos x hne).ne' hx

/-- Convergence of the Taylor series never represents f on a neighborhood of zero. -/
theorem flatFunction_no_taylor_neighborhood :
    ¬ ∃ U : Set ℝ, U ∈ 𝓝 0 ∧ ∀ x ∈ U,
      HasSum (fun j : ℕ => iteratedDeriv j flatFunction 0 / (j.factorial : ℝ) * x^j)
        (flatFunction x) := by
  rintro ⟨U, hU, h⟩
  apply flatFunction_not_locally_zero
  filter_upwards [hU] with x hx
  exact (h x hx).unique (flatFunction_taylor_series x)

/-- For an analytic scalar function, vanishing of every derivative forces local vanishing. -/
theorem flatFunction_not_analytic : ¬ AnalyticAt ℝ flatFunction 0 := by
  intro ha
  apply flatFunction_not_locally_zero
  apply analyticOrderAt_eq_top.mp
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mpr
    (fun i _ => flatFunction_derivatives_zero i)

end D04
