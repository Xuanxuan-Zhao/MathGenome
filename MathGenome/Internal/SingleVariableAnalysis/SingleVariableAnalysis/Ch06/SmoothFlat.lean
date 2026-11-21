import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.FlatDecay
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Higher
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.SmoothFlat
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace SingleVariableAnalysis

open Polynomial Filter
open scoped Topology ContDiff

/-- The source's recursively constructed polynomial coefficients. -/
def flatDerivativePolynomial : ℕ → Polynomial ℝ :=
  Specs.SingleVariableAnalysis.Ch06.SmoothFlat.derivativePolynomialValue

@[simp] theorem flatDerivativePolynomial_zero : flatDerivativePolynomial 0 = 1 := rfl

theorem flatDerivativePolynomial_succ (j : ℕ) :
    flatDerivativePolynomial (j + 1) = -X ^ 2 * (flatDerivativePolynomial j).derivative +
      C 2 * X ^ 3 * flatDerivativePolynomial j := rfl

/-- Multiplication by any polynomial in the reciprocal still gives a continuous
zero extension, by the accepted inverse-power decay estimate. -/
theorem flatExponential_polynomial_tendsto_zero (p : Polynomial ℝ) :
    Tendsto (fun x : ℝ => p.eval x⁻¹ * flatExponential x) (𝓝 0) (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => p.eval x⁻¹ * flatExponential x)
      (𝓝[≠] 0) (𝓝 0) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [eval_add, add_mul, add_zero] using hp.add hq
    | monomial n c =>
      have hn : Tendsto (fun x : ℝ => x⁻¹ ^ n * flatExponential x)
          (𝓝[≠] 0) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        apply (flatExponential_inversePower_decay n).congr'
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [flatExponential_of_ne_zero hx]
        simp only [norm_mul, norm_pow, norm_inv, Real.norm_eq_abs,
          zpow_neg, zpow_natCast]
        change (|x| ^ n)⁻¹ * realSeriesExp (-1 / x ^ 2) =
          |x|⁻¹ ^ n * |realSeriesExp (-1 / x ^ 2)|
        have hpos : 0 < realSeriesExp (-1 / x ^ 2) := real_expSeries_pos _
        rw [abs_of_pos hpos, inv_pow]
      simpa only [eval_monomial, mul_assoc, mul_zero] using hn.const_mul c
  conv_lhs => rw [← nhdsNE_sup_pure (0 : ℝ)]
  rw [tendsto_sup]
  refine ⟨hp, ?_⟩
  simpa using tendsto_pure_nhds (fun x : ℝ => p.eval x⁻¹ * flatExponential x) 0

/-- One derivative step, valid also at zero. The zero case uses the decay of
(p * X)(1/x) f(x), which is exactly the difference quotient. -/
theorem flatExponential_polynomial_hasDerivAt (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => p.eval x⁻¹ * flatExponential x)
      ((-X ^ 2 * p.derivative + C 2 * X ^ 3 * p).eval x⁻¹ * flatExponential x) x := by
  by_cases hx : x = 0
  · subst x
    simp only [flatExponential_zero, mul_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    apply ((flatExponential_polynomial_tendsto_zero (p * X)).mono_left
      nhdsWithin_le_nhds).congr
    intro y
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have he : HasDerivAt (fun y : ℝ => Real.exp (-1 / y ^ 2))
        (2 * x⁻¹ ^ 3 * Real.exp (-1 / x ^ 2)) x := by
      have hd := ((hasDerivAt_const x (-1 : ℝ)).div
        ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)).exp
      convert hd using 1 <;> dsimp
      field_simp
      ring
    have hd := ((p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx)).mul he
    have hExp : realSeriesExp = Real.exp := funext expSeries_eq_realExp
    have hval : ((-X ^ 2 * p.derivative + C 2 * X ^ 3 * p).eval x⁻¹ *
        flatExponential x) =
        (p.derivative.eval x⁻¹ * -(x ^ 2)⁻¹ * Real.exp (-1 / x ^ 2) +
          p.eval x⁻¹ * (2 * x⁻¹ ^ 3 * Real.exp (-1 / x ^ 2))) := by
      rw [flatExponential_of_ne_zero hx, hExp]
      simp only [eval_add, eval_mul, eval_neg, eval_pow, eval_X, eval_C]
      simp only [inv_pow]
      ring
    rw [hval]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [flatExponential_of_ne_zero hy, hExp]
    rfl

/-- Every iterated derivative is the zero-extended polynomial expression. -/
theorem flatExponential_iteratedDeriv (j : ℕ) :
    RealIteratedDerivative j flatExponential =
      fun x => (flatDerivativePolynomial j).eval x⁻¹ * flatExponential x := by
  induction j with
  | zero => simp [flatDerivativePolynomial_zero]
  | succ j ih =>
    rw [realIteratedDerivative_succ, ih]
    funext x
    rw [(flatExponential_polynomial_hasDerivAt _ x).deriv,
      flatDerivativePolynomial_succ]

theorem flatExponential_smooth : Specs.SingleVariableAnalysis.Ch06.SmoothFlat.smooth := by
  change SmoothOn flatExponential Set.univ
  intro k
  constructor
  · intro j _ x _
    rw [flatExponential_iteratedDeriv]
    exact (flatExponential_polynomial_hasDerivAt _ x).differentiableAt
  · intro j _
    rw [flatExponential_iteratedDeriv]
    intro x _
    exact (flatExponential_polynomial_hasDerivAt _ x).continuousAt.continuousWithinAt

theorem flatExponential_all_derivatives_zero :
    Specs.SingleVariableAnalysis.Ch06.SmoothFlat.derivativesAtZero := by
  intro j
  change RealIteratedDerivative j flatExponential 0 = 0
  rw [flatExponential_iteratedDeriv]
  simp

theorem flatExponential_smooth_positive :
    Specs.SingleVariableAnalysis.Ch06.SmoothFlat.positiveOffZero :=
  flatExponential_pos

theorem flatExponential_derivative_representation :
    Specs.SingleVariableAnalysis.Ch06.SmoothFlat.derivativeRepresentation := by
  intro j x hx
  change RealIteratedDerivative j flatExponential x =
    (flatDerivativePolynomial j).eval (1 / x) * realSeriesExp (-1 / x ^ 2)
  simpa only [one_div, flatExponential_of_ne_zero hx] using
    congrFun (flatExponential_iteratedDeriv j) x

end SingleVariableAnalysis
