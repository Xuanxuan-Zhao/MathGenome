import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.ChebyshevConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.NearBestError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.ChebyshevLebesgue
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.HolderBernstein
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The final assertion of W53: quantitative interpolation error and uniform
convergence for Hölder functions on every nondegenerate compact interval. -/
noncomputable section
open Filter
open scoped Topology

namespace NumAnalysis206.Approximation.ChebyshevConvergence
open ChebyshevLebesgue
open NumAnalysis206.HolderBernstein

/-- Insert the transported Bernstein polynomial into W52. -/
theorem quantitative_bound (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b)
    {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖f - interpolationOperator (affineNodes a b hab n) f‖ ≤
      (1 + lebesgueConstant (affineNodes a b hab n)) *
        L * (b - a) ^ α * (4 * (n : ℝ)) ^ (-α / 2) := by
  have hp : (intervalPolynomial a b hab n f).degree ≤ (n : WithBot ℕ) :=
    Polynomial.degree_le_of_natDegree_le (intervalPolynomial_natDegree_le a b hab n f)
  have hbern := interval_uniform_error_le a b hab f hα hα1 hL hf hn
  rw [norm_sub_rev] at hbern
  calc
    _ ≤ (1 + lebesgueConstant (affineNodes a b hab n)) *
        ‖f - (intervalPolynomial a b hab n f).toContinuousMapOn (Set.Icc a b)‖ :=
      interpolation_error_le _ hab (affineNodes_injective a b hab n) f _ hp
    _ ≤ (1 + lebesgueConstant (affineNodes a b hab n)) *
        ((L * (b - a) ^ α) * (4 * (n : ℝ)) ^ (-α / 2)) :=
      mul_le_mul_of_nonneg_left hbern (by
        exact add_nonneg zero_le_one (norm_nonneg _))
    _ = _ := by ring

/-- An explicit envelope; dropping the factor `4^(-α/2)` gives a simpler constant. -/
theorem logarithmic_error_bound (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b)
    {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖f - interpolationOperator (affineNodes a b hab n) f‖ ≤
      ((1 + 8 * Real.pi) * L * (b - a) ^ α) *
        ((1 + Real.log ((n : ℝ) + 1)) * (n : ℝ) ^ (-α / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hleb : 1 + lebesgueConstant (affineNodes a b hab n) ≤
      (1 + 8 * Real.pi) * (1 + Real.log ((n : ℝ) + 1)) := by
    rw [affine_constant]
    have hb := standard_bound n
    nlinarith
  have hpow : (4 * (n : ℝ)) ^ (-α / 2) ≤ (n : ℝ) ^ (-α / 2) :=
    Real.rpow_le_rpow_of_nonpos hn' (by linarith) (by linarith)
  calc
    _ ≤ (1 + lebesgueConstant (affineNodes a b hab n)) *
        L * (b - a) ^ α * (4 * (n : ℝ)) ^ (-α / 2) :=
      quantitative_bound a b hab f hα hα1 hL hf hn
    _ ≤ ((1 + 8 * Real.pi) * (1 + Real.log ((n : ℝ) + 1))) *
        L * (b - a) ^ α * (n : ℝ) ^ (-α / 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hleb hL) (by positivity)
      · exact hpow
      · positivity
      · positivity
    _ = _ := by ring

/-- The W53 rate for the fixed interval and Hölder data. -/
theorem asymptotic_rate (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b)
    {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => ‖f - interpolationOperator (affineNodes a b hab n) f‖)
      (fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) * (n : ℝ) ^ (-α / 2)) := by
  apply Asymptotics.IsBigO.of_bound ((1 + 8 * Real.pi) * L * (b - a) ^ α)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by
    apply mul_nonneg
    · exact add_nonneg zero_le_one (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    · positivity)]
  exact logarithmic_error_bound a b hab f hα hα1 hL hf hn

/-- A positive power beats the logarithmic loss in the Lebesgue bound. -/
theorem logarithmic_rate_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ =>
      (1 + Real.log ((n : ℝ) + 1)) * (n : ℝ) ^ (-α / 2)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-α / 2)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by positivity : 0 < α / 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (α / 2))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop (by positivity : 0 < α / 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper := (hpow.const_mul (1 + Real.log 2)).add hlog
  simp only [mul_zero, add_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · exact Eventually.of_forall fun n => mul_nonneg
      (add_nonneg zero_le_one (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogle : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn'.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    calc
      _ ≤ (1 + (Real.log 2 + Real.log (n : ℝ))) * (n : ℝ) ^ (-α / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 + Real.log 2) * (n : ℝ) ^ (-α / 2) +
          Real.log (n : ℝ) / (n : ℝ) ^ (α / 2) := by
        rw [neg_div, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
        ring

/-- Convergence in the uniform norm on the original interval. -/
theorem convergence (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b)
    {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) :
    Tendsto (fun n : ℕ => interpolationOperator (affineNodes a b hab n) f)
      atTop (𝓝 f) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using
    (asymptotic_rate a b hab f hα hα1 hL hf).trans_tendsto
      (logarithmic_rate_tendsto_zero hα)

/-- Pointwise presentation of the same uniform convergence. -/
theorem uniform_convergence (a b : ℝ) (hab : a < b) (f : IntervalContinuous a b)
    {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ s t : Set.Icc a b, |f t - f s| ≤ L * |(t : ℝ) - s| ^ α) :
    TendstoUniformly (fun (n : ℕ) (t : Set.Icc a b) =>
      interpolationOperator (affineNodes a b hab n) f t) f atTop :=
  ContinuousMap.tendsto_iff_tendstoUniformly.mp (convergence a b hab f hα hα1 hL hf)

end NumAnalysis206.Approximation.ChebyshevConvergence
