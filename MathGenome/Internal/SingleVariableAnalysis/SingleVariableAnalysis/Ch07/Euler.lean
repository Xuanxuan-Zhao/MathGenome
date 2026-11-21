import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.Euler
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
K03.07.euler. The upstream bridges identify the constructed factorial sums
with the canonical functions. Mathlib's exp_mul_I is an algebraic identity
from its exponential definitions of sin and cos; exp_conj commutes
conjugation with the defining partial sums and their limit.

For the derivative we work directly with the factorial series on a bounded
real interval. The differentiated shifted terms have the summable majorant
‖z‖ (A ‖z‖)^n / n!. No complex derivative is used.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped BigOperators Topology

theorem expSeries_imaginary : Specs.SingleVariableAnalysis.Ch07.Euler.imaginaryInput := by
  intro t
  rw [expSeries_eq_complexExp, (sinCosSeries_eq_real t).1, (sinCosSeries_eq_real t).2]
  simpa only [mul_comm] using Complex.exp_ofReal_mul_I t

theorem expSeries_imaginary_norm : Specs.SingleVariableAnalysis.Ch07.Euler.imaginaryModulus := by
  intro t
  rw [expSeries_eq_complexExp]
  exact Complex.norm_exp_I_mul_ofReal t

theorem expSeries_conjugation : Specs.SingleVariableAnalysis.Ch07.Euler.conjugation := by
  intro z
  rw [expSeries_eq_complexExp, expSeries_eq_complexExp]
  exact (Complex.exp_conj z).symm

namespace Euler

/-- Differentiating a shifted factorial term uses only real increments. -/
theorem shifted_term_hasDerivAt (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((s : ℂ) * z)^(n+1) / ((n+1).factorial : ℂ))
      (z * (((t : ℂ) * z)^n / (n.factorial : ℂ))) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const z)
  have hd := (hl.pow (n+1)).div_const ((n+1).factorial : ℂ)
  convert hd using 1
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem series_split (z : ℂ) :
    seriesExp z = 1 + ∑' n : ℕ, z^(n+1) / ((n+1).factorial : ℂ) := by
  simpa only [seriesExp, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] using
    ((ExpConstruction.summable z).sum_add_tsum_nat_add 1).symm

end Euler

theorem expSeries_real_parameter_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.Euler.realParameterDerivative := by
  intro z t
  change HasDerivAt (fun s : ℝ => seriesExp ((s : ℂ) * z))
    (z * seriesExp ((t : ℂ) * z)) t
  let A : ℝ := |t| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have htA : t ∈ Ioo (-A) A := by
    have h := abs_le.mp (le_refl |t|)
    constructor <;> dsimp [A] <;> linarith [h.1, h.2]
  have hd : HasDerivAt
      (fun s : ℝ => ∑' n : ℕ, ((s : ℂ) * z)^(n+1) / ((n+1).factorial : ℂ))
      (∑' n : ℕ, z * (((t : ℂ) * z)^n / (n.factorial : ℂ))) t := by
    apply hasDerivAt_tsum_of_isPreconnected
      ((Real.summable_pow_div_factorial (A * ‖z‖)).mul_left ‖z‖)
      isOpen_Ioo (convex_Ioo (-A) A).isPreconnected
      (fun n s _ => Euler.shifted_term_hasDerivAt z n s)
      (fun n s hs => ?_)
      (show (0 : ℝ) ∈ Ioo (-A) A by constructor <;> linarith)
      ((summable_nat_add_iff 1).mpr (ExpConstruction.summable ((0 : ℂ) * z))) htA
    simp only [norm_mul, ExpConstruction.norm_term, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩) (norm_nonneg z)
  rw [tsum_mul_left] at hd
  exact (hd.const_add 1).congr_of_eventuallyEq
    (Eventually.of_forall fun s => Euler.series_split ((s : ℂ) * z))

end SingleVariableAnalysis
