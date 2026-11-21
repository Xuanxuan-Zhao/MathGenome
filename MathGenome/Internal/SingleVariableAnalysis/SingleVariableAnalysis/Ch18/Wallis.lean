import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.Wallis
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.WallisRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Squeeze
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra

/-!
The two limits of K03.18.wallis. We use the upstream proper Darboux
integrals and their finite formulas, then squeeze the odd/even ratio.
Finite product algebra gives Wallis' product limit, and continuity of
square root gives the central binomial limit. No Gamma, Gaussian integral,
Stirling formula or measure-integral Wallis theorem is used.
-/
noncomputable section
namespace SingleVariableAnalysis.Wallis
open Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch18.Wallis

/-- The Wallis product, with the manuscript's indices 1 through n. -/
def wallisProduct : ℕ → ℝ := productValue

private theorem coefficient_zero : wallisCoefficient 0 = 1 := by
  norm_num [wallisCoefficient,
    Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.coefficientValue]

/-- Elementary finite product algebra, including the empty product. -/
theorem wallis_product_coefficient : productCoefficientIdentity := by
  change ∀ n, wallisProduct n = 1 / ((2 * (n : ℝ) + 1) * wallisCoefficient n ^ 2)
  intro n
  induction n with
  | zero => simp [wallisProduct, productValue, coefficient_zero]
  | succ n ih =>
    have hp : wallisProduct (n + 1) = wallisProduct n *
        ((2 * (n : ℝ) + 2) ^ 2 / ((2 * n + 1) * (2 * n + 3))) := by
      exact Finset.prod_range_succ _ _
    rw [hp, ih]
    push_cast
    have hc := wallisCoefficient_step n
    have hn : wallisCoefficient n ≠ 0 := (wallisCoefficient_positive n).ne'
    have hn' : wallisCoefficient (n + 1) ≠ 0 := (wallisCoefficient_positive (n + 1)).ne'
    have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    have hstep : wallisCoefficient (n + 1) =
        (2 * (n : ℝ) + 1) * wallisCoefficient n / (2 * n + 2) := by
      apply (eq_div_iff h2).mpr
      linear_combination hc
    rw [hstep]
    field_simp
    ring

/-- Even integrals are strictly positive, so division preserves the sandwich. -/
theorem wallis_even_positive (n : ℕ) : 0 < wallisIntegral (2 * n) := by
  change 0 < Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.integralValue (2 * n)
  rw [wallis_even n]
  exact mul_pos Real.pi_div_two_pos (wallisCoefficient_positive n)

/-- The explicit lower and upper estimates for the odd/even ratio. -/
theorem wallis_ratio_bounds (n : ℕ) :
    (2 * (n : ℝ) + 1) / (2 * n + 2) ≤
      wallisIntegral (2 * n + 1) / wallisIntegral (2 * n) ∧
    wallisIntegral (2 * n + 1) / wallisIntegral (2 * n) ≤ 1 := by
  have hp := wallis_even_positive n
  have hs := wallis_sandwich n
  change wallisIntegral (2 * n + 2) ≤ wallisIntegral (2 * n + 1) ∧
    wallisIntegral (2 * n + 1) ≤ wallisIntegral (2 * n) at hs
  constructor
  · apply (le_div_iff₀ hp).mpr
    have ht := wallis_step (2 * n)
    push_cast at ht
    rw [ht] at hs
    convert hs.1 using 1
    ring
  · exact (div_le_one hp).mpr hs.2

/-- The substantial analytic step: squeeze the ratio of proper integrals. -/
theorem wallis_integral_ratio_limit : integralRatioLimit := by
  have hl : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n + 2)) atTop (𝓝 1) := by
    simpa [add_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 2 2 (d := 2) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (wallis_ratio_bounds n).1) (fun n => (wallis_ratio_bounds n).2)

/-- This identity transfers the integral squeeze to the finite product. -/
theorem wallis_product_ratio : productRatioIdentity := by
  intro n
  rw [wallis_product_coefficient n, wallis_even n, wallis_odd n]
  have hc : Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.coefficientValue n ≠ 0 :=
    (wallisCoefficient_positive n).ne'
  field_simp

theorem wallis_product_limit : productLimit := by
  change Tendsto productValue atTop (𝓝 (Real.pi / 2))
  have he : productValue = fun n => (Real.pi / 2) *
      (Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.integralValue (2 * n + 1) /
        Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.integralValue (2 * n)) :=
    funext wallis_product_ratio
  rw [he]
  simpa only [mul_one] using wallis_integral_ratio_limit.const_mul (Real.pi / 2)

/-- The square of the normalized coefficient has limit 1/π. -/
theorem wallis_coefficient_square_limit :
    Tendsto (fun n : ℕ => (n : ℝ) * wallisCoefficient n ^ 2) atTop (𝓝 (1 / Real.pi)) := by
  have hl : Tendsto (fun n : ℕ => (n : ℝ) / (2 * n + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa [add_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) 1 1 (d := 2) (by norm_num)
  have h := hl.div wallis_product_limit Real.pi_div_two_pos.ne'
  have he (n : ℕ) : (n : ℝ) / (2 * n + 1) / wallisProduct n =
      (n : ℝ) * wallisCoefficient n ^ 2 := by
    change (n : ℝ) / (2 * n + 1) / productValue n = _
    rw [wallis_product_coefficient n]
    have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    rfl
  convert h using 1
  · funext n
    exact (he n).symm
  · congr 1
    field_simp

theorem wallis_coefficient_limit : coefficientLimit := by
  change Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * wallisCoefficient n)
    atTop (𝓝 (1 / Real.sqrt Real.pi))
  have h := wallis_coefficient_square_limit.sqrt
  have he (n : ℕ) : Real.sqrt ((n : ℝ) * wallisCoefficient n ^ 2) =
      Real.sqrt (n : ℝ) * wallisCoefficient n := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq
      (wallisCoefficient_positive n).le]
  have hv : Real.sqrt (1 / Real.pi) = 1 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  simpa only [he, hv] using h

end SingleVariableAnalysis.Wallis
