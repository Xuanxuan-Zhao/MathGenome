import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.MTest
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.CompactUniform
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform absolute convergence on smaller power-series disks

`K03.13.compact_uniform`, paper.tex:1374–1383. Choose finite radii
`r < ρ < R` and `s = (r+ρ)/2 > 0`. Absolute convergence at ρ gives
`|a n| * ρ^n ≤ M`. The formal k-th derivative terms on the r-disk
are then bounded by `(M/s^k) * n.descFactorial k * (s/ρ)^n`.
The descending-factorial geometric series is summable (Mathlib's finite
binomial/Cauchy-product proof), and the upstream M-test supplies uniform
convergence of both the scalar and magnitude partial sums. Only the
nonnegative numerical majorant is passed through unconditional `Summable`;
the conclusions use the upstream ordinary inclusive partial-sum predicates.
No hypothesis asserts a derivative or a derivative-series convergence.
-/

noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators Topology ENNReal

def realFormalDerivativeTerm (a : ℕ → ℝ) (c : ℝ) (k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (n.descFactorial k : ℝ) * a n * (x-c)^(n-k)

def complexFormalDerivativeTerm (a : ℕ → ℂ) (c : ℝ) (k : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (n.descFactorial k : ℂ) * a n * (z-(c : ℂ))^(n-k)

theorem real_formalDerivative_zero (a : ℕ → ℝ) (c x : ℝ) (n : ℕ) :
    realFormalDerivativeTerm a c 0 x n = realPowerSeriesTerm a c x n := by
  simp [realFormalDerivativeTerm, realPowerSeriesTerm]

theorem complex_formalDerivative_zero (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (n : ℕ) :
    complexFormalDerivativeTerm a c 0 z n = complexPowerSeriesTerm a c z n := by
  simp [complexFormalDerivativeTerm, complexPowerSeriesTerm]

theorem real_formalDerivative_formula (a : ℕ → ℝ) (c x : ℝ) (k n : ℕ) :
    realFormalDerivativeTerm a c k x n =
      (∏ j ∈ Finset.range k, ((n-j : ℕ) : ℝ)) * a n * (x-c)^(n-k) := by
  simp [realFormalDerivativeTerm, Nat.descFactorial_eq_prod_range, Nat.cast_prod]

theorem complex_formalDerivative_formula (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (k n : ℕ) :
    complexFormalDerivativeTerm a c k z n =
      (∏ j ∈ Finset.range k, ((n-j : ℕ) : ℂ)) * a n * (z-(c : ℂ))^(n-k) := by
  simp [complexFormalDerivativeTerm, Nat.descFactorial_eq_prod_range, Nat.cast_prod]

theorem real_formalDerivative_below (a : ℕ → ℝ) (c x : ℝ) (k n : ℕ) (h : n < k) :
    realFormalDerivativeTerm a c k x n = 0 := by
  simp [realFormalDerivativeTerm, Nat.descFactorial_of_lt h]

theorem complex_formalDerivative_below (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (k n : ℕ) (h : n < k) :
    complexFormalDerivativeTerm a c k z n = 0 := by
  simp [complexFormalDerivativeTerm, Nat.descFactorial_of_lt h]

namespace PowerSeriesCompact

theorem ordinary_converges_of_summable (b : ℕ → ℝ) (h : Summable b) :
    RealSeriesConverges b := by
  refine ⟨∑' n, b n, (realSequenceConverges_iff _ _).mpr ?_⟩
  exact h.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)

theorem rescale (b s ρ : ℝ) (hs : s ≠ 0) (hρ : ρ ≠ 0)
    (k n : ℕ) (hkn : k ≤ n) :
    b * s^(n-k) = (b * ρ^n) * (s/ρ)^n / s^k := by
  rw [div_pow]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkn]

/-- A summable numerical bound on every formal derivative term. The auxiliary
radius s is positive even when r = 0, so no division by a zero radius occurs. -/
theorem derivative_majorant (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (r ρ : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ)
    (hconv : RealSeriesConverges (fun n => b n * ρ^n)) (k : ℕ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ RealSeriesConverges B ∧
      ∀ n t, 0 ≤ t → t ≤ r → (n.descFactorial k : ℝ) * b n * t^(n-k) ≤ B n := by
  have hρ : 0 < ρ := hr.trans_lt hrρ
  obtain ⟨M, hM, hbound⟩ := real_convergent_bounded _ 0
    (real_series_term_limit _ hconv)
  let s := (r+ρ)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hrs : r ≤ s := by dsimp [s]; linarith
  have hsρ : s < ρ := by dsimp [s]; linarith
  have hq0 : 0 ≤ s/ρ := (div_pos hs hρ).le
  have hq1 : ‖s/ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (div_lt_one hρ).mpr hsρ
  let B := fun n : ℕ => (M / s^k) * ((n.descFactorial k : ℝ) * (s/ρ)^n)
  refine ⟨B, fun n => by dsimp [B]; positivity, ?_, ?_⟩
  · apply ordinary_converges_of_summable
    exact (summable_descFactorial_mul_geometric_of_norm_lt_one k hq1).mul_left _
  · intro n t ht htr
    by_cases hkn : k ≤ n
    · calc
        (n.descFactorial k : ℝ) * b n * t^(n-k) ≤
            (n.descFactorial k : ℝ) * b n * s^(n-k) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (htr.trans hrs) _)
            (mul_nonneg (Nat.cast_nonneg _) (hb n))
        _ = (n.descFactorial k : ℝ) * ((b n * ρ^n) * (s/ρ)^n / s^k) := by
          rw [mul_assoc, rescale (b n) s ρ hs.ne' hρ.ne' k n hkn]
        _ ≤ (n.descFactorial k : ℝ) * (M * (s/ρ)^n / s^k) := by
          gcongr
          exact (le_abs_self _).trans (hbound n)
        _ = B n := by dsimp [B]; ring
    · have hz : n.descFactorial k = 0 := Nat.descFactorial_of_lt (by omega)
      simp [hz, B]

end PowerSeriesCompact

open PowerSeriesCompact

theorem real_formalDerivative_compact_uniform (a : ℕ → ℝ) (c r : ℝ)
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < realPowerSeriesRadius a) (k : ℕ) :
    (∃ f : {x : ℝ // |x-c| ≤ r} → ℝ, RealUniformConverges
      (fun N (x : {x : ℝ // |x-c| ≤ r}) => realPartialSum
        (realFormalDerivativeTerm a c k x) N) f) ∧
    (∃ g : {x : ℝ // |x-c| ≤ r} → ℝ, RealUniformConverges
      (fun N (x : {x : ℝ // |x-c| ≤ r}) => realPartialSum
        (fun n => |realFormalDerivativeTerm a c k x n|) N) g) ∧
    ∀ x : {x : ℝ // |x-c| ≤ r}, RealSeriesConverges
      (fun n => |realFormalDerivativeTerm a c k x n|) := by
  obtain ⟨ρ, hρ0, hrρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hR
  have hrρ' : r < ρ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mp hrρ
  have hc := real_powerSeries_radius_absolute a 0 ρ
    (by simpa [abs_of_nonneg hρ0] using hρR)
  have hc' : RealSeriesConverges (fun n => |a n| * ρ^n) := by
    simpa only [RealPowerSeriesAbsolutelyConverges, real_powerSeries_term_magnitude,
      sub_zero, abs_of_nonneg hρ0] using hc
  obtain ⟨B, hB0, hB, hb⟩ := derivative_majorant (fun n => |a n|)
    (fun n => abs_nonneg _) r ρ hr hrρ' hc' k
  apply real_m_test (fun n (x : {x : ℝ // |x-c| ≤ r}) =>
    realFormalDerivativeTerm a c k x n) B hB0 ?_ hB
  intro n x
  simpa only [realFormalDerivativeTerm, abs_mul, abs_pow,
    Nat.abs_cast] using hb n |(x : ℝ)-c| (abs_nonneg _) x.property

theorem complex_formalDerivative_compact_uniform (a : ℕ → ℂ) (c r : ℝ)
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < complexPowerSeriesRadius a) (k : ℕ) :
    (∃ f : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℂ, ComplexUniformConverges
      (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => complexPartialSum
        (complexFormalDerivativeTerm a c k z) N) f) ∧
    (∃ g : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℝ, RealUniformConverges
      (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => realPartialSum
        (fun n => ‖complexFormalDerivativeTerm a c k z n‖) N) g) ∧
    ∀ z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}, RealSeriesConverges
      (fun n => ‖complexFormalDerivativeTerm a c k z n‖) := by
  obtain ⟨ρ, hρ0, hrρ, hρR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hR
  have hrρ' : r < ρ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mp hrρ
  have hc := complex_powerSeries_radius_absolute a 0 (ρ : ℂ)
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hρR)
  have hc' : RealSeriesConverges (fun n => ‖a n‖ * ρ^n) := by
    simpa only [ComplexPowerSeriesAbsolutelyConverges,
      complex_powerSeries_term_magnitude, Complex.ofReal_zero, sub_zero,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0] using hc
  obtain ⟨B, hB0, hB, hb⟩ := derivative_majorant (fun n => ‖a n‖)
    (fun n => norm_nonneg _) r ρ hr hrρ' hc' k
  apply complex_m_test (fun n (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) =>
    complexFormalDerivativeTerm a c k z n) B hB0 ?_ hB
  intro n z
  simpa only [complexFormalDerivativeTerm, norm_mul, norm_pow, Complex.norm_natCast]
    using hb n ‖(z : ℂ)-(c : ℂ)‖ (norm_nonneg _) z.property

theorem real_coefficients_complex_compact_uniform :
    Specs.SingleVariableAnalysis.Ch13.CompactUniform.realCoefficientsComplexCompactUniform := by
  intro a c r hr hR k
  have hrad : complexPowerSeriesRadius (fun n => (a n : ℂ)) = realPowerSeriesRadius a := by
    simp [complexPowerSeriesRadius, realPowerSeriesRadius, complexPowerSeriesRootGrowth,
      realPowerSeriesRootGrowth, Complex.norm_real, Real.norm_eq_abs]
  exact complex_formalDerivative_compact_uniform (fun n => (a n : ℂ)) c r hr
    (by rwa [hrad]) k

theorem real_powerSeries_compact_uniform :
    Specs.SingleVariableAnalysis.Ch13.CompactUniform.realPowerSeriesCompactUniform := by
  intro a c r hr hR
  have h := real_formalDerivative_compact_uniform a c r hr hR 0
  simp only [realPartialSum, realFormalDerivativeTerm, Nat.descFactorial_zero, Nat.cast_one,
    one_mul, Nat.sub_zero] at h
  exact h

theorem complex_powerSeries_compact_uniform :
    Specs.SingleVariableAnalysis.Ch13.CompactUniform.complexPowerSeriesCompactUniform := by
  intro a c r hr hR
  have h := complex_formalDerivative_compact_uniform a c r hr hR 0
  simp only [complexPartialSum, realPartialSum, complexFormalDerivativeTerm,
    Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero] at h
  exact h

end SingleVariableAnalysis
