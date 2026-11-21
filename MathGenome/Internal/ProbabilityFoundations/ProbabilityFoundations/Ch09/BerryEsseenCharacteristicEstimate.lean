import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.BerryEsseenCharacteristicEstimate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace ProbabilityFoundations.Ch09

/-- The elementary supporting-line inequality for the cubic moment. -/
lemma three_sq_le_two_abs_cube_add_one (x : ℝ) :
    3 * x ^ 2 ≤ 2 * |x| ^ 3 + 1 := by
  have h := mul_nonneg (sq_nonneg (|x| - 1)) (show 0 ≤ 2 * |x| + 1 by positivity)
  nlinarith [sq_abs x]

/-- A unit second moment forces the third absolute moment to be at least one.
This proof uses a pointwise polynomial inequality, so Jensen need not be imported. -/
theorem one_le_third_absolute_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (_hY : Measurable Y) (h3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (h2 : (∫ ω, Y ω ^ 2 ∂P) = 1) :
    1 ≤ ∫ ω, |Y ω| ^ 3 ∂P := by
  have hi2 : Integrable (fun ω => Y ω ^ 2) P :=
    Integrable.of_integral_ne_zero (by rw [h2]; norm_num)
  have h := integral_mono (hi2.const_mul 3) ((h3.const_mul 2).add (integrable_const 1))
    (fun ω => three_sq_le_two_abs_cube_add_one (Y ω))
  simp only [Pi.add_apply] at h
  simp only [integral_add (h3.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul, h2] at h
  linarith

/-- Bound the third derivative by the third absolute moment, uniformly in frequency. -/
lemma norm_iteratedDeriv_charFun_three_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (u : ℝ) :
    ‖iteratedDeriv 3 (charFun μ) u‖ ≤ ∫ x, |x| ^ 3 ∂μ := by
  rw [iteratedDeriv_charFun h3, norm_mul, norm_pow]
  simp only [Complex.norm_I, one_pow, one_mul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with x
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]

/-- A third moment gives a global cubic remainder, with a convenient numerical
constant. The bound is deliberately coarser than the sharp integral remainder. -/
lemma characteristic_taylor_bound_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (h0 : (∫ x, x ∂μ) = 0)
    (h2 : (∫ x, x ^ 2 ∂μ) = 1) (u : ℝ) (hu : 0 ≤ u) :
    ‖charFun μ u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤
      (∫ x, |x| ^ 3 ∂μ) * u ^ 3 / 2 := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  have hc : ContDiff ℝ 3 (charFun μ) := contDiff_charFun h3
  have hTaylor : taylorWithinEval (charFun μ) 2 (Set.Icc 0 u) 0 u =
      taylorWithinEval (charFun μ) 2 Set.univ 0 u := by
    simp only [taylor_within_apply, iteratedDerivWithin_univ]
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu)
      ((hc.of_le (by exact_mod_cast (show k ≤ 3 by have := Finset.mem_range.mp hk; omega))).contDiffAt)
      (by exact ⟨le_rfl, hu.le⟩)]
  have hb := taylor_mean_remainder_bound (n := 2) hu.le hc.contDiffOn
    (show u ∈ Set.Icc 0 u from ⟨hu.le, le_rfl⟩) (C := ∫ x, |x| ^ 3 ∂μ)
    (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu) hc.contDiffAt hy]
      exact norm_iteratedDeriv_charFun_three_le μ h3 y)
  rw [hTaylor] at hb
  have ht : taylorWithinEval (charFun μ) 2 Set.univ 0 u =
      1 - (u : ℂ) ^ 2 / 2 := by
    have h := taylorWithinEval_charFun_two_zero' (P := μ) (X := id)
      measurable_id.aemeasurable h0 h2 u
    simpa using h
  rw [ht] at hb
  simpa only [sub_zero, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] using hb

lemma characteristic_taylor_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : MemLp id 3 μ) (h0 : (∫ x, x ∂μ) = 0)
    (h2 : (∫ x, x ^ 2 ∂μ) = 1) (u : ℝ) :
    ‖charFun μ u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤
      (∫ x, |x| ^ 3 ∂μ) * |u| ^ 3 / 2 := by
  by_cases hu : 0 ≤ u
  · simpa [abs_of_nonneg hu] using characteristic_taylor_bound_nonneg μ h3 h0 h2 u hu
  · have h := characteristic_taylor_bound_nonneg μ h3 h0 h2 (-u) (by linarith)
    rw [charFun_neg] at h
    have he : 1 - ((-u : ℝ) : ℂ) ^ 2 / 2 =
        conj (1 - (u : ℂ) ^ 2 / 2) := by
      have he : (1 : ℂ) - (u : ℂ) ^ 2 / 2 = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.conj_ofReal]
      push_cast
      ring
    rw [he, ← map_sub, Complex.norm_conj] at h
    simpa [abs_of_neg (lt_of_not_ge hu)] using h

/-- The deterministic local step. Its Taylor premise is supplied by the
preceding theorem in the probabilistic application. -/
lemma local_gaussian_comparison {ρ u : ℝ} {a : ℂ} (hρ : 1 ≤ ρ)
    (hu : ρ * |u| ≤ 1 / 3)
    (hT : ‖a - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ ρ * |u| ^ 3 / 2) :
    ‖a‖ ≤ Real.exp (-u ^ 2 / 3) ∧
      ‖a - (Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤ ρ * |u| ^ 3 := by
  have hu1 : |u| ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (abs_nonneg u)]
  have hu2 : u ^ 2 ≤ 1 := by
    nlinarith [sq_abs u, mul_nonneg (show 0 ≤ 1 - |u| by linarith) (show 0 ≤ 1 + |u| by positivity)]
  have habs : ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2‖ = 1 - u ^ 2 / 2 := by
    have he : (1 : ℂ) - (u : ℂ) ^ 2 / 2 = ((1 - u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
  have hT' : ‖a‖ ≤ 1 - u ^ 2 / 2 + ρ * |u| ^ 3 / 2 := by
    calc
      ‖a‖ ≤ ‖a - (1 - (u : ℂ) ^ 2 / 2)‖ + ‖(1 : ℂ) - (u : ℂ) ^ 2 / 2‖ :=
        by
          have h := norm_le_insert (1 - (u : ℂ) ^ 2 / 2) a
          rw [norm_sub_rev (1 - (u : ℂ) ^ 2 / 2) a] at h
          linarith
      _ ≤ _ := by rw [habs]; linarith
  have hsmall : ρ * |u| ^ 3 ≤ u ^ 2 / 3 := by
    have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg |u|)
    nlinarith [sq_abs u]
  constructor
  · calc
      ‖a‖ ≤ 1 - u ^ 2 / 3 := by linarith
      _ ≤ Real.exp (-u ^ 2 / 3) := by linarith [Real.add_one_le_exp (-u ^ 2 / 3)]
  · have hG : ‖(Real.exp (-u ^ 2 / 2) : ℂ) - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ u ^ 4 / 4 := by
      have hh := Real.norm_exp_sub_one_sub_id_le (x := -u ^ 2 / 2)
        (by rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [sq_nonneg u])]; nlinarith)
      have he : (Real.exp (-u ^ 2 / 2) : ℂ) - (1 - (u : ℂ) ^ 2 / 2) =
          ((Real.exp (-u ^ 2 / 2) - 1 - (-u ^ 2 / 2) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [he, Complex.norm_real]
      convert hh using 1
      rw [Real.norm_eq_abs, sq_abs]
      ring
    have hu4 : u ^ 4 ≤ ρ * |u| ^ 3 := by
      have hh := mul_le_mul_of_nonneg_right hu1 (pow_nonneg (abs_nonneg u) 3)
      have hh' := mul_le_mul_of_nonneg_right hρ (pow_nonneg (abs_nonneg u) 3)
      nlinarith [sq_abs u, pow_abs u 4]
    calc
      ‖a - (Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤
          ‖a - (1 - (u : ℂ) ^ 2 / 2)‖ +
          ‖(Real.exp (-u ^ 2 / 2) : ℂ) - (1 - (u : ℂ) ^ 2 / 2)‖ :=
        by
          calc
            _ ≤ ‖a - (1 - (u : ℂ) ^ 2 / 2)‖ + ‖(1 - (u : ℂ) ^ 2 / 2) - (Real.exp (-u ^ 2 / 2) : ℂ)‖ := by
              have h := norm_add_le (a - (1 - (u : ℂ) ^ 2 / 2)) ((1 - (u : ℂ) ^ 2 / 2) - (Real.exp (-u ^ 2 / 2) : ℂ))
              convert h using 2
              ring
            _ = _ := by rw [norm_sub_rev (1 - (u : ℂ) ^ 2 / 2)]
      _ ≤ ρ * |u| ^ 3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ ρ) (pow_nonneg (abs_nonneg u) 3)]

/-- A quantitative difference-of-powers bound, including arbitrary complex phases. -/
lemma norm_pow_succ_sub_pow_succ_le (a b : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1 : ℝ) * ‖a - b‖ * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
      ring
    rw [he]
    calc
      _ ≤ ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ + ‖(a - b) * b ^ (n + 1)‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b‖ ^ (n + 1) := by simp only [norm_mul, norm_pow]
      _ ≤ r * ((n + 1 : ℝ) * ‖a - b‖ * r ^ n) + ‖a - b‖ * r ^ (n + 1) := by gcongr
      _ = _ := by push_cast; ring

/-- Exponential damping survives raising the local comparison to the n-th power. -/
lemma gaussian_power_comparison {ρ u : ℝ} {a : ℂ} (hρ : 1 ≤ ρ)
    (hu : ρ * |u| ≤ 1 / 3)
    (hT : ‖a - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ ρ * |u| ^ 3 / 2)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖a ^ n - (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ)‖ ≤
      (n : ℝ) * ρ * |u| ^ 3 * Real.exp (-(n : ℝ) * u ^ 2 / 6) := by
  obtain ⟨ha, hdiff⟩ := local_gaussian_comparison hρ hu hT
  have hb : ‖(Real.exp (-u ^ 2 / 2) : ℂ)‖ ≤ Real.exp (-u ^ 2 / 3) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  have hn1 : 1 ≤ n := by omega
  have hp := norm_pow_succ_sub_pow_succ_le a (Real.exp (-u ^ 2 / 2))
    (Real.exp_pos (-u ^ 2 / 3)).le ha hb (n - 1)
  rw [Nat.sub_add_cancel hn1] at hp
  have he : (Real.exp (-u ^ 2 / 2) : ℂ) ^ n =
      (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he] at hp
  have hdamp : Real.exp (-u ^ 2 / 3) ^ (n - 1) ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 6) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_sub hn1, Nat.cast_one]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (sq_nonneg u)]
  calc
    _ ≤ (n : ℝ) * ‖a - (Real.exp (-u ^ 2 / 2) : ℂ)‖ * Real.exp (-u ^ 2 / 3) ^ (n - 1) := by
      convert hp using 1
      rw [Nat.cast_sub hn1, Nat.cast_one]
      ring
    _ ≤ (n : ℝ) * (ρ * |u| ^ 3) * Real.exp (-(n : ℝ) * u ^ 2 / 6) := by gcongr
    _ = _ := by ring

/-- Rescale the deterministic estimate by the positive square root of n. -/
lemma rescaled_gaussian_power_comparison {ρ t : ℝ} {a : ℂ} (hρ : 1 ≤ ρ)
    (n : ℕ) (hn : 2 ≤ n)
    (ht : |t| ≤ (1 / 3 : ℝ) * Real.sqrt (n : ℝ) / ρ)
    (hT : ‖a - (1 - ((t / Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ 2 / 2)‖ ≤
      ρ * |t / Real.sqrt (n : ℝ)| ^ 3 / 2) :
    ‖a ^ n - (Real.exp (-t ^ 2 / 2) : ℂ)‖ ≤
      (ρ / Real.sqrt (n : ℝ)) * |t| ^ 3 * Real.exp (-t ^ 2 / 6) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hρ0 : 0 < ρ := by linarith
  have hsmall : ρ * |t / Real.sqrt (n : ℝ)| ≤ 1 / 3 := by
    rw [abs_div, abs_of_pos hs]
    have hh := (le_div_iff₀ hρ0).mp ht
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have h := gaussian_power_comparison hρ hsmall hT n hn
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have he : (n : ℝ) * (t / Real.sqrt (n : ℝ)) ^ 2 = t ^ 2 := by
    field_simp
    nlinarith [hs2]
  have he2 : -(n : ℝ) * (t / Real.sqrt (n : ℝ)) ^ 2 / 2 = -t ^ 2 / 2 := by nlinarith [he]
  have he6 : -(n : ℝ) * (t / Real.sqrt (n : ℝ)) ^ 2 / 6 = -t ^ 2 / 6 := by nlinarith [he]
  rw [he2, he6] at h
  have hcoef : (n : ℝ) * ρ * |t / Real.sqrt (n : ℝ)| ^ 3 =
      ρ / Real.sqrt (n : ℝ) * |t| ^ 3 := by
    rw [abs_div, abs_of_pos hs]
    field_simp
    rw [hs2]
    ring
  rwa [hcoef] at h

/-- Universal quantitative characteristic-function estimate for a centered,
unit-variance random variable with finite third absolute moment. One may take
c = 1/3 and C₀ = 1; neither depends on the probability space or the law. -/
theorem berry_esseen_characteristic_estimate :
    Specs.ProbabilityFoundations.Ch09.BerryEsseenCharacteristicEstimate.Estimate := by
  refine ⟨1 / 3, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro Ω mΩ P instP Y hY h3 h0 h2
  dsimp only
  have hρ := one_le_third_absolute_moment P Y hY h3 h2
  refine ⟨hρ, ?_⟩
  intro n hn t ht
  let μ := P.map Y
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hm3 : Integrable (fun x : ℝ => |x| ^ 3) μ :=
    (integrable_map_measure (by fun_prop) hY.aemeasurable).mpr h3
  have hLp : MemLp id 3 μ := by
    apply (integrable_norm_rpow_iff (by fun_prop) (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).mp
    simpa using hm3
  have hm0 : (∫ x, x ∂μ) = 0 := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
    exact h0
  have hm2 : (∫ x, x ^ 2 ∂μ) = 1 := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
    exact h2
  have hmρ : (∫ x, |x| ^ 3 ∂μ) = ∫ ω, |Y ω| ^ 3 ∂P := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
  have hTaylor := characteristic_taylor_bound μ hLp hm0 hm2 (t / Real.sqrt (n : ℝ))
  rw [hmρ] at hTaylor
  simpa only [one_mul] using rescaled_gaussian_power_comparison hρ n hn ht hTaylor

end ProbabilityFoundations.Ch09
