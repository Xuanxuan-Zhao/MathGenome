import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Tauber
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.TauberAveraged
import Mathlib.Tactic.FieldSimp

/-!
# Tauber's converse under the averaged coefficient condition

The finite identity gives ordinary convergence of the difference series
∑(aₙ-bₙ) to zero. Apply the upstream Abel endpoint theorem to that
series, and the upstream Tauber theorem to b. Interior convergence is
proved before transferring any total `tsum` values. The source hypothesis
is the scalar limit Tₙ/n → 0; it is never replaced by a bound on n aₙ.
The left-neighborhood filter at 1 agrees with the specified approach
0 < r < 1, since r is eventually positive in that filter.

For the Abel step, see also the proof at
https://planetmath.org/proofofabelslimittheorem (saved under research/).
-/

namespace SingleVariableAnalysis
open Filter
open scoped BigOperators Topology
open Specs.SingleVariableAnalysis.Ch13.TauberAveraged

/-- The exact telescoping identity, including n=0. -/
theorem tauber_averaged_finite_identity {K : Type*} [Field K] [CharZero K]
    (a : ℕ → K) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), a k) -
      (∑ k ∈ Finset.range (n + 1), transformed a k) =
      weightedTotal a n / ((n : K) + 1) := by
  induction n with
  | zero => simp [weightedTotal, transformed]
  | succ n ih =>
    have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hn2 : (n : K) + 1 + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
    rw [Finset.sum_range_succ a (n + 1), Finset.sum_range_succ (transformed a) (n + 1)]
    rw [show (∑ k ∈ Finset.range (n + 1), a k) + a (n + 1) -
        ((∑ k ∈ Finset.range (n + 1), transformed a k) + transformed a (n + 1)) =
        ((∑ k ∈ Finset.range (n + 1), a k) -
          (∑ k ∈ Finset.range (n + 1), transformed a k)) +
          a (n + 1) - transformed a (n + 1) by ring, ih]
    simp only [transformed, Nat.add_one_ne_zero, ↓reduceIte]
    have hT : weightedTotal a (n + 1) = weightedTotal a n + ((n : K) + 1) * a (n + 1) := by
      simp only [weightedTotal, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [hT]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- The remainder T_n/(n+1) is null under exactly the averaged hypothesis. -/
theorem tauber_averaged_remainder_tendsto {K : Type*} [RCLike K]
    (a : ℕ → K)
    (h : Tendsto (fun n => weightedTotal a n / (n : K)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedTotal a n / ((n : K) + 1)) atTop (𝓝 0) := by
  have ht := h.mul (tendsto_natCast_div_add_atTop (1 : K))
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [div_eq_mul_inv, hn0, mul_assoc]

/-- Multiplying the transformed coefficient by n gives the same null remainder. -/
theorem tauber_averaged_transformed_condition {K : Type*} [RCLike K]
    (a : ℕ → K)
    (h : Tendsto (fun n => weightedTotal a n / (n : K)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : K) * transformed a n) atTop (𝓝 0) := by
  apply (tauber_averaged_remainder_tendsto a h).congr
  intro n
  by_cases hn : n = 0
  · simp [hn, weightedTotal]
  · have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn1 : (n : K) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    simp only [transformed, ite_eq_right hn]
    field_simp

/-- The difference series converges ordinarily to zero, before any Abel limit is used. -/
theorem tauber_averaged_difference_tendsto {K : Type*} [RCLike K]
    (a : ℕ → K)
    (h : Tendsto (fun n => weightedTotal a n / (n : K)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (a k - transformed a k))
      atTop (𝓝 0) := by
  simpa only [Finset.sum_sub_distrib, tauber_averaged_finite_identity] using
    tauber_averaged_remainder_tendsto a h

/-- Interior absolute convergence follows from the averaged condition alone. -/
theorem tauber_averaged_summable_norm {K : Type*} [RCLike K]
    (a : ℕ → K)
    (h : Tendsto (fun n => weightedTotal a n / (n : K)) atTop (𝓝 0))
    {z : K} (hz : ‖z‖ < 1) : Summable (fun n => ‖a n * z ^ n‖) := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ) • transformed a n) atTop (𝓝 0) := by
    simpa only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_natCast] using
      tauber_averaged_transformed_condition a h
  obtain ⟨C, hC⟩ := tauber_coefficients_bounded (transformed a) hb
  have hbs := abel_summable_norm_mul_pow_of_bounded (transformed a) z C hC hz
  have hcs := abel_summable_norm_mul_pow (fun n => a n - transformed a n) 0 z
    ((abel_tendsto_sum_range_iff _ _).mp (tauber_averaged_difference_tendsto a h)) hz
  apply (hcs.add hbs).of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  have he : a n * z ^ n = (a n - transformed a n) * z ^ n + transformed a n * z ^ n := by ring
  rw [he]
  exact norm_add_le _ _

/-- The manuscript's inclusive finite identity for real coefficients. -/
theorem real_tauber_averaged_identity (a : ℕ → ℝ) (n : ℕ) :
    realPartialSum a n - realPartialSum (transformed a) n =
      weightedTotal a n / ((n : ℝ) + 1) :=
  tauber_averaged_finite_identity a n

/-- The same finite identity for complex coefficients. -/
theorem complex_tauber_averaged_identity (a : ℕ → ℂ) (n : ℕ) :
    complexPartialSum a n - complexPartialSum (transformed a) n =
      weightedTotal a n / ((n : ℂ) + 1) :=
  tauber_averaged_finite_identity a n

theorem real_tauber_averaged_transformed_condition (a : ℕ → ℝ)
    (h : RealSequenceConverges (fun n => weightedTotal a n / (n : ℝ)) 0) :
    RealSequenceConverges (fun n => (n : ℝ) * transformed a n) 0 :=
  (realSequenceConverges_iff _ _).mpr
    (tauber_averaged_transformed_condition a ((realSequenceConverges_iff _ _).mp h))

theorem complex_tauber_averaged_transformed_condition (a : ℕ → ℂ)
    (h : ComplexSequenceConverges (fun n => weightedTotal a n / (n : ℂ)) 0) :
    ComplexSequenceConverges (fun n => (n : ℂ) * transformed a n) 0 :=
  (complexSequenceConverges_iff _ _).mpr
    (tauber_averaged_transformed_condition a ((complexSequenceConverges_iff _ _).mp h))

private theorem averaged_real_ordinary_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum a S) :
    RealSeriesHasSum a S :=
  (realSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

private theorem averaged_complex_ordinary_of_hasSum {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) :
    ComplexSeriesHasSum a S :=
  (complexSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

/-- Absolute convergence and the ordinary interior value need no Abel-limit assumption. -/
theorem real_tauber_averaged_interior (a : ℕ → ℝ)
    (h : RealSequenceConverges (fun n => weightedTotal a n / (n : ℝ)) 0)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    RealPowerSeriesAbsolutelyConverges a 0 r ∧
      RealPowerSeriesHasSum a 0 r (∑' n, a n * r ^ n) := by
  have hs := tauber_averaged_summable_norm a ((realSequenceConverges_iff _ _).mp h)
    (z := r) (by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1)
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => |a n * (r - 0) ^ n|) T
    simp only [sub_zero]
    exact ⟨_, averaged_real_ordinary_of_hasSum (by simpa only [Real.norm_eq_abs] using hs.hasSum)⟩
  · change RealSeriesHasSum (fun n => a n * (r - 0) ^ n) _
    simpa only [sub_zero] using averaged_real_ordinary_of_hasSum hs.of_norm.hasSum

/-- The complex power series is evaluated on the real unit interval. -/
theorem complex_tauber_averaged_interior (a : ℕ → ℂ)
    (h : ComplexSequenceConverges (fun n => weightedTotal a n / (n : ℂ)) 0)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ComplexPowerSeriesAbsolutelyConverges a 0 (r : ℂ) ∧
      ComplexPowerSeriesHasSum a 0 (r : ℂ) (∑' n, a n * (r : ℂ) ^ n) := by
  have hs := tauber_averaged_summable_norm a ((complexSequenceConverges_iff _ _).mp h)
    (z := (r : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1)
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => ‖a n * ((r : ℂ) - (0 : ℝ)) ^ n‖) T
    simp only [Complex.ofReal_zero, sub_zero]
    exact ⟨_, averaged_real_ordinary_of_hasSum hs.hasSum⟩
  · change ComplexSeriesHasSum (fun n => a n * ((r : ℂ) - (0 : ℝ)) ^ n) _
    simpa only [Complex.ofReal_zero, sub_zero] using averaged_complex_ordinary_of_hasSum hs.of_norm.hasSum

/-- The transformed power series is also absolutely convergent in the unit interval. -/
theorem real_tauber_averaged_transformed_interior (a : ℕ → ℝ)
    (h : RealSequenceConverges (fun n => weightedTotal a n / (n : ℝ)) 0)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    RealPowerSeriesAbsolutelyConverges (transformed a) 0 r ∧
      RealPowerSeriesHasSum (transformed a) 0 r (∑' n, transformed a n * r ^ n) :=
  real_tauber_interior (transformed a) (real_tauber_averaged_transformed_condition a h) r hr hr1

/-- Complex transformed interior convergence, derived before any endpoint limit. -/
theorem complex_tauber_averaged_transformed_interior (a : ℕ → ℂ)
    (h : ComplexSequenceConverges (fun n => weightedTotal a n / (n : ℂ)) 0)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ComplexPowerSeriesAbsolutelyConverges (transformed a) 0 (r : ℂ) ∧
      ComplexPowerSeriesHasSum (transformed a) 0 (r : ℂ)
        (∑' n, transformed a n * (r : ℂ) ^ n) :=
  complex_tauber_interior (transformed a)
    (complex_tauber_averaged_transformed_condition a h) r hr hr1

/-- A convergent difference series transfers the real Abel limit to b. -/
theorem real_tauber_averaged_abel_transfer (a : ℕ → ℝ) (S : ℝ)
    (h : RealSequenceConverges (fun n => weightedTotal a n / (n : ℝ)) 0)
    (hS : Tendsto (fun r : ℝ => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 S)) :
    Tendsto (fun r : ℝ => ∑' n, transformed a n * r ^ n) (𝓝[<] 1) (𝓝 S) := by
  have hc : RealSeriesHasSum (fun n => a n - transformed a n) 0 :=
    (realSequenceConverges_iff _ _).mpr
      (tauber_averaged_difference_tendsto a ((realSequenceConverges_iff _ _).mp h))
  have ht := hS.sub (real_abel_endpoint _ 0 hc)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with r hr1 hr
  change r < 1 at hr1
  have hz : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1
  have ha := (tauber_averaged_summable_norm a ((realSequenceConverges_iff _ _).mp h) hz).of_norm
  have hd := (abel_summable_norm_mul_pow (fun n => a n - transformed a n) 0 r
    ((abel_tendsto_sum_range_iff _ _).mp ((realSequenceConverges_iff _ _).mp hc)) hz).of_norm
  rw [← ha.tsum_sub hd]
  exact tsum_congr (fun n => by ring)

/-- A convergent difference series transfers the complex Abel limit to b. -/
theorem complex_tauber_averaged_abel_transfer (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSequenceConverges (fun n => weightedTotal a n / (n : ℂ)) 0)
    (hS : Tendsto (fun r : ℝ => ∑' n, a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S)) :
    Tendsto (fun r : ℝ => ∑' n, transformed a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) := by
  have hc : ComplexSeriesHasSum (fun n => a n - transformed a n) 0 :=
    (complexSequenceConverges_iff _ _).mpr
      (tauber_averaged_difference_tendsto a ((complexSequenceConverges_iff _ _).mp h))
  have ht := hS.sub (complex_abel_endpoint _ 0 hc)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with r hr1 hr
  change r < 1 at hr1
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have ha := (tauber_averaged_summable_norm a ((complexSequenceConverges_iff _ _).mp h) hz).of_norm
  have hd := (abel_summable_norm_mul_pow (fun n => a n - transformed a n) 0 (r : ℂ)
    ((abel_tendsto_sum_range_iff _ _).mp ((complexSequenceConverges_iff _ _).mp hc)) hz).of_norm
  rw [← ha.tsum_sub hd]
  exact tsum_congr (fun n => by ring)

/-- The averaged Tauber theorem for real coefficients and ordinary inclusive sums. -/
theorem real_tauber_averaged (a : ℕ → ℝ) (S : ℝ)
    (h : RealSequenceConverges (fun n => weightedTotal a n / (n : ℝ)) 0)
    (hS : Tendsto (fun r : ℝ => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 S)) :
    RealSeriesHasSum a S := by
  have hb := real_tauber (transformed a) S (real_tauber_averaged_transformed_condition a h)
    (real_tauber_averaged_abel_transfer a S h hS)
  have ht := (tauber_averaged_difference_tendsto a ((realSequenceConverges_iff _ _).mp h)).add
    ((realSequenceConverges_iff _ _).mp hb)
  apply (realSequenceConverges_iff _ _).mpr
  change Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (𝓝 S)
  simpa only [realPartialSum, Finset.sum_sub_distrib, sub_add_cancel, zero_add] using ht

/-- The averaged Tauber theorem for complex coefficients; no order on the coefficients is used. -/
theorem complex_tauber_averaged (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSequenceConverges (fun n => weightedTotal a n / (n : ℂ)) 0)
    (hS : Tendsto (fun r : ℝ => ∑' n, a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S)) :
    ComplexSeriesHasSum a S := by
  have hb := complex_tauber (transformed a) S (complex_tauber_averaged_transformed_condition a h)
    (complex_tauber_averaged_abel_transfer a S h hS)
  have ht := (tauber_averaged_difference_tendsto a ((complexSequenceConverges_iff _ _).mp h)).add
    ((complexSequenceConverges_iff _ _).mp hb)
  apply (complexSequenceConverges_iff _ _).mpr
  change Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), a k) atTop (𝓝 S)
  simpa only [complexPartialSum, Finset.sum_sub_distrib, sub_add_cancel, zero_add] using ht

end SingleVariableAnalysis
