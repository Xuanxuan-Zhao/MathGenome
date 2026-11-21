import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Abel
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Tauber
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Positivity

/-!
# Tauber's converse under the original coefficient condition

K03.13.tauber, paper.tex:1474–1491. The coefficient condition alone gives
absolute interior convergence and s_N − f(1 − 1/N) → 0. The finite head
is bounded by the Cesaro mean of n‖a_n‖; a geometric majorant controls the
infinite tail. Only then is the assumed Abel limit used. The conclusions
use the shared ordinary inclusive partial-sum predicates, and do not impose
absolute convergence at the endpoint. Public comparison: Choimet–Queffélec,
*Twelve Landmarks of Twentieth-Century Analysis*, §1.1, Theorem 1.1.2.
-/

namespace SingleVariableAnalysis
open Filter
open scoped BigOperators Topology

section NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coefficient condition supplies bounded coefficients, including degree zero. -/
theorem tauber_coefficients_bounded (a : ℕ → E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ n, ‖a n‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
  refine ⟨max C ‖a 0‖, fun n => ?_⟩
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hb := hC _ ⟨n, rfl⟩
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)] at hb
    exact (le_trans (by nlinarith [norm_nonneg (a n)]) hb).trans (le_max_left _ _)

/-- Geometric majorants prove absolute convergence before an endpoint limit is used. -/
theorem tauber_summable_norm [CompleteSpace E] (a : ℕ → E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0))
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n => ‖x ^ n • a n‖) := by
  obtain ⟨C, hC⟩ := tauber_coefficients_bounded a h
  refine ((summable_geometric_of_lt_one hx hx1).mul_left C).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => ?_)
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx n), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hx n)

/-- Bernoulli's elementary bound in the form needed for finite truncations. -/
theorem tauber_one_sub_pow_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hp : x ^ n ≤ 1 := pow_le_one₀ hx hx1
    nlinarith

/-- A finite head is controlled by the Cesaro average of n‖aₙ‖. -/
theorem tauber_head_bound (a : ℕ → E) {N : ℕ} (hN : 0 < N) :
    ‖∑ n ∈ Finset.range N, (a n - (1 - (N : ℝ)⁻¹) ^ n • a n)‖ ≤
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖ := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 0 ≤ 1 - (N : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hNr)
  have hx1 : 1 - (N : ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖a n - (1 - (N : ℝ)⁻¹) ^ n • a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (N : ℝ)⁻¹ * ((n : ℝ) * ‖a n‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show a n - (1 - (N : ℝ)⁻¹) ^ n • a n =
        (1 - (1 - (N : ℝ)⁻¹) ^ n) • a n by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr (pow_le_one₀ hx hx1))]
      have hb := tauber_one_sub_pow_le hx hx1 n
      simp only [sub_sub_cancel] at hb
      nlinarith [norm_nonneg (a n)]
    _ = _ := by rw [Finset.mul_sum]

/-- Multiplication by n tending to zero also makes the original coefficients null. -/
theorem tauber_coefficients_tendsto_zero (a : ℕ → E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using h.norm)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [norm_nonneg (a n)]

/-- A small tail of n‖aₙ‖ bounds the geometric tail at x_N by the same error. -/
theorem tauber_tail_bound (a : ℕ → E) {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 ≤ ε) (ha : ∀ n ≥ N, (n : ℝ) * ‖a n‖ ≤ ε) :
    ‖∑' k, (1 - (N : ℝ)⁻¹) ^ (k + N) • a (k + N)‖ ≤ ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let x : ℝ := 1 - (N : ℝ)⁻¹
  have hx : 0 ≤ x := sub_nonneg.mpr (inv_le_one_of_one_le₀ hNr1)
  have hx1 : x < 1 := sub_lt_self _ (inv_pos.mpr hNr)
  have hg := (hasSum_geometric_of_lt_one hx hx1).mul_left (ε / N)
  have he : (ε / (N : ℝ)) * (1 - x)⁻¹ = ε := by
    dsimp [x]
    rw [sub_sub_cancel, inv_inv, div_mul_cancel₀ _ hNr.ne']
  rw [he] at hg
  apply tsum_of_norm_bounded hg
  intro k
  have hkN : N ≤ k + N := Nat.le_add_left _ _
  have hb : ‖a (k + N)‖ ≤ ε / N := by
    apply (le_div_iff₀ hNr).mpr
    have hcast : (N : ℝ) ≤ (k + N : ℕ) := by exact_mod_cast hkN
    nlinarith [ha (k + N) hkN, norm_nonneg (a (k + N))]
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx _)]
  calc
    x ^ (k + N) * ‖a (k + N)‖ ≤ x ^ (k + N) * (ε / N) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hx _)
    _ ≤ (ε / N) * x ^ k := by
      rw [pow_add]
      have hp : x ^ N ≤ 1 := pow_le_one₀ hx hx1.le
      have hz : 0 ≤ ε / (N : ℝ) := div_nonneg hε hNr.le
      nlinarith [pow_nonneg hx k, mul_nonneg (pow_nonneg hx k) hz]

/-- The error for exclusive truncations vanishes, without an Abel-limit hypothesis. -/
theorem tauber_exclusive_approximation [CompleteSpace E] (a : ℕ → E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, a n) -
      ∑' n, (1 - (N : ℝ)⁻¹) ^ n • a n) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ) * ‖a n‖) atTop (𝓝 0) := by
    simpa only [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _), norm_zero] using h.norm
  have hc := hb.cesaro
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he2 : 0 < ε / 2 := half_pos hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hb (ε / 2) he2
  obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp hc (ε / 2) he2
  refine ⟨max 1 (max M L), fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hN)
  have hNM : M ≤ N := (le_max_left M L).trans ((le_max_right _ _).trans hN)
  have hNL : L ≤ N := (le_max_right M L).trans ((le_max_right _ _).trans hN)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hx : 0 ≤ 1 - (N : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hNr)
  have hx1 : 1 - (N : ℝ)⁻¹ < 1 := sub_lt_self _ (by positivity)
  have hs := (tauber_summable_norm a h hx hx1).of_norm
  have hid := hs.sum_add_tsum_nat_add N
  have htail := tauber_tail_bound a hN1 he2.le (fun n hn => by
    have ht := hM n (hNM.trans hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))] at ht
    exact ht.le)
  have hhead := tauber_head_bound a hN1
  have hsmall := hL N hNL
  rw [Real.dist_eq, sub_zero] at hsmall
  have hid' : (∑ n ∈ Finset.range N, a n) - ∑' n, (1 - (N : ℝ)⁻¹) ^ n • a n =
      (∑ n ∈ Finset.range N, (a n - (1 - (N : ℝ)⁻¹) ^ n • a n)) -
      ∑' k, (1 - (N : ℝ)⁻¹) ^ (k + N) • a (k + N) := by
    rw [← hid, Finset.sum_sub_distrib]
    abel
  rw [dist_zero_right, hid']
  have hnorm := norm_sub_le
    (∑ n ∈ Finset.range N, (a n - (1 - (N : ℝ)⁻¹) ^ n • a n))
    (∑' k, (1 - (N : ℝ)⁻¹) ^ (k + N) • a (k + N))
  exact lt_of_le_of_lt (hnorm.trans (add_le_add hhead htail))
    (by linarith [le_abs_self ((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖)])

/-- The source's inclusive partial-sum approximation s_N − f(1 − 1/N) → 0. -/
theorem tauber_approximation [CompleteSpace E] (a : ℕ → E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0)) :
    Tendsto (fun N => (∑ n ∈ Finset.range (N + 1), a n) -
      ∑' n, (1 - (N : ℝ)⁻¹) ^ n • a n) atTop (𝓝 0) := by
  have ht := (tauber_exclusive_approximation a h).add (tauber_coefficients_tendsto_zero a h)
  simpa only [zero_add] using ht.congr (fun N => by rw [Finset.sum_range_succ]; abel)

/-- The sampling points approach 1 strictly from the left. -/
theorem tauber_sampling_tendsto :
    Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (𝓝[<] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have ht : Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (𝓝 (1 - 0 : ℝ)) :=
      tendsto_const_nhds.sub hi
    simpa only [sub_zero] using ht
  · filter_upwards [eventually_ge_atTop 1] with N hN
    change 1 - (N : ℝ)⁻¹ < 1
    exact sub_lt_self _ (inv_pos.mpr (by exact_mod_cast hN))

/-- Tauber's converse for a complete real normed space, using ordinary truncations. -/
theorem tauber_of_abel_limit [CompleteSpace E] (a : ℕ → E) (S : E)
    (h : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0))
    (hS : Tendsto (fun x : ℝ => ∑' n, x ^ n • a n) (𝓝[<] 1) (𝓝 S)) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) atTop (𝓝 S) := by
  have ht := (tauber_approximation a h).add (hS.comp tauber_sampling_tendsto)
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using ht

end NormedSpace
private theorem tauber_real_ordinary_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum a S) :
    RealSeriesHasSum a S :=
  (realSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

private theorem tauber_complex_ordinary_of_hasSum {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) :
    ComplexSeriesHasSum a S :=
  (complexSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

/-- Absolute convergence and the ordinary interior value, derived from n aₙ → 0. -/
theorem real_tauber_interior (a : ℕ → ℝ)
    (h : RealSequenceConverges (fun n => (n : ℝ) * a n) 0)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    RealPowerSeriesAbsolutelyConverges a 0 x ∧
      RealPowerSeriesHasSum a 0 x (∑' n, a n * x ^ n) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0) :=
    (realSequenceConverges_iff _ _).mp h
  have hs : Summable (fun n => ‖a n * x ^ n‖) := by
    simpa only [smul_eq_mul, mul_comm] using tauber_summable_norm a ht hx.le hx1
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => |a n * (x - 0) ^ n|) T
    simp only [sub_zero]
    exact ⟨_, tauber_real_ordinary_of_hasSum (by simpa only [Real.norm_eq_abs] using hs.hasSum)⟩
  · change RealSeriesHasSum (fun n => a n * (x - 0) ^ n) _
    simpa only [sub_zero] using tauber_real_ordinary_of_hasSum hs.of_norm.hasSum

/-- The complex series is evaluated at a real argument using the usual embedding. -/
theorem complex_tauber_interior (a : ℕ → ℂ)
    (h : ComplexSequenceConverges (fun n => (n : ℂ) * a n) 0)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    ComplexPowerSeriesAbsolutelyConverges a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSum a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0) := by
    simpa only [Complex.real_smul, Complex.ofReal_natCast] using
      (complexSequenceConverges_iff _ _).mp h
  have hs : Summable (fun n => ‖a n * (x : ℂ) ^ n‖) := by
    simpa only [Complex.real_smul, Complex.ofReal_pow, mul_comm] using
      tauber_summable_norm a ht hx.le hx1
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => ‖a n * ((x : ℂ) - (0 : ℝ)) ^ n‖) T
    simp only [Complex.ofReal_zero, sub_zero]
    exact ⟨_, tauber_real_ordinary_of_hasSum hs.hasSum⟩
  · change ComplexSeriesHasSum (fun n => a n * ((x : ℂ) - (0 : ℝ)) ^ n) _
    simpa only [Complex.ofReal_zero, sub_zero] using tauber_complex_ordinary_of_hasSum hs.of_norm.hasSum

/-- The exact inclusive approximation asserted in the manuscript, for real coefficients. -/
theorem real_tauber_approximation (a : ℕ → ℝ)
    (h : RealSequenceConverges (fun n => (n : ℝ) * a n) 0) :
    RealSequenceConverges
      (fun N => realPartialSum a N - ∑' n, a n * (1 - (N : ℝ)⁻¹) ^ n) 0 := by
  apply (realSequenceConverges_iff _ _).mpr
  simpa only [realPartialSum, smul_eq_mul, mul_comm] using
    tauber_approximation a ((realSequenceConverges_iff _ _).mp h)

/-- The same inclusive approximation for complex coefficients. -/
theorem complex_tauber_approximation (a : ℕ → ℂ)
    (h : ComplexSequenceConverges (fun n => (n : ℂ) * a n) 0) :
    ComplexSequenceConverges
      (fun N => complexPartialSum a N -
        ∑' n, a n * ((1 - (N : ℝ)⁻¹ : ℝ) : ℂ) ^ n) 0 := by
  apply (complexSequenceConverges_iff _ _).mpr
  have ht : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0) := by
    simpa only [Complex.real_smul, Complex.ofReal_natCast] using
      (complexSequenceConverges_iff _ _).mp h
  simpa only [complexPartialSum, Complex.real_smul, Complex.ofReal_pow, mul_comm] using
    tauber_approximation a ht

/-- An Abel sum plus the original small-coefficient hypothesis implies ordinary convergence. -/
theorem real_tauber (a : ℕ → ℝ) (S : ℝ)
    (h : RealSequenceConverges (fun n => (n : ℝ) * a n) 0)
    (hS : Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 S)) :
    RealSeriesHasSum a S := by
  apply (realSequenceConverges_iff _ _).mpr
  have ht : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0) :=
    (realSequenceConverges_iff _ _).mp h
  have hS' : Tendsto (fun x : ℝ => ∑' n, x ^ n • a n) (𝓝[<] 1) (𝓝 S) := by
    simpa only [smul_eq_mul, mul_comm] using hS
  exact tauber_of_abel_limit a S ht hS'

/-- Complex Tauber converse; no order on complex numbers and no absolute endpoint sum is assumed. -/
theorem complex_tauber (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSequenceConverges (fun n => (n : ℂ) * a n) 0)
    (hS : Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 S)) :
    ComplexSeriesHasSum a S := by
  apply (complexSequenceConverges_iff _ _).mpr
  have ht : Tendsto (fun n : ℕ => (n : ℝ) • a n) atTop (𝓝 0) := by
    simpa only [Complex.real_smul, Complex.ofReal_natCast] using
      (complexSequenceConverges_iff _ _).mp h
  have hS' : Tendsto (fun x : ℝ => ∑' n, x ^ n • a n) (𝓝[<] 1) (𝓝 S) := by
    simpa only [Complex.real_smul, Complex.ofReal_pow, mul_comm] using hS
  exact tauber_of_abel_limit a S ht hS'

end SingleVariableAnalysis
