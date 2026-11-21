import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.PowerSeries
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Abel
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring

/-!
# Abel's endpoint theorem

The endpoint limit reuses Mathlib's Abel theorem, whose hypothesis is a limit
of ordered finite sums, not unconditional summability. We bridge its exclusive
partial sums to the project's inclusive sums. Interior absolute convergence
and the Abel partial-sum identity are proved with geometric majorants and a
finite identity followed by limits. Negative endpoints are obtained by sign
alternation and the real substitution x ↦ -x.
-/
namespace SingleVariableAnalysis
open Filter
open scoped BigOperators Topology

/-- Switching between inclusive and exclusive truncations loses no convergence information. -/
theorem abel_tendsto_sum_range_iff {K : Type*} [TopologicalSpace K] [AddCommMonoid K]
    (a : ℕ → K) (S : K) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) atTop (𝓝 S) ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  tendsto_add_atTop_iff_nat (f := fun N => ∑ n ∈ Finset.range N, a n) 1

private theorem real_ordinary_tendsto (a : ℕ → ℝ) (S : ℝ)
    (h : RealSeriesHasSum a S) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  (abel_tendsto_sum_range_iff a S).mp ((realSequenceConverges_iff _ _).mp h)

private theorem complex_ordinary_tendsto (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSeriesHasSum a S) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  (abel_tendsto_sum_range_iff a S).mp ((complexSequenceConverges_iff _ _).mp h)

private theorem real_ordinary_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum a S) :
    RealSeriesHasSum a S :=
  (realSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

private theorem complex_ordinary_of_hasSum {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) :
    ComplexSeriesHasSum a S :=
  (complexSequenceConverges_iff _ _).mpr
    ((abel_tendsto_sum_range_iff a S).mpr h.tendsto_sum_nat)

/-- A bounded coefficient sequence times a strict geometric sequence is absolutely summable. -/
theorem abel_summable_norm_mul_pow_of_bounded {K : Type*} [NormedDivisionRing K]
    (b : ℕ → K) (z : K) (C : ℝ) (hC : ∀ n, ‖b n‖ ≤ C) (hz : ‖z‖ < 1) :
    Summable (fun n => ‖b n * z ^ n‖) := by
  refine ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C).of_nonneg_of_le
    (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)

/-- Ordinary convergence at 1 supplies the bounded coefficients used in the geometric majorant. -/
theorem abel_summable_norm_mul_pow {K : Type*} [NormedDivisionRing K]
    (a : ℕ → K) (S z : K)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S))
    (hz : ‖z‖ < 1) : Summable (fun n => ‖a n * z ^ n‖) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h.cauchySeq
  exact abel_summable_norm_mul_pow_of_bounded a z C hC hz

/-- Finite form of Abel's partial-sum identity, with its exact remaining boundary. -/
theorem abel_finite_identity {K : Type*} [CommRing K] (a : ℕ → K) (z : K) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n * z ^ n) =
      (1 - z) * (∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n + 1), a j) * z ^ n) +
      (∑ j ∈ Finset.range N, a j) * z ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun n => a n * z ^ n),
      Finset.sum_range_succ (fun n => (∑ j ∈ Finset.range (n + 1), a j) * z ^ n),
      ih, Finset.sum_range_succ a N, pow_succ]
    ring

/-- The series of weighted partial sums is absolutely convergent, and gives Abel's identity. -/
theorem abel_partial_sum_identity {K : Type*} [NormedField K] [CompleteSpace K]
    (a : ℕ → K) (S z : K)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S)) (hz : ‖z‖ < 1) :
    Summable (fun n => ‖(∑ j ∈ Finset.range (n + 1), a j) * z ^ n‖) ∧
      (∑' n, a n * z ^ n) =
        (1 - z) * ∑' n, (∑ j ∈ Finset.range (n + 1), a j) * z ^ n := by
  have hi := (abel_tendsto_sum_range_iff a S).mpr h
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hi).exists_norm_le
  have hb := abel_summable_norm_mul_pow_of_bounded
    (fun n => ∑ j ∈ Finset.range (n + 1), a j) z C
    (fun n => hC _ ⟨n, rfl⟩) hz
  refine ⟨hb, ?_⟩
  have ha := (abel_summable_norm_mul_pow a S z h hz).of_norm
  have hv := (h.mul (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz))
  have ht := ((hb.of_norm.hasSum.tendsto_sum_nat).const_mul (1 - z)).add hv
  simp only [mul_zero, add_zero] at ht
  exact tendsto_nhds_unique ha.hasSum.tendsto_sum_nat
    (ht.congr (fun N => (abel_finite_identity a z N).symm))

/-- Absolute convergence and the ordinary value on [0,1). -/
theorem real_abel_interior (a : ℕ → ℝ) (S : ℝ) (h : RealSeriesHasSum a S)
    (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    RealPowerSeriesAbsolutelyConverges a 0 x ∧
      RealPowerSeriesHasSum a 0 x (∑' n, a n * x ^ n) := by
  have hn := abel_summable_norm_mul_pow a S x (real_ordinary_tendsto a S h)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx₀] using hx₁)
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => |a n * (x - 0) ^ n|) T
    simp only [sub_zero]
    exact ⟨_, real_ordinary_of_hasSum (by simpa only [Real.norm_eq_abs] using hn.hasSum)⟩
  · change RealSeriesHasSum (fun n => a n * (x - 0) ^ n) _
    simpa only [sub_zero] using real_ordinary_of_hasSum hn.of_norm.hasSum

/-- The complex-valued series uses a real argument and the usual complex embedding. -/
theorem complex_abel_interior (a : ℕ → ℂ) (S : ℂ) (h : ComplexSeriesHasSum a S)
    (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    ComplexPowerSeriesAbsolutelyConverges a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSum a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n) := by
  have hn := abel_summable_norm_mul_pow a S (x : ℂ) (complex_ordinary_tendsto a S h)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀] using hx₁)
  constructor
  · change ∃ T, RealSeriesHasSum (fun n => ‖a n * ((x : ℂ) - (0 : ℝ)) ^ n‖) T
    simp only [Complex.ofReal_zero, sub_zero]
    exact ⟨_, real_ordinary_of_hasSum hn.hasSum⟩
  · change ComplexSeriesHasSum (fun n => a n * ((x : ℂ) - (0 : ℝ)) ^ n) _
    simpa only [Complex.ofReal_zero, sub_zero] using complex_ordinary_of_hasSum hn.of_norm.hasSum

/-- Abel's identity with the manuscript's inclusive ordinary partial sums. -/
theorem real_abel_identity (a : ℕ → ℝ) (S : ℝ) (h : RealSeriesHasSum a S)
    (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    RealSeriesConverges (fun n => |realPartialSum a n * x ^ n|) ∧
      (∑' n, a n * x ^ n) = (1 - x) * ∑' n, realPartialSum a n * x ^ n := by
  obtain ⟨hn, he⟩ := abel_partial_sum_identity a S x (real_ordinary_tendsto a S h)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx₀] using hx₁)
  exact ⟨⟨_, real_ordinary_of_hasSum (by simpa only [Real.norm_eq_abs, realPartialSum] using hn.hasSum)⟩, he⟩

theorem complex_abel_identity (a : ℕ → ℂ) (S : ℂ) (h : ComplexSeriesHasSum a S)
    (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    RealSeriesConverges (fun n => ‖complexPartialSum a n * (x : ℂ) ^ n‖) ∧
      (∑' n, a n * (x : ℂ) ^ n) =
        (1 - (x : ℂ)) * ∑' n, complexPartialSum a n * (x : ℂ) ^ n := by
  obtain ⟨hn, he⟩ := abel_partial_sum_identity a S (x : ℂ) (complex_ordinary_tendsto a S h)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀] using hx₁)
  exact ⟨⟨_, real_ordinary_of_hasSum hn.hasSum⟩, he⟩

/-- Abel's endpoint limit from below; conditional ordinary convergence suffices. -/
theorem real_abel_endpoint (a : ℕ → ℝ) (S : ℝ) (h : RealSeriesHasSum a S) :
    Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 S) :=
  Real.tendsto_tsum_powerSeries_nhdsWithin_lt (real_ordinary_tendsto a S h)

theorem complex_abel_endpoint (a : ℕ → ℂ) (S : ℂ) (h : ComplexSeriesHasSum a S) :
    Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) := by
  simpa only [Function.comp_def] using
    (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
      (complex_ordinary_tendsto a S h)).comp tendsto_map

/-- Sign alternation is exactly the substitution of a negated argument. -/
theorem abel_alternating_term {K : Type*} [CommRing K] (a : ℕ → K) (x : K) (n : ℕ) :
    ((-1 : K) ^ n * a n) * (-x) ^ n = a n * x ^ n := by
  calc
    _ = a n * (((-1 : K) * (-x)) ^ n) := by rw [mul_pow]; ring
    _ = a n * x ^ n := by simp

private theorem abel_neg_tendsto :
    Tendsto (fun x : ℝ => -x) (𝓝[>] (-1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (continuous_neg.tendsto (-1 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change -x < (1 : ℝ)
    linarith only [show (-1 : ℝ) < x from hx]

/-- The analogous theorem at -1, under ordinary convergence of ∑(-1)^n a_n. -/
theorem real_abel_negative_endpoint (a : ℕ → ℝ) (S : ℝ)
    (h : RealSeriesHasSum (fun n => (-1 : ℝ) ^ n * a n) S) :
    (∀ x : ℝ, -1 < x → x ≤ 0 →
      RealPowerSeriesAbsolutelyConverges a 0 x ∧
      RealPowerSeriesHasSum a 0 x (∑' n, a n * x ^ n)) ∧
    Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[>] (-1)) (𝓝 S) := by
  constructor
  · intro x hx₀ hx₁
    have ht := real_abel_interior (fun n => (-1 : ℝ) ^ n * a n) S h (-x)
      (neg_nonneg.mpr hx₁) (by linarith)
    change (RealSeriesConverges (fun n => |((-1 : ℝ) ^ n * a n) * (-x - 0) ^ n|) ∧
      RealSeriesHasSum (fun n => ((-1 : ℝ) ^ n * a n) * (-x - 0) ^ n) _) at ht
    change RealSeriesConverges (fun n => |a n * (x - 0) ^ n|) ∧
      RealSeriesHasSum (fun n => a n * (x - 0) ^ n) _
    simpa only [sub_zero, abel_alternating_term] using ht
  · simpa only [Function.comp_def, abel_alternating_term] using
      (real_abel_endpoint (fun n => (-1 : ℝ) ^ n * a n) S h).comp abel_neg_tendsto

theorem complex_abel_negative_endpoint (a : ℕ → ℂ) (S : ℂ)
    (h : ComplexSeriesHasSum (fun n => (-1 : ℂ) ^ n * a n) S) :
    (∀ x : ℝ, -1 < x → x ≤ 0 →
      ComplexPowerSeriesAbsolutelyConverges a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSum a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n)) ∧
    Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[>] (-1)) (𝓝 S) := by
  constructor
  · intro x hx₀ hx₁
    have ht := complex_abel_interior (fun n => (-1 : ℂ) ^ n * a n) S h (-x)
      (neg_nonneg.mpr hx₁) (by linarith)
    change (RealSeriesConverges
        (fun n => ‖((-1 : ℂ) ^ n * a n) * (((-x : ℝ) : ℂ) - 0) ^ n‖) ∧
      ComplexSeriesHasSum
        (fun n => ((-1 : ℂ) ^ n * a n) * (((-x : ℝ) : ℂ) - 0) ^ n) _) at ht
    change RealSeriesConverges (fun n => ‖a n * ((x : ℂ) - 0) ^ n‖) ∧
      ComplexSeriesHasSum (fun n => a n * ((x : ℂ) - 0) ^ n) _
    simpa only [sub_zero, Complex.ofReal_neg, abel_alternating_term] using ht
  · simpa only [Function.comp_def, Complex.ofReal_neg, abel_alternating_term] using
      (complex_abel_endpoint (fun n => (-1 : ℂ) ^ n * a n) S h).comp abel_neg_tendsto

end SingleVariableAnalysis
