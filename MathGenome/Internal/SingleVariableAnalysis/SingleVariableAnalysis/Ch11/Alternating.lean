import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Necessary
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Alternating
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Alternating series, signed remainders, and the harmonic example

The sums here are ordinary ordered partial-sum limits, including conditional
convergence. We reuse Mathlib's antitone alternating-series convergence test
and its two partial-sum bracketing inequalities. Its packaged error-bound
theorem has a summability hypothesis that is unnecessary here and is not used.
The bracketing inequalities give the sign and sharp first-omitted-term bound
by parity, including zero terms. Harmonic divergence is the upstream dyadic
proof, after an explicit finite-sum index shift.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology
open Filter

theorem alternating_series_converges (b : ℕ → ℝ) (_hb : ∀ n, 0 ≤ b n)
    (hm : ∀ n, b (n + 1) ≤ b n) (h0 : RealSequenceConverges b 0) :
    RealSeriesConverges (fun n => (-1 : ℝ) ^ n * b n) := by
  have hmono : Antitone b := antitone_nat_of_succ_le hm
  obtain ⟨S, hS⟩ := hmono.tendsto_alternating_series_of_tendsto_zero
    ((realSequenceConverges_iff b 0).mp h0)
  refine ⟨S, (realSequenceConverges_iff _ S).mpr ?_⟩
  exact hS.comp (tendsto_add_atTop_nat 1)

/-- Bounds relative to a prefix of exactly n terms, before converting to the
paper's inclusive upper index. These require ordinary convergence only. -/
theorem alternating_prefix_remainder (b : ℕ → ℝ) (hm : Antitone b) (S : ℝ)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * b i)
      atTop (𝓝 S)) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * (S - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * b i) ∧
      |S - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * b i| ≤ b n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    have hl := hm.alternating_series_le_tendsto hS k
    have hu := hm.tendsto_le_alternating_series hS k
    simp only [Finset.sum_range_succ] at hu
    simp [pow_mul] at hu ⊢
    constructor
    · linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)]
      linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    have hu := hm.tendsto_le_alternating_series hS k
    have hl := hm.alternating_series_le_tendsto hS (k + 1)
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ] at hl
    simp [pow_add, pow_mul] at hl ⊢
    constructor
    · linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hu)]
      linarith

theorem alternating_series_remainder (b : ℕ → ℝ) (_hb : ∀ n, 0 ≤ b n)
    (hm : ∀ n, b (n + 1) ≤ b n) (_h0 : RealSequenceConverges b 0)
    (S : ℝ) (hS : RealSeriesHasSum (fun n => (-1 : ℝ) ^ n * b n) S) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) *
      (S - realPartialSum (fun n => (-1 : ℝ) ^ n * b n) N) ∧
      |S - realPartialSum (fun n => (-1 : ℝ) ^ n * b n) N| ≤ b (N + 1) := by
  have ht := (realSequenceConverges_iff _ S).mp hS
  have hr : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * b i)
      atTop (𝓝 S) := (tendsto_add_atTop_iff_nat 1).mp ht
  exact alternating_prefix_remainder b (antitone_nat_of_succ_le hm) S hr (N + 1)

theorem alternating_harmonic_conditional :
    RealSeriesConverges (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1)) ∧
      ¬ RealSeriesConverges (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) := by
  have h0 : RealSequenceConverges (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
    have hh := (real_shift_iff (fun n : ℕ => 1 / (n : ℝ)) 0 1).mpr harmonic_term_limit
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  constructor
  · simpa only [mul_one_div] using alternating_series_converges
      (fun n : ℕ => 1 / ((n : ℝ) + 1))
      (fun n => one_div_nonneg.mpr (by positivity))
      (fun n => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)) h0
  · rintro ⟨S, hS⟩
    apply harmonic_series_diverges
    refine ⟨S, (real_shift_iff (realPartialSum (fun n : ℕ => 1 / (n : ℝ))) S 1).mp ?_⟩
    have he : ∀ N, realPartialSum
        (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) N =
        realPartialSum (fun n : ℕ => 1 / (n : ℝ)) (N + 1) := by
      intro N
      have ha : (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) =
          (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
        funext n
        simp [abs_div, abs_pow, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
      rw [ha]
      unfold realPartialSum
      rw [Finset.sum_range_succ' (fun n : ℕ => 1 / (n : ℝ)) (N + 1)]
      simp
    change RealSequenceConverges (realPartialSum
      (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|)) S at hS
    simpa only [← he] using hS

end SingleVariableAnalysis
