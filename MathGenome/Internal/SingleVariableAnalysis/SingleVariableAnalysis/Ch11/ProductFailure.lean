import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Comparison
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.ProductFailure

/-!
# Two conditional series whose Cauchy product diverges

K03.11.product_failure. The common magnitude decreases to zero, but dominates
the harmonic sequence. Every summand of the nth convolution has sign (-1)^n.
The arithmetic–geometric mean inequality bounds each denominator by (n+2)/2,
so the coefficient magnitude is at least 2(n+1)/(n+2), including n = 0.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

noncomputable def productFailureA (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / Real.sqrt ((n : ℝ) + 1)

noncomputable def productFailureB : ℕ → ℝ := productFailureA

noncomputable def productFailureC (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), productFailureA k * productFailureB (n - k)

theorem productFailureA_abs (n : ℕ) :
    |productFailureA n| = 1 / Real.sqrt ((n : ℝ) + 1) := by
  simp [productFailureA, abs_div, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem product_failure_factors_conditional :
    (RealSeriesConverges productFailureA ∧
      ¬ RealSeriesConverges (fun n => |productFailureA n|)) ∧
    (RealSeriesConverges productFailureB ∧
      ¬ RealSeriesConverges (fun n => |productFailureB n|)) := by
  have hc : RealSeriesConverges productFailureA := by
    have hh : RealSequenceConverges (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) 0 := by
      apply (realSequenceConverges_iff _ _).mpr
      simpa only [one_div, Real.sqrt_inv, Real.sqrt_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.sqrt
    change RealSeriesConverges (fun n : ℕ => (-1 : ℝ)^n / Real.sqrt ((n : ℝ) + 1))
    simpa only [mul_one_div] using
      alternating_series_converges (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1))
        (fun n => by positivity)
        (fun n => one_div_le_one_div_of_le (by positivity)
          (Real.sqrt_le_sqrt (by push_cast; linarith))) hh
  have hd : ¬ RealSeriesConverges (fun n => |productFailureA n|) := by
    intro ha
    apply comparison_harmonic_diverges
    apply real_series_comparison_of_nonnegative _ _ (fun n => by positivity) _ ha
    intro n
    rw [productFailureA_abs]
    exact one_div_le_one_div_of_le (by positivity)
      (Real.sqrt_le_self_iff.mpr (Or.inr (by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)))
  exact ⟨⟨hc, hd⟩, ⟨hc, hd⟩⟩

theorem product_failure_magnitude (n : ℕ) :
    |productFailureC n| = ∑ k ∈ Finset.range (n + 1),
      1 / Real.sqrt (((k : ℝ) + 1) * ((n - k : ℕ) + 1 : ℝ)) := by
  have he : productFailureC n = (-1 : ℝ)^n *
      ∑ k ∈ Finset.range (n + 1),
        1 / Real.sqrt (((k : ℝ) + 1) * ((n - k : ℕ) + 1 : ℝ)) := by
    rw [productFailureC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    dsimp [productFailureA, productFailureB]
    rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hkn,
      Real.sqrt_mul (by positivity)]
    ring
  rw [he, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  apply abs_of_nonneg
  exact Finset.sum_nonneg (fun k _ => by positivity)

/-- The finite arithmetic–geometric mean bound for a convolution denominator. -/
theorem product_failure_sqrt_bound (n k : ℕ) (hk : k ≤ n) :
    Real.sqrt (((k : ℝ) + 1) * ((n - k : ℕ) + 1 : ℝ)) ≤ ((n : ℝ) + 2) / 2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [Nat.cast_sub hk]
    nlinarith [sq_nonneg ((k : ℝ) + 1 - ((n : ℝ) - k + 1))]

theorem product_failure_lower_bound (n : ℕ) :
    2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ |productFailureC n| ∧
      1 ≤ 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  constructor
  · rw [product_failure_magnitude]
    calc
      2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) =
          ∑ _k ∈ Finset.range (n + 1), 1 / (((n : ℝ) + 2) / 2) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
        field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le (by positivity)
        exact product_failure_sqrt_bound n k (by
          simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
  · apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 2)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem product_failure_term_not_zero_limit :
    ¬ RealSequenceConverges productFailureC 0 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have hl := product_failure_lower_bound N
  have hu := hN N le_rfl
  simp only [sub_zero] at hu
  linarith

theorem product_failure_diverges : RealSeriesDiverges productFailureC := by
  intro h
  exact product_failure_term_not_zero_limit (real_series_term_limit _ h)

end SingleVariableAnalysis
