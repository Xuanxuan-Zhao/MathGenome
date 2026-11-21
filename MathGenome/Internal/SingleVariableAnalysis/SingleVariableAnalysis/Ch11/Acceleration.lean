import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Acceleration
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.IntegralTest
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A telescoping acceleration of the reciprocal-square series

The two general remainder bounds reuse the upstream ordinary-series and
improper Riemann theorems. The new corrected terms are bounded in magnitude
by `1 / (3 * (n+1)^4)`. For the quantitative error we dominate this by the
successive differences of `1 / (9 * n^3)`, sum on finite tails, and pass to
an ordinary partial-sum limit. This is an algebraic alternative to evaluating
the fourth-power improper integral in the manuscript.

Mathlib's p-series theorem supplies absolute summability of the two numerical
series. We explicitly convert it to the project's ordinary inclusive limits;
no absolute-convergence hypothesis is imposed on the alternating remainder.
-/

namespace SingleVariableAnalysis
open scoped BigOperators Topology
open Filter

theorem acceleration_alternating_remainder :
    Specs.SingleVariableAnalysis.Ch11.Acceleration.alternatingRemainder :=
  alternating_series_remainder

theorem acceleration_integral_tail_bounds :
    Specs.SingleVariableAnalysis.Ch11.Acceleration.integralTailBounds := by
  intro f hn hm hi N hN
  exact Riemann.Improper.integral_test_remainder_bounds f hn hm
    ((Riemann.Improper.integral_test f hn hm).mpr hi) N hN

/-- Algebraic form and the fourth-power majorant of a corrected term. -/
theorem reciprocalSquareCorrection_bound (n : ℕ) :
    reciprocalSquareCorrection n =
      -(1 / (4 * ((n : ℝ)+1)^2 * (((n : ℝ)+1)^2-1/4))) ∧
    |reciprocalSquareCorrection n| ≤ 1 / (3 * ((n : ℝ)+1)^4) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < ((n : ℝ)+1)^2-1/4 := by nlinarith [sq_nonneg (n : ℝ)]
  have he : reciprocalSquareCorrection n =
      -(1 / (4 * ((n : ℝ)+1)^2 * (((n : ℝ)+1)^2-1/4))) := by
    unfold reciprocalSquareCorrection
    have h0 : (n : ℝ)+1 ≠ 0 := by positivity
    have h1 : (n : ℝ)+1-1/2 ≠ 0 := by linarith
    have h2 : (n : ℝ)+1+1/2 ≠ 0 := by linarith
    field_simp (disch := nlinarith)
    ring
  refine ⟨he, ?_⟩
  rw [he, abs_neg, abs_of_pos (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg (((n : ℝ)+1)^2-1)]

/-- Summability is used only for these explicitly absolutely convergent series. -/
theorem reciprocalSquareTerm_summable : Summable reciprocalSquareTerm := by
  change Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ)))

theorem reciprocalSquareCorrection_summable : Summable reciprocalSquareCorrection := by
  have hp : Summable (fun n : ℕ => 1 / (3 * ((n : ℝ)+1)^4)) := by
    have h := ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (4 : ℕ)))).mul_left (1/3 : ℝ)
    simpa only [Nat.cast_add, Nat.cast_one, one_div_mul_one_div] using h
  exact hp.of_norm_bounded (fun n => by
    simpa only [Real.norm_eq_abs] using (reciprocalSquareCorrection_bound n).2)

private theorem ordinary_hasSum_of_hasSum {a : ℕ → ℝ} {S : ℝ}
    (h : HasSum a S) : RealSeriesHasSum a S := by
  exact (realSequenceConverges_iff _ _).mpr
    (h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))

theorem acceleration_corrected_convergence :
    Specs.SingleVariableAnalysis.Ch11.Acceleration.correctedConvergence := by
  exact ⟨⟨_, ordinary_hasSum_of_hasSum reciprocalSquareTerm_summable.hasSum⟩,
    ⟨_, ordinary_hasSum_of_hasSum reciprocalSquareCorrection_summable.hasSum⟩,
    ⟨_, ordinary_hasSum_of_hasSum
      (summable_abs_iff.mpr reciprocalSquareCorrection_summable).hasSum⟩⟩

/-- The rational correction telescopes at every finite cut. -/
theorem reciprocalSquareCorrection_prefix (N : ℕ) :
    (∑ n ∈ Finset.range N, reciprocalSquareCorrection n) =
      (∑ n ∈ Finset.range N, reciprocalSquareTerm n) - 2 +
        1 / ((N : ℝ) + 1/2) := by
  have he : ∀ n : ℕ, reciprocalSquareCorrection n = reciprocalSquareTerm n -
      (1 / ((n : ℝ)+1/2) - 1 / (((n+1 : ℕ) : ℝ)+1/2)) := by
    intro n
    unfold reciprocalSquareCorrection reciprocalSquareTerm
    push_cast
    rw [show (n : ℝ)+1-1/2 = (n : ℝ)+1/2 by ring]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub']
  norm_num
  ring

private theorem half_reciprocal_limit :
    Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1/2)) atTop (𝓝 0) := by
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1/2 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem acceleration_corrected_identity :
    Specs.SingleVariableAnalysis.Ch11.Acceleration.correctedIdentity := by
  intro S C hS hC
  have hs : Tendsto (fun N => ∑ n ∈ Finset.range N, reciprocalSquareTerm n)
      atTop (𝓝 S) := (tendsto_add_atTop_iff_nat 1).mp
        ((realSequenceConverges_iff _ _).mp hS)
  have hc : Tendsto (fun N => ∑ n ∈ Finset.range N, reciprocalSquareCorrection n)
      atTop (𝓝 C) := (tendsto_add_atTop_iff_nat 1).mp
        ((realSequenceConverges_iff _ _).mp hC)
  have ht := (hs.sub_const 2).add half_reciprocal_limit
  simp only [add_zero] at ht
  have eqn : C = S - 2 := tendsto_nhds_unique hc
    (by simpa only [reciprocalSquareCorrection_prefix] using ht)
  linarith

/-- A telescoping majorant for the fourth-power tail. -/
theorem fourthPower_telescoping_bound (x : ℝ) (hx : 0 < x) :
    1 / (3 * (x+1)^4) ≤ 1 / (9*x^3) - 1 / (9*(x+1)^3) := by
  have he : 1 / (9*x^3) - 1 / (9*(x+1)^3) - 1 / (3*(x+1)^4) =
      (6*x^2+4*x+1) / (9*x^3*(x+1)^4) := by
    field_simp
    ring
  have hh : 0 ≤ (6*x^2+4*x+1) / (9*x^3*(x+1)^4) := by positivity
  linarith

/-- Uniform finite-tail bound, before passing to an ordinary sum. -/
theorem reciprocalSquareCorrection_finite_tail (N m : ℕ) (hN : 1 ≤ N) :
    |∑ i ∈ Finset.range m, reciprocalSquareCorrection (N+i)| ≤
      1 / (9 * (N : ℝ)^3) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  calc
    |∑ i ∈ Finset.range m, reciprocalSquareCorrection (N+i)| ≤
        ∑ i ∈ Finset.range m, |reciprocalSquareCorrection (N+i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m,
        (1 / (9*((N+i : ℕ) : ℝ)^3) - 1 / (9*((N+(i+1) : ℕ) : ℝ)^3)) := by
      apply Finset.sum_le_sum
      intro i _
      have h := fourthPower_telescoping_bound ((N+i : ℕ) : ℝ) (by push_cast; positivity)
      exact (reciprocalSquareCorrection_bound (N+i)).2.trans (by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h)
    _ = 1 / (9*(N : ℝ)^3) - 1 / (9*((N+m : ℕ) : ℝ)^3) := by
      simpa only [Nat.add_zero] using
        Finset.sum_range_sub' (fun i : ℕ => 1 / (9*((N+i : ℕ) : ℝ)^3)) m
    _ ≤ 1 / (9*(N : ℝ)^3) := sub_le_self _ (by positivity)

theorem acceleration_corrected_error :
    Specs.SingleVariableAnalysis.Ch11.Acceleration.correctedError := by
  intro S hS N hN
  let C := ∑' n, reciprocalSquareCorrection n
  have hC : RealSeriesHasSum reciprocalSquareCorrection C :=
    ordinary_hasSum_of_hasSum reciprocalSquareCorrection_summable.hasSum
  have hi := acceleration_corrected_identity S C hS hC
  have hc := reciprocalSquareCorrection_summable.hasSum.tendsto_sum_nat
  have ht := ((hc.comp (tendsto_add_atTop_nat N)).sub_const
    (∑ n ∈ Finset.range N, reciprocalSquareCorrection n)).abs
  have hb : |C - ∑ n ∈ Finset.range N, reciprocalSquareCorrection n| ≤
      1 / (9*(N : ℝ)^3) := by
    apply le_of_tendsto' ht
    intro m
    have he : (∑ n ∈ Finset.range (m+N), reciprocalSquareCorrection n) -
        (∑ n ∈ Finset.range N, reciprocalSquareCorrection n) =
        ∑ i ∈ Finset.range m, reciprocalSquareCorrection (N+i) := by
      rw [Nat.add_comm m N, Finset.sum_range_add]
      simp only [add_sub_cancel_left]
    simp only [Function.comp_def]
    rw [he]
    exact reciprocalSquareCorrection_finite_tail N m hN
  have he : S - (2 + ∑ n ∈ Finset.range N, reciprocalSquareCorrection n) =
      C - ∑ n ∈ Finset.range N, reciprocalSquareCorrection n := by linarith
  rwa [he]

end SingleVariableAnalysis
