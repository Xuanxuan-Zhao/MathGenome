import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Scalar
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Archimedean
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Archimedean bounds and rational density

This proves all assertions of `K03.01.archimedean` (paper.tex:181–191).
Mathlib's real Archimedean instance and `exists_rat_btwn` apply to the same
canonical real field. The reciprocal limit is deduced directly from the
Archimedean bound, using its epsilon inequality rather than later limit algebra.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem archimedean_bound (x : ℝ) :
    ∃ n : ℕ, 0 < n ∧ x < (n : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max x 0)
  exact ⟨n, Nat.cast_pos.mp ((le_max_right x 0).trans_lt hn),
    (le_max_left x 0).trans_lt hn⟩

theorem rational_density (x y : ℝ) (hxy : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y :=
  exists_rat_btwn hxy

/-- Choosing `N > 1/ε` makes every positive reciprocal on the tail smaller
than `ε`. This also makes explicit the manuscript's positive-index convention. -/
theorem reciprocal_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → |1 / (n : ℝ)| < ε := by
  obtain ⟨N, hNpos, hN⟩ := archimedean_bound (1 / ε)
  refine ⟨N, hNpos, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (hNpos.trans_le hn)
  rw [abs_of_pos (one_div_pos.mpr hnpos)]
  exact (one_div_lt hnpos hε).mpr (hN.trans_le (Nat.cast_le.mpr hn))

theorem reciprocal_limit :
    Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hN n hn

theorem rational_approximation (x ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - x| < ε := by
  obtain ⟨q, hxq, hqx⟩ := rational_density x (x + ε) (lt_add_of_pos_right x hε)
  refine ⟨q, ?_⟩
  rw [abs_of_pos (sub_pos.mpr hxq)]
  exact sub_lt_iff_lt_add'.mpr hqx

end SingleVariableAnalysis
