import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.BinomialQuantities
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.GeometricTailConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum

/-! Convergence of the source geometric majorant and its strict tails. -/

open scoped Topology BigOperators
open Filter

namespace D03SupportRepairs

/-- The source majorant is twice the geometric series with ratio one half. -/
theorem geomTerm_summable : Summable (fun j : ℕ => geomTerm j) := by
  exact (summable_geometric_of_lt_one (r := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)).mul_left 2

/-- Restricting the summable majorant to a strict tail preserves summability. -/
theorem geometricTail_summable (J : ℕ) :
    Summable (fun j : ℕ => if J < j then geomTerm j else 0) := by
  refine (geomTerm_summable.indicator {j : ℕ | J < j}).congr ?_
  intro j
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- The terms, and therefore the actual tails, are nonnegative. -/
theorem geometricTail_nonneg (J : ℕ) : 0 ≤ geometricTail J := by
  apply tsum_nonneg
  intro j
  split_ifs
  · exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  · exact le_refl 0

/-- Padding by zeros is equivalent to shifting the original series past the cutoff. -/
theorem geometricTail_eq_tsum_shift (J : ℕ) :
    geometricTail J = ∑' k : ℕ, geomTerm (k + (J + 1)) := by
  have h := (geometricTail_summable J).sum_add_tsum_nat_add (J + 1)
  have hzero : (∑ j ∈ Finset.range (J + 1),
      if J < j then geomTerm j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp [Nat.not_lt_of_ge hj']
  have hshift : (fun k : ℕ => if J < k + (J + 1) then geomTerm (k + (J + 1)) else 0) =
      (fun k : ℕ => geomTerm (k + (J + 1))) := by
    funext k
    simp only [ite_eq_left (by omega : J < k + (J + 1))]
  rw [hzero, zero_add, hshift] at h
  exact h.symm

/-- The actual strict geometric tails vanish at infinity. -/
theorem geometricTail_tendsto :
    Tendsto geometricTail atTop (nhds (0 : ℝ)) := by
  change Tendsto (fun J => geometricTail J) atTop (nhds (0 : ℝ))
  simp_rw [geometricTail_eq_tsum_shift]
  exact (tendsto_sum_nat_add geomTerm).comp (tendsto_add_atTop_nat 1)

end D03SupportRepairs
