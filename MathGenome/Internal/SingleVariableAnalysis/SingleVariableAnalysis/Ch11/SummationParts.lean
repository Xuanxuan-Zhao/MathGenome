import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.SummationParts
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Ring

/-!
# Finite summation by parts

The global formula is Mathlib's finite Abel transformation, with its endpoints
and signs translated to the manuscript's convention. The tail formula is also
proved directly by induction on the upper endpoint. Both formulas allow `p = q`
and `p = 0`; the global lower boundary is a sum over `range p`, hence zero
at `p = 0`, rather than a partial sum evaluated at the natural number `p - 1`.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

/-- Finite Abel transformation in the source's global-prefix convention. -/
theorem summation_parts {K : Type*} [CommRing K]
    (a b : ℕ → K) (p q : ℕ) (hpq : p ≤ q) :
    (∑ n ∈ Finset.Icc p q, a n * b n) =
      (∑ j ∈ Finset.range (q + 1), a j) * b q -
        (∑ j ∈ Finset.range p, a j) * b p +
      ∑ n ∈ Finset.Ico p q,
        (∑ j ∈ Finset.range (n + 1), a j) * (b n - b (n + 1)) := by
  have h := Finset.sum_Ico_by_parts b a (Nat.lt_succ_of_le hpq)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, smul_eq_mul,
    Finset.Ico_add_one_right_eq_Icc] at h
  have hsign :
      (∑ n ∈ Finset.Ico p q,
        (b (n + 1) - b n) * (∑ j ∈ Finset.range (n + 1), a j)) =
      -(∑ n ∈ Finset.Ico p q,
        (∑ j ∈ Finset.range (n + 1), a j) * (b n - b (n + 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsign] at h
  simpa only [sub_neg_eq_add, mul_comm] using h

/-- The equivalent formula with partial sums anchored at the lower endpoint. -/
theorem summation_parts_tail {K : Type*} [CommRing K]
    (a b : ℕ → K) (p q : ℕ) (hpq : p ≤ q) :
    (∑ n ∈ Finset.Icc p q, a n * b n) =
      (∑ j ∈ Finset.Icc p q, a j) * b q +
      ∑ n ∈ Finset.Ico p q,
        (∑ j ∈ Finset.Icc p n, a j) * (b n - b (n + 1)) := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hpq), ih,
      Finset.sum_Ico_succ_top hpq,
      Finset.sum_Icc_succ_top (Nat.le_succ_of_le hpq)]
    ring

theorem summation_parts_real :
    Specs.SingleVariableAnalysis.Ch11.SummationParts.globalReal :=
  summation_parts

theorem summation_parts_complex :
    Specs.SingleVariableAnalysis.Ch11.SummationParts.globalComplex :=
  summation_parts

theorem summation_parts_tail_real :
    Specs.SingleVariableAnalysis.Ch11.SummationParts.tailReal :=
  summation_parts_tail

theorem summation_parts_tail_complex :
    Specs.SingleVariableAnalysis.Ch11.SummationParts.tailComplex :=
  summation_parts_tail

end SingleVariableAnalysis
