import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.UniqueLimit
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniqueness, boundedness, and finite prefixes

This implements `K03.01.unique_limit`. The upstream epsilon definitions
are identified with the canonical metric filters before applying uniqueness
in a Hausdorff space and boundedness of the range of a convergent sequence.
The latter is a bound on all indices, not just on a tail.

Finite changes give eventual equality because every finite subset of `ℕ`
is bounded above. Translation of `atTop` by any natural number is `atTop`,
which gives both directions of deleting or restoring a finite prefix.
No completeness of the complex numbers is needed for these results.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem real_limit_unique (a : ℕ → ℝ) (L M : ℝ)
    (hL : RealSequenceConverges a L) (hM : RealSequenceConverges a M) : L = M :=
  tendsto_nhds_unique ((realSequenceConverges_iff a L).mp hL)
    ((realSequenceConverges_iff a M).mp hM)

theorem complex_limit_unique (a : ℕ → ℂ) (L M : ℂ)
    (hL : ComplexSequenceConverges a L) (hM : ComplexSequenceConverges a M) : L = M :=
  tendsto_nhds_unique ((complexSequenceConverges_iff a L).mp hL)
    ((complexSequenceConverges_iff a M).mp hM)

theorem real_convergent_bounded (a : ℕ → ℝ) (L : ℝ)
    (h : RealSequenceConverges a L) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |a n| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ :=
    (Metric.isBounded_range_of_tendsto a ((realSequenceConverges_iff a L).mp h)).exists_pos_norm_le
  refine ⟨C, hCpos.le, fun n => ?_⟩
  simpa only [Real.norm_eq_abs] using hC (a n) (Set.mem_range_self n)

theorem complex_convergent_bounded (a : ℕ → ℂ) (L : ℂ)
    (h : ComplexSequenceConverges a L) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖a n‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ :=
    (Metric.isBounded_range_of_tendsto a ((complexSequenceConverges_iff a L).mp h)).exists_pos_norm_le
  exact ⟨C, hCpos.le, fun n => hC (a n) (Set.mem_range_self n)⟩

private theorem eventually_eq_of_finite_ne {α : Type*} (a b : ℕ → α)
    (h : Set.Finite {n | a n ≠ b n}) : a =ᶠ[Filter.atTop] b := by
  obtain ⟨N, hN⟩ := h.bddAbove
  apply Filter.eventually_atTop.mpr
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hle : n ≤ N := hN hne
  exact (Nat.not_succ_le_self N) (le_trans hn hle)

theorem real_finite_changes_iff (a b : ℕ → ℝ)
    (h : Set.Finite {n | a n ≠ b n}) (L : ℝ) :
    RealSequenceConverges a L ↔ RealSequenceConverges b L := by
  rw [realSequenceConverges_iff, realSequenceConverges_iff]
  have hab := eventually_eq_of_finite_ne a b h
  exact ⟨fun ha => ha.congr' hab, fun hb => hb.congr' hab.symm⟩

theorem complex_finite_changes_iff (a b : ℕ → ℂ)
    (h : Set.Finite {n | a n ≠ b n}) (L : ℂ) :
    ComplexSequenceConverges a L ↔ ComplexSequenceConverges b L := by
  rw [complexSequenceConverges_iff, complexSequenceConverges_iff]
  have hab := eventually_eq_of_finite_ne a b h
  exact ⟨fun ha => ha.congr' hab, fun hb => hb.congr' hab.symm⟩

/-- Deleting the first `k` terms preserves, and reflects, the given finite limit. -/
theorem real_shift_iff (a : ℕ → ℝ) (L : ℝ) (k : ℕ) :
    RealSequenceConverges (fun n => a (n + k)) L ↔ RealSequenceConverges a L := by
  rw [realSequenceConverges_iff, realSequenceConverges_iff]
  exact Filter.tendsto_add_atTop_iff_nat k

theorem complex_shift_iff (a : ℕ → ℂ) (L : ℂ) (k : ℕ) :
    ComplexSequenceConverges (fun n => a (n + k)) L ↔ ComplexSequenceConverges a L := by
  rw [complexSequenceConverges_iff, complexSequenceConverges_iff]
  exact Filter.tendsto_add_atTop_iff_nat k

end SingleVariableAnalysis
