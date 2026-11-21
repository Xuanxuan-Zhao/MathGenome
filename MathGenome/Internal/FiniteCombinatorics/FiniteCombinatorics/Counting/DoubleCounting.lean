import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.DoubleCounting

/-! Double counting an incidence relation (paper.tex, Proposition p204:W03). -/

universe u v

namespace FiniteCombinatorics.Counting

/-- Count each ordered pair of the relation once, first grouping by its first
coordinate and then by its second coordinate. Empty sets are allowed. -/
theorem incidence_count : Specs.FiniteCombinatorics.Counting.incidenceCount.{u, v} := by
  classical
  intro α β A B R hR
  have hfilter : (A.product B).filter (fun p => p ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hR h, h⟩⟩
  have hcount : R.card =
      ∑ a ∈ A, ∑ b ∈ B, if (a, b) ∈ R then 1 else 0 := by
    calc
      R.card = ((A.product B).filter (fun p => p ∈ R)).card :=
        congrArg Finset.card hfilter.symm
      _ = _ := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_product A B (fun p => if p ∈ R then 1 else 0)
  constructor
  · simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcount
  · rw [Finset.sum_comm] at hcount
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcount

end FiniteCombinatorics.Counting
