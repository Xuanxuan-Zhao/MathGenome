import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.SortedUnion
import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.MarkedCellBudget
import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.LocalizedComparison
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.QuantitativeInsertion
import Mathlib.Tactic.NormNum

namespace D03Insertion

/-- Insert the nodes of any partition into an arbitrarily tagged partition.
The same refined tags preserve every unmarked cell and satisfy the stronger
2Mm|Q| bound, the source's 4Mm|Q| bound, and exact equality when Mm = 0.
This applies in particular to both real and complex valued functions. -/
theorem quantitative_insertion : Specification.quantitative_insertionType := by
  intro K _ _ a b hab s n hs hn p q hp hq hp0 hps hq0 hqn f M hM hf ξ hξ
  have hpv : ValidPartition a b p := ⟨hs, hp, hp0, hps⟩
  have hqv : ValidPartition a b q := ⟨hn, hq, hq0, hqn⟩
  obtain ⟨t, r, hr, hu⟩ := sorted_union_partition hab p q hpv hqv
  obtain ⟨ζ, hζ, hpreserve, hlocal⟩ :=
    localized_tagged_sum_comparison hab hpv hqv hr hu f M hM hf ξ hξ
  have hstrong : ‖taggedSum f q ξ - taggedSum f r ζ‖ ≤
      2 * M * ((s - 1 : ℕ) : ℝ) * mesh q := by
    calc
      _ ≤ 2 * M * (∑ i ∈ marked p q, width q i) := hlocal
      _ ≤ 2 * M * (((s - 1 : ℕ) : ℝ) * mesh q) :=
        mul_le_mul_of_nonneg_left (marked_length_budget hab hpv hqv).2
          (mul_nonneg (by norm_num) hM)
      _ = _ := by ring
  refine ⟨t, r, ζ, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hu, hζ, ?_, hstrong, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, _⟩ := unmarked_cell_exists_unique hpv hqv hr hu i hi
    exact ⟨j, hj.1, hj.2, hpreserve i hi j hj.1 hj.2⟩
  · exact hstrong.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hM)
        (Nat.cast_nonneg _)) (mesh_nonneg q))
  · intro hzero
    have hz : ‖taggedSum f q ξ - taggedSum f r ζ‖ ≤ 0 := by
      calc
        _ ≤ 2 * M * ((s - 1 : ℕ) : ℝ) * mesh q := hstrong
        _ = 2 * (M * ((s - 1 : ℕ) : ℝ)) * mesh q := by ring
        _ = 0 := by rw [hzero]; simp
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end D03Insertion
