import MathGenome.Internal.Specs.D05.Foundations.SubsetCount
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The finite-combinatorics paragraph of paper.tex:352.
The equivalence below connects actual lists to injections from their ordered
positions. Thus the embedding count counts lists, not just an auxiliary object.
-/
namespace D05.Foundations.SubsetCount
open D05.Foundations

/-- Distinct lists and injections from their ordered positions describe the same data. -/
noncomputable def distinctListsEquivEmbedding (α : Type*) (p : ℕ) :
    DistinctLists α p ≃ (Fin p ↪ α) := by
  let f : (Fin p ↪ α) → DistinctLists α p := fun e =>
    ⟨List.ofFn e, List.length_ofFn, List.nodup_ofFn.mpr e.injective⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro e e' h
    apply DFunLike.ext
    have hf := List.ofFn_injective (congrArg Subtype.val h)
    exact congrFun hf
  · rintro ⟨l, hlen, hnd⟩
    subst p
    refine ⟨⟨l.get, hnd.injective_get⟩, ?_⟩
    exact Subtype.ext (List.ofFn_get l)

/-- The finite embedding formula applied to actual lists. -/
theorem distinctLists_card (α : Type*) [Fintype α] (p : ℕ) :
    Nat.card (DistinctLists α p) = (Fintype.card α).descFactorial p := by
  classical
  rw [Nat.card_congr (distinctListsEquivEmbedding α p), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- A nonrepeating list of full length contains every element, and conversely. -/
noncomputable def orderingsEquivDistinctLists (α : Type*) [Fintype α] :
    Orderings α ≃ DistinctLists α (Fintype.card α) := by
  classical
  apply Equiv.subtypeEquivRight
  intro l
  constructor
  · rintro ⟨hnd, hmem⟩
    refine ⟨?_, hnd⟩
    have hfull : l.toFinset = Finset.univ := by ext a; simp [hmem a]
    rw [← List.toFinset_card_of_nodup hnd, hfull, Finset.card_univ]
  · rintro ⟨hlen, hnd⟩
    refine ⟨hnd, ?_⟩
    have hfull : l.toFinset = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [List.toFinset_card_of_nodup hnd, hlen]
    intro a
    have : a ∈ l.toFinset := by rw [hfull]; exact Finset.mem_univ a
    simpa using this

theorem subset_count : D05SubsetCountSpec.subset_count := by
  intro α s n p hs
  simpa only [hs] using Finset.card_powersetCard p s

theorem ordered_list_count : D05SubsetCountSpec.ordered_list_count := by
  intro α s n p hs
  rw [distinctLists_card, Fintype.card_coe, hs, Nat.descFactorial_eq_prod_range]

theorem orderings_count : D05SubsetCountSpec.orderings_count := by
  intro α t p ht
  rw [Nat.card_congr (orderingsEquivDistinctLists t), distinctLists_card,
    Nat.descFactorial_self, Fintype.card_coe, ht]

theorem double_count : D05SubsetCountSpec.double_count := by
  intro α s p
  rw [distinctLists_card, Fintype.card_coe, Finset.card_powersetCard,
    Nat.descFactorial_eq_factorial_mul_choose]

theorem quotient_formula : D05SubsetCountSpec.quotient_formula := by
  intro α s n p hs
  rw [← ordered_list_count s n p hs, double_count,
    Nat.mul_div_cancel_left _ (Nat.factorial_pos p)]

theorem above_card : D05SubsetCountSpec.above_card := by
  intro α s n p hs hp
  have hz : (s.powersetCard p).card = 0 := by
    rw [subset_count s n p hs, Nat.choose_eq_zero_of_lt hp]
  exact ⟨hz, by rw [double_count, hz, Nat.mul_zero]⟩

theorem degree_zero : D05SubsetCountSpec.degree_zero := by
  intro α s
  constructor
  · rw [subset_count s s.card 0 rfl, Nat.choose_zero_right]
  · rw [double_count, subset_count s s.card 0 rfl, Nat.choose_zero_right,
      Nat.factorial_zero, Nat.mul_one]

end D05.Foundations.SubsetCount
