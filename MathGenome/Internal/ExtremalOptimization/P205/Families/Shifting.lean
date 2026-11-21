import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.Shifting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs

namespace P205.Families.Shifting
open Finset

theorem shift_rule : Expected.shiftRule := by
  intro n i j hij A
  unfold UV.compress
  simp only [disjoint_singleton_left, singleton_subset_iff]
  split_ifs with h
  · ext a
    simp only [sup_eq_union, mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    grind only
  · rfl

theorem shift_card : Expected.cardinality := by
  intro n i j F
  exact UV.card_compression _ _ _

theorem shift_rank : Expected.rank := by
  intro n k i j F h
  exact h.uvCompression (by simp)

/-- A disjoint output pair has at most one moved member. The other member's
replacement was already present and gives a disjoint pair in the original family. -/
theorem shift_intersecting : Expected.intersection := by
  intro n i j hij F hF A hA B hB hAB
  simp only [Finset.mem_coe, shift] at hA hB
  have neij : i ≠ j := ne_of_lt hij
  have moved {C : Finset (Fin n)} (hC : C ∈ UV.compression {i} {j} F)
      (hnC : C ∉ F) : i ∈ C ∧ j ∉ C ∧ insert j (C.erase i) ∈ F := by
    have h₁ := UV.le_of_mem_compression_of_notMem hC hnC
    have h₂ := UV.disjoint_of_mem_compression_of_notMem hC hnC
    have h₃ := UV.sup_sdiff_mem_of_mem_compression_of_notMem hC hnC
    refine ⟨by simpa using h₁, by simpa using h₂, ?_⟩
    simpa only [sup_eq_union, union_singleton, sdiff_singleton_eq_erase,
      erase_insert_of_ne neij.symm] using h₃
  have mixed {C D : Finset (Fin n)} (hC : C ∈ UV.compression {i} {j} F)
      (hnC : C ∉ F) (hD : D ∈ UV.compression {i} {j} F) (hDF : D ∈ F)
      (hCD : Disjoint C D) : False := by
    obtain ⟨hiC, hjC, hCF⟩ := moved hC hnC
    have hiD : i ∉ D := fun hiD => disjoint_left.mp hCD hiC hiD
    have hjD : j ∈ D := by
      by_contra hn
      apply hF hCF hDF
      apply disjoint_left.mpr
      intro x hx hxD
      simp only [mem_insert, mem_erase] at hx
      rcases hx with rfl | ⟨_, hxC⟩
      · exact hn hxD
      · exact disjoint_left.mp hCD hxC hxD
    have hD' : insert i (D.erase j) ∈ F := by
      have hh := UV.sup_sdiff_mem_of_mem_compression hD
        (by simpa using hjD) (by simpa using hiD)
      simpa only [sup_eq_union, union_singleton, sdiff_singleton_eq_erase,
        erase_insert_of_ne neij] using hh
    apply hF hCF hD'
    apply disjoint_left.mpr
    intro x hx hxD
    simp only [mem_insert, mem_erase] at hx hxD
    rcases hx with rfl | ⟨hxi, hxC⟩
    · rcases hxD with hji | ⟨hjj, _⟩
      · exact neij hji.symm
      · exact hjj rfl
    · rcases hxD with rfl | ⟨_, hxD⟩
      · exact hxi rfl
      · exact disjoint_left.mp hCD hxC hxD
  by_cases hAF : A ∈ F
  · by_cases hBF : B ∈ F
    · exact hF hAF hBF hAB
    · exact mixed hB hBF hA hAF hAB.symm
  · by_cases hBF : B ∈ F
    · exact mixed hA hAF hB hBF hAB
    · exact disjoint_left.mp hAB (moved hA hAF).1 (moved hB hBF).1

private lemma point_sum_lt {n : ℕ} {i j : Fin n} (hij : i < j)
    {A : Finset (Fin n)} (hne : UV.compress ({i} : Finset (Fin n)) {j} A ≠ A) :
    (∑ x ∈ UV.compress ({i} : Finset (Fin n)) {j} A, x.val) < ∑ x ∈ A, x.val := by
  rw [shift_rule i j (ne_of_lt hij)] at hne ⊢
  split_ifs at hne ⊢ with h
  · rw [sum_insert (by simp [h.1])]
    have he := sum_erase_add A (fun x : Fin n => x.val) h.2
    have hij' : i.val < j.val := hij
    omega
  · exact (hne rfl).elim

/-- Separate retained members from moved members and sum the strict decrease
of the point-label sum over the nonempty moved part. -/
theorem shift_labelSum_lt : Expected.decrease := by
  intro n i j hij F hne
  change UV.compression {i} {j} F ≠ F at hne
  have moved_ne : ∀ A ∈ {A ∈ F | UV.compress {i} {j} A ∉ F},
      UV.compress {i} {j} A ≠ A := by
    intro A hA heq
    have hh := (mem_filter.mp hA).2
    exact hh (heq.symm ▸ (mem_filter.mp hA).1)
  have splitF : {A ∈ F | UV.compress {i} {j} A ∈ F} ∪
      {A ∈ F | UV.compress {i} {j} A ∉ F} = F := filter_union_filter_not_eq _ _
  have nonempty : {A ∈ F | UV.compress {i} {j} A ∉ F}.Nonempty := by
    contrapose! hne
    rw [UV.compression, filter_image, hne, image_empty, union_empty]
    rwa [hne, union_empty] at splitF
  change labelSum (UV.compression {i} {j} F) < labelSum F
  rw [UV.compression, labelSum, labelSum, sum_union UV.compress_disjoint]
  conv_rhs => rw [← splitF]
  rw [sum_union (disjoint_filter_filter_not _ _ _), add_lt_add_iff_left,
    filter_image, sum_image UV.compress_injOn]
  exact sum_lt_sum_of_nonempty nonempty fun A hA => point_sum_lt hij (moved_ne A hA)

theorem shifts_wellFounded : Expected.termination := by
  intro n
  apply (measure (@labelSum n)).wf.mono
  intro G F h
  obtain ⟨i, j, hij, hne, rfl⟩ := h
  exact shift_labelSum_lt i j hij F hne

/-- Termination and existence do not require uniformity or intersection. -/
theorem exists_stable : Expected.reachableStable := by
  intro n F
  induction F using (shifts_wellFounded n).induction with
  | h F ih =>
    by_cases stable : Stable F
    · exact ⟨F, Relation.ReflTransGen.refl, stable⟩
    · simp only [Stable, not_forall] at stable
      obtain ⟨i, j, hij, hne⟩ := stable
      have step : Step F (shift i j F) := ⟨i, j, hij, hne, rfl⟩
      obtain ⟨G, hFG, hG⟩ := ih (shift i j F) step
      exact ⟨G, hFG.head step, hG⟩

/-- The terminal family retains all three source invariants. -/
theorem exists_shifted : Expected.normalForm := by
  intro n k F hsize hinter
  induction F using (shifts_wellFounded n).induction generalizing k with
  | h F ih =>
    by_cases stable : Stable F
    · exact ⟨F, Relation.ReflTransGen.refl, stable, rfl, hsize, hinter⟩
    · have unst : ∃ i j : Fin n, i < j ∧ shift i j F ≠ F := by
        simp only [Stable, not_forall] at stable
        obtain ⟨i, j, hij, hne⟩ := stable
        exact ⟨i, j, hij, hne⟩
      obtain ⟨i, j, hij, hne⟩ := unst
      have step : Step F (shift i j F) := ⟨i, j, hij, hne, rfl⟩
      obtain ⟨G, hFG, hG, hcard, hsz, hint⟩ :=
        ih (shift i j F) step (shift_rank i j F hsize) (shift_intersecting i j hij F hinter)
      exact ⟨G, hFG.head step, hG, hcard.trans (shift_card i j F), hsz, hint⟩

end P205.Families.Shifting
