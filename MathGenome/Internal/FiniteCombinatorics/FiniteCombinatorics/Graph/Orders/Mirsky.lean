import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Orders.Mirsky

open Finset
open scoped Classical

namespace FiniteCombinatorics.Mirsky

variable {P : Type*} [PartialOrder P] [Fintype P]

lemma chain_card_le_height (C : Finset P) (hC : IsChain (· ≤ ·) (C : Set P)) :
    C.card ≤ height P := by
  classical
  exact Finset.le_sup (by simp [hC] : C ∈ (univ : Finset (Finset P)).filter
    (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P)))

lemma height_attained : ∃ C : Finset P,
    IsChain (· ≤ ·) (C : Set P) ∧ C.card = height P := by
  classical
  have hne : ((univ : Finset (Finset P)).filter
      (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P))).Nonempty := by
    exact ⟨∅, by simp⟩
  obtain ⟨C, hC, heq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨C, (mem_filter.mp hC).2, heq.symm⟩

theorem terminal_attained (P : Type*) [PartialOrder P] [Fintype P] (x : P) :
    ∃ C : Finset P, IsChain (· ≤ ·) (C : Set P) ∧ x ∈ C ∧
      (∀ y ∈ C, y ≤ x) ∧ C.card = terminalLength P x := by
  classical
  have hne : ((univ : Finset (Finset P)).filter
      (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P) ∧ x ∈ C ∧ ∀ y ∈ C, y ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp
  obtain ⟨C, hC, heq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨C, (mem_filter.mp hC).2.1, (mem_filter.mp hC).2.2.1,
    (mem_filter.mp hC).2.2.2, heq.symm⟩

lemma card_le_terminalLength (x : P) (C : Finset P)
    (hc : IsChain (· ≤ ·) (C : Set P)) (hx : x ∈ C) (hmax : ∀ y ∈ C, y ≤ x) :
    C.card ≤ terminalLength P x := by
  classical
  exact Finset.le_sup (show C ∈ (univ : Finset (Finset P)).filter
    (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P) ∧ x ∈ C ∧ ∀ y ∈ C, y ≤ x) from
      mem_filter.mpr ⟨mem_univ _, hc, hx, hmax⟩)

theorem terminal_strictMono (P : Type*) [PartialOrder P] [Fintype P] :
    StrictMono (terminalLength P) := by
  classical
  intro x y hxy
  obtain ⟨C, hc, hx, hm, he⟩ := terminal_attained P x
  have hy : y ∉ C := fun h => (not_le_of_gt hxy) (hm y h)
  have hc' : IsChain (· ≤ ·) ((insert y C : Finset P) : Set P) := by
    rw [coe_insert]
    exact hc.insert (fun z hz _ => Or.inr ((hm z hz).trans hxy.le))
  have hb := card_le_terminalLength y (insert y C) hc' (mem_insert_self _ _) (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact (hm z hz).trans hxy.le)
  rw [card_insert_of_notMem hy, he] at hb
  omega

lemma terminal_pos (x : P) : 0 < terminalLength P x := by
  obtain ⟨C, _, hx, _, he⟩ := terminal_attained P x
  rw [← he]
  exact card_pos.mpr ⟨x, hx⟩

lemma terminal_le_height (x : P) : terminalLength P x ≤ height P := by
  obtain ⟨C, hc, _, _, he⟩ := terminal_attained P x
  rw [← he]
  exact chain_card_le_height C hc

/-- A level, indexed from zero so that there are exactly `height P` possible indices. -/
private noncomputable def level (i : ℕ) : Finset P :=
  univ.filter (fun x => terminalLength P x = i + 1)

private lemma level_mem (x : P) (i : ℕ) :
    x ∈ level (P := P) i ↔ terminalLength P x = i + 1 := by
  simp [level]

private noncomputable def levelParts : Finset (Finset P) :=
  ((range (height P)).image (level (P := P))).erase ∅

private lemma levelParts_cover (x : P) :
    ∃! A, A ∈ levelParts (P := P) ∧ x ∈ A := by
  classical
  have hp := terminal_pos x
  have hb := terminal_le_height x
  have hx : x ∈ level (P := P) (terminalLength P x - 1) := by
    rw [level_mem]
    omega
  have hi : terminalLength P x - 1 ∈ range (height P) := by
    simp only [mem_range]
    omega
  refine ⟨level (P := P) (terminalLength P x - 1), ⟨?_, hx⟩, ?_⟩
  · exact mem_erase.mpr ⟨ne_empty_of_mem hx, mem_image.mpr ⟨_, hi, rfl⟩⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_erase.mp hA.1).2
    have hh := (level_mem x i).mp hA.2
    congr 1
    omega

private noncomputable def levelPartition : Finpartition (univ : Finset P) :=
  Finpartition.ofExistsUnique (levelParts (P := P)) (fun _ _ => subset_univ _)
    (fun x _ => levelParts_cover x) (notMem_erase _ _)

private lemma levelPartition_antichain :
    IsAntichainPartition P (levelPartition (P := P)) := by
  classical
  intro A hA x hx y hy hne hxy
  obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_erase.mp hA).2
  have hx' := (level_mem x i).mp hx
  have hy' := (level_mem y i).mp hy
  have hh := terminal_strictMono P (lt_of_le_of_ne hxy hne)
  omega

private lemma levelPartition_card_le :
    (levelPartition (P := P)).parts.card ≤ height P := by
  exact card_erase_le.trans (card_image_le.trans (by rw [card_range]))

lemma chain_card_le_partition (C : Finset P) (hc : IsChain (· ≤ ·) (C : Set P))
    (Q : Finpartition (univ : Finset P)) (hQ : IsAntichainPartition P Q) :
    C.card ≤ Q.parts.card := by
  classical
  apply card_le_card_of_injOn Q.part
  · intro x _
    exact Q.part_mem.mpr (mem_univ x)
  · intro x hx y hy heq
    have hxp := Q.mem_part (mem_univ x)
    have hyp := Q.mem_part (mem_univ y)
    rw [← heq] at hyp
    rcases hc.total hx hy with hxy | hyx
    · exact (hQ _ (Q.part_mem.mpr (mem_univ x))).eq hxp hyp hxy
    · exact (hQ _ (Q.part_mem.mpr (mem_univ x))).eq' hxp hyp hyx

theorem mirsky (P : Type*) [PartialOrder P] [Fintype P] :
    (∃ C : Finset P, IsChain (· ≤ ·) (C : Set P) ∧ C.card = height P) ∧
    (∃ Q : Finpartition (univ : Finset P), IsAntichainPartition P Q ∧ Q.parts.card = height P) ∧
    (∀ C : Finset P, IsChain (· ≤ ·) (C : Set P) → C.card ≤ height P) ∧
    (∀ Q : Finpartition (univ : Finset P), IsAntichainPartition P Q → height P ≤ Q.parts.card) := by
  classical
  obtain ⟨C, hc, he⟩ := height_attained (P := P)
  have lower : ∀ Q : Finpartition (univ : Finset P),
      IsAntichainPartition P Q → height P ≤ Q.parts.card := by
    intro Q hQ
    rw [← he]
    exact chain_card_le_partition C hc Q hQ
  refine ⟨⟨C, hc, he⟩, ⟨levelPartition, levelPartition_antichain, ?_⟩,
    chain_card_le_height, lower⟩
  exact le_antisymm levelPartition_card_le (lower _ levelPartition_antichain)

theorem count_eq_height (P : Type*) [PartialOrder P] [Fintype P] :
    antichainCount P = height P := by
  obtain ⟨_, ⟨Q, hQ, he⟩, _, lower⟩ := mirsky P
  apply le_antisymm
  · exact Nat.sInf_le ⟨Q, hQ, he⟩
  · apply le_csInf
    · exact ⟨height P, Q, hQ, he⟩
    · rintro k ⟨R, hR, rfl⟩
      exact lower R hR

theorem empty_case (P : Type*) [PartialOrder P] [Fintype P] [IsEmpty P] :
    height P = 0 ∧ antichainCount P = 0 ∧
    ∃ Q : Finpartition (univ : Finset P), Q.parts = ∅ ∧ IsAntichainPartition P Q := by
  classical
  have hh : height P = 0 := by
    obtain ⟨C, _, he⟩ := height_attained (P := P)
    rw [← he]
    have : C = ∅ := Subsingleton.elim _ _
    simp [this]
  refine ⟨hh, (count_eq_height P).trans hh, ?_⟩
  obtain ⟨Q, hQ, hcard⟩ := (mirsky P).2.1
  exact ⟨Q, card_eq_zero.mp (hcard.trans hh), hQ⟩

end FiniteCombinatorics.Mirsky
