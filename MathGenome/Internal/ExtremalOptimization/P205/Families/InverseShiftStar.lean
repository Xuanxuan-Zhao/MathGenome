import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.InverseShiftStar
import MathGenome.Internal.ExtremalOptimization.P205.Families.Shifting
import Mathlib.Tactic.Tauto

namespace P205.Families.InverseShiftStar
open Finset Shifting

@[simp] theorem mem_fullStar {n k : ℕ} {c : Fin n} {A : Finset (Fin n)} :
    A ∈ fullStar k c ↔ A.card = k ∧ c ∈ A := by
  simp [fullStar]

lemma card_fullStar {n k : ℕ} (hk : 1 ≤ k) (c : Fin n) :
    (fullStar k c).card = (n - 1).choose (k - 1) := by
  simpa [fullStar] using
    card_filter_powersetCard_subset ({c} : Finset (Fin n)) univ k
      (subset_univ _) (by simpa using hk)

@[simp] lemma subset_avoid_pair {n : ℕ} {i j : Fin n} {D : Finset (Fin n)} :
    D ⊆ (univ \ {i, j}) ↔ i ∉ D ∧ j ∉ D := by
  simp [subset_sdiff, disjoint_insert_right]

/-- The lower member of each two-set compression fiber is present exactly when
at least one of the two original members was present. -/
lemma lower_mem_shift {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {D : Finset (Fin n)} (hi : i ∉ D) (hj : j ∉ D) (F : Family n) :
    insert i D ∈ shift i j F ↔ insert i D ∈ F ∨ insert j D ∈ F := by
  constructor
  · intro h
    by_cases hF : insert i D ∈ F
    · exact Or.inl hF
    · have h' := UV.sup_sdiff_mem_of_mem_compression_of_notMem h hF
      right
      simpa [sup_eq_union, sdiff_singleton_eq_erase, erase_insert_of_ne,
        erase_eq_of_notMem, hi, hj, hij, hij.symm] using h'
  · rintro (h | h)
    · have h' := UV.compress_mem_compression (u := {i}) (v := {j}) h
      simpa [shift, shift_rule i j hij] using h'
    · have h' := UV.compress_mem_compression (u := {i}) (v := {j}) h
      simpa [shift, shift_rule i j hij, hi, hj, hij] using h'

/-- The upper member survives exactly when both original members were present. -/
lemma upper_mem_shift {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {D : Finset (Fin n)} (hi : i ∉ D) (hj : j ∉ D) (F : Family n) :
    insert j D ∈ shift i j F ↔ insert i D ∈ F ∧ insert j D ∈ F := by
  constructor
  · intro h
    have hF := UV.mem_of_mem_compression h (by simp) (by simp)
    have h' := UV.sup_sdiff_mem_of_mem_compression h (by simp) (by simp [hi, hij])
    refine ⟨?_, hF⟩
    simpa [sup_eq_union, sdiff_singleton_eq_erase, erase_insert_of_ne,
      erase_eq_of_notMem, hi, hj, hij, hij.symm] using h'
  · intro h
    apply UV.mem_compression.mpr
    left
    refine ⟨h.2, ?_⟩
    simpa [shift, shift_rule i j hij, hi, hj, hij] using h.1

/-- Sets containing both shifted points, or neither, do not change membership. -/
lemma fixed_mem_shift {n : ℕ} {i j : Fin n} {A : Finset (Fin n)}
    (h : i ∈ A ↔ j ∈ A) (F : Family n) :
    A ∈ shift i j F ↔ A ∈ F := by
  have hc : UV.compress ({i} : Finset (Fin n)) {j} A = A := by
    unfold UV.compress
    simp only [disjoint_singleton_left, singleton_subset_iff]
    rw [ite_eq_right (by tauto)]
  constructor
  · intro hA
    by_cases hF : A ∈ F
    · exact hF
    · have hi := UV.le_of_mem_compression_of_notMem hA hF
      have hj := UV.disjoint_of_mem_compression_of_notMem hA hF
      simp only [singleton_subset_iff, disjoint_singleton_left] at hi hj
      exact (hj (h.mp hi)).elim
  · intro hF
    exact UV.mem_compression.mpr (Or.inl ⟨hF, hc.symm ▸ hF⟩)

/-- A predicate constant on disjoint rank-`r` subsets of a sufficiently large
finite ground set is constant on the entire rank. -/
lemma constant_of_disjoint {α : Type*} [DecidableEq α] (S : Finset α) (r : ℕ)
    (hsize : 2 * r < S.card) (P : Finset α → Prop)
    (hedge : ∀ A ⊆ S, A.card = r → ∀ B ⊆ S, B.card = r →
      Disjoint A B → (P A ↔ P B)) :
    ∀ A ⊆ S, A.card = r → ∀ B ⊆ S, B.card = r → (P A ↔ P B) := by
  intro A hAS hAr B hBS hBr
  revert hAS hAr
  induction A using (measure (fun C : Finset α => (C \ B).card)).wf.induction with
  | h A ih =>
    intro hAS hAr
    by_cases hab : A = B
    · subst A
      rfl
    have hnAB : ¬ A ⊆ B := fun h => hab (eq_of_subset_of_card_le h (by omega))
    have hnBA : ¬ B ⊆ A := fun h => hab (eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨x, hxA, hxB⟩ := not_subset.mp hnAB
    obtain ⟨y, hyB, hyA⟩ := not_subset.mp hnBA
    let C := insert y (A.erase x)
    have hCS : C ⊆ S := insert_subset (hBS hyB) ((erase_subset _ _).trans hAS)
    have hCr : C.card = r := by
      dsimp [C]
      rw [card_insert_of_notMem (notMem_mono (erase_subset _ _) hyA),
        card_erase_of_mem hxA, hAr]
      have := card_pos.mpr ⟨x, hxA⟩
      omega
    have hu : A ∪ C = insert y A := by
      ext z
      simp only [C, mem_union, mem_insert, mem_erase]
      tauto
    have huc : (A ∪ C).card = r + 1 := by
      rw [hu, card_insert_of_notMem hyA, hAr]
    have hroom : r ≤ (S \ (A ∪ C)).card := by
      rw [card_sdiff_of_subset (union_subset hAS hCS), huc]
      omega
    obtain ⟨T, hT, hTr⟩ := exists_subset_card_eq hroom
    have hTS : T ⊆ S := hT.trans sdiff_subset
    have hAT : Disjoint A T := disjoint_left.mpr fun z hzA hzT =>
      (mem_sdiff.mp (hT hzT)).2 (mem_union_left C hzA)
    have hCT : Disjoint C T := disjoint_left.mpr fun z hzC hzT =>
      (mem_sdiff.mp (hT hzT)).2 (mem_union_right A hzC)
    have hAC : P A ↔ P C :=
      (hedge A hAS hAr T hTS hTr hAT).trans (hedge C hCS hCr T hTS hTr hCT).symm
    have hd : C \ B = (A \ B).erase x := by
      ext z
      simp only [C, mem_sdiff, mem_insert, mem_erase]
      grind
    have hlt : (C \ B).card < (A \ B).card := by
      rw [hd]
      exact card_erase_lt_of_mem (mem_sdiff.mpr ⟨hxA, hxB⟩)
    exact hAC.trans (ih C hlt hCS hCr)

theorem inverse_shift_star : Expected.inverseShiftStar := by
  intro n k hk hn i j hij F hr hint c hs
  have hne : i ≠ j := ne_of_lt hij
  have finish (d : Fin n) (hd : ∀ A ∈ F, d ∈ A) : F = fullStar k d := by
    apply eq_of_subset_of_card_le
    · intro A hA
      exact mem_fullStar.mpr ⟨hr hA, hd A hA⟩
    · have heq := shift_card i j F
      rw [hs, card_fullStar hk c] at heq
      rw [card_fullStar hk d, heq]
  have hcompress (A : Finset (Fin n)) (hA : A ∈ F) :
      c ∈ UV.compress ({i} : Finset (Fin n)) {j} A := by
    have h := UV.compress_mem_compression (u := {i}) (v := {j}) hA
    change UV.compress ({i} : Finset (Fin n)) {j} A ∈ shift i j F at h
    rw [hs] at h
    exact (mem_fullStar.mp h).2
  by_cases hci : c = i
  swap
  · by_cases hcj : c = j
    swap
    · refine ⟨c, finish c ?_⟩
      intro A hA
      have h := hcompress A hA
      rw [shift_rule i j hne] at h
      split_ifs at h with hm
      · simpa [hci, hcj, mem_insert, mem_erase] using h
      · exact h
    · subst c
      let S : Finset (Fin n) := univ \ {i, j}
      have hSc : S.card = n - 2 := by
        simp [S, card_sdiff_of_subset (subset_univ _), hne]
      obtain ⟨D, hDS, hDr⟩ := exists_subset_card_eq (s := S) (n := k - 1)
        (by omega)
      obtain ⟨hiD, hjD⟩ := subset_avoid_pair.mp hDS
      have hu : insert j D ∈ shift i j F := by
        rw [hs, mem_fullStar, card_insert_of_notMem hjD, hDr]
        exact ⟨by omega, mem_insert_self _ _⟩
      have hl := UV.compress_mem_compression_of_mem_compression hu
      have hl' : insert i D ∈ shift i j F := by
        simpa [shift, shift_rule i j hne, hiD, hjD, hne] using hl
      rw [hs, mem_fullStar] at hl'
      simpa [hne.symm, hjD] using hl'.2
  · subst c
    let S : Finset (Fin n) := univ \ {i, j}
    have hSc : S.card = n - 2 := by
      simp [S, card_sdiff_of_subset (subset_univ _), hne]
    have pair (D : Finset (Fin n)) (hDS : D ⊆ S) (hDr : D.card = k - 1) :
        (insert i D ∈ F ∨ insert j D ∈ F) ∧
        ¬ (insert i D ∈ F ∧ insert j D ∈ F) := by
      obtain ⟨hiD, hjD⟩ := subset_avoid_pair.mp hDS
      constructor
      · apply (lower_mem_shift hne hiD hjD F).mp
        rw [hs, mem_fullStar, card_insert_of_notMem hiD, hDr]
        exact ⟨by omega, mem_insert_self _ _⟩
      · intro h
        have h' := (upper_mem_shift hne hiD hjD F).mpr h
        rw [hs, mem_fullStar] at h'
        simpa [hne, hiD] using h'.2
    have edge : ∀ A ⊆ S, A.card = k - 1 → ∀ B ⊆ S, B.card = k - 1 →
        Disjoint A B → (insert i A ∈ F ↔ insert i B ∈ F) := by
      intro A hAS hAr B hBS hBr hAB
      obtain ⟨hiA, hjA⟩ := subset_avoid_pair.mp hAS
      obtain ⟨hiB, hjB⟩ := subset_avoid_pair.mp hBS
      have cross : Disjoint (insert i A) (insert j B) := by
        simp [disjoint_insert_left, disjoint_insert_right, hne.symm, hiB, hjA, hAB]
      have cross' : Disjoint (insert j A) (insert i B) := by
        simp [disjoint_insert_left, disjoint_insert_right, hne, hjB, hiA, hAB]
      constructor
      · intro hA
        rcases (pair B hBS hBr).1 with hB | hB
        · exact hB
        · exact (hint hA hB cross).elim
      · intro hB
        rcases (pair A hAS hAr).1 with hA | hA
        · exact hA
        · exact (hint hA hB cross').elim
    have constancy := constant_of_disjoint S (k - 1) (by omega)
      (fun D => insert i D ∈ F) edge
    obtain ⟨D₀, hD₀S, hD₀r⟩ := exists_subset_card_eq (s := S) (n := k - 1) (by omega)
    have contains_either : ∀ A ∈ F, i ∈ A ∨ j ∈ A := by
      intro A hA
      have h := hcompress A hA
      rw [shift_rule i j hne] at h
      split_ifs at h with hm
      · exact Or.inr hm.2
      · exact Or.inl h
    by_cases hchoice : insert i D₀ ∈ F
    · refine ⟨i, finish i ?_⟩
      intro A hA
      by_contra hiA
      have hjA := (contains_either A hA).resolve_left hiA
      have hAS : A.erase j ⊆ S := subset_avoid_pair.mpr
        ⟨notMem_mono (erase_subset _ _) hiA, notMem_erase _ _⟩
      have hAr : (A.erase j).card = k - 1 := by rw [card_erase_of_mem hjA, hr hA]
      have hlo := (constancy D₀ hD₀S hD₀r (A.erase j) hAS hAr).mp hchoice
      exact (pair (A.erase j) hAS hAr).2 ⟨hlo, by simpa [insert_erase hjA] using hA⟩
    · refine ⟨j, finish j ?_⟩
      intro A hA
      by_contra hjA
      have hiA := (contains_either A hA).resolve_right hjA
      have hAS : A.erase i ⊆ S := subset_avoid_pair.mpr
        ⟨notMem_erase _ _, notMem_mono (erase_subset _ _) hjA⟩
      have hAr : (A.erase i).card = k - 1 := by rw [card_erase_of_mem hiA, hr hA]
      have hlo : insert i (A.erase i) ∈ F := by simpa [insert_erase hiA] using hA
      exact hchoice ((constancy D₀ hD₀S hD₀r (A.erase i) hAS hAr).mpr hlo)

end P205.Families.InverseShiftStar
