import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Tabloids
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardTableaux
import Lean.Elab.Tactic.Omega

noncomputable section
namespace AdvancedFiniteGroupRepresentations

abbrev RowIncreasing := @Specs.AdvancedFiniteGroupRepresentations.RowIncreasing
abbrev ColumnIncreasing := @Specs.AdvancedFiniteGroupRepresentations.ColumnIncreasing
abbrev IsStandard := @Specs.AdvancedFiniteGroupRepresentations.IsStandard
abbrev StandardTableau := @Specs.AdvancedFiniteGroupRepresentations.StandardTableau
abbrev standardTableauCount := @Specs.AdvancedFiniteGroupRepresentations.standardTableauCount
abbrev IsRemovable := @Specs.AdvancedFiniteGroupRepresentations.IsRemovable
abbrev RemovableCell := @Specs.AdvancedFiniteGroupRepresentations.RemovableCell
abbrev deletedDiagram := @Specs.AdvancedFiniteGroupRepresentations.deletedDiagram
abbrev deleteCell := @Specs.AdvancedFiniteGroupRepresentations.deleteCell
abbrev IsAddable := @Specs.AdvancedFiniteGroupRepresentations.IsAddable
abbrev AddableCell := @Specs.AdvancedFiniteGroupRepresentations.AddableCell
abbrev adjoinedDiagram := @Specs.AdvancedFiniteGroupRepresentations.adjoinedDiagram
abbrev addCell := @Specs.AdvancedFiniteGroupRepresentations.addCell
abbrev lastLabelSubgroup := @Specs.AdvancedFiniteGroupRepresentations.lastLabelSubgroup
abbrev extendPermutation := @Specs.AdvancedFiniteGroupRepresentations.extendPermutation
abbrev hook := @Specs.AdvancedFiniteGroupRepresentations.hook
abbrev hookLength := @Specs.AdvancedFiniteGroupRepresentations.hookLength


variable {n : ℕ} {p : Partition n}

theorem standardTableau_finite (p : Partition n) : Finite (StandardTableau p) := by
  unfold StandardTableau Specs.AdvancedFiniteGroupRepresentations.StandardTableau
  infer_instance

theorem emptyTableau_standard : IsStandard emptyTableau := by
  constructor <;> intro a b <;> exact Fin.elim0 (emptyTableau a)

theorem empty_standardTableau_unique :
    ∃! t : StandardTableau emptyPartition, t.val = emptyTableau := by
  refine ⟨⟨emptyTableau, emptyTableau_standard⟩, rfl, ?_⟩
  intro t ht
  exact Subtype.ext ht

theorem empty_standardTableauCount : standardTableauCount emptyPartition = 1 := by
  let : Unique (StandardTableau emptyPartition) :=
    { default := ⟨emptyTableau, emptyTableau_standard⟩
      uniq := fun t => Subtype.ext (empty_tableau_unique t.val) }
  exact Nat.card_unique

theorem removable_iff_exists_diagram (p : Partition n) (c : ℕ × ℕ) :
    IsRemovable p c ↔ c ∈ cells p ∧ ∃ d : YoungDiagram, d.cells = (cells p).erase c := by
  constructor
  · intro h
    exact ⟨h.1, ⟨(cells p).erase c, h.2⟩, rfl⟩
  · rintro ⟨hc, d, hd⟩
    exact ⟨hc, hd ▸ d.isLowerSet⟩

theorem removable_iff_row_end (p : Partition n) (c : ℕ × ℕ) :
    IsRemovable p c ↔ c.2 + 1 = rowLength p c.1 ∧
      rowLength p (c.1 + 1) < rowLength p c.1 := by
  rcases c with ⟨i,j⟩
  constructor
  · intro h
    have hc := (cell_iff p i j).mp h.1
    have hr : rowLength p i ≤ j + 1 := by
      by_contra hn
      have hy : (i,j+1) ∈ (cells p).erase (i,j) :=
        Finset.mem_erase.mpr ⟨by simp, (cell_iff p _ _).mpr (by omega)⟩
      have hx := h.2 (show (i,j) ≤ (i,j+1) from ⟨le_rfl, by omega⟩) hy
      exact (Finset.notMem_erase _ _) hx
    have hb : rowLength p (i+1) ≤ j := by
      by_contra hn
      have hy : (i+1,j) ∈ (cells p).erase (i,j) :=
        Finset.mem_erase.mpr ⟨by simp, (cell_iff p _ _).mpr (by omega)⟩
      have hx := h.2 (show (i,j) ≤ (i+1,j) from ⟨by omega, le_rfl⟩) hy
      exact (Finset.notMem_erase _ _) hx
    dsimp at *
    omega
  · rintro ⟨hr,hb⟩
    have hc : (i,j) ∈ cells p := (cell_iff p _ _).mpr (by dsimp at hr; omega)
    refine ⟨hc, ?_⟩
    intro y x hxy hy
    rcases x with ⟨a,b⟩
    rcases y with ⟨r,s⟩
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
    have hx : (a,b) ∈ cells p := (diagram p).isLowerSet hxy hy
    refine Finset.mem_erase.mpr ⟨?_, hx⟩
    intro heq
    cases heq
    have hrow := (cell_iff p r s).mp hy
    have hle : i ≤ r := hxy.1
    have hj : j ≤ s := hxy.2
    have hri := rowLength_antitone p hle
    have hir : r ≤ i := by
      by_contra hn
      have hh := rowLength_antitone p (show i+1 ≤ r by omega)
      dsimp at hr hb
      omega
    have req : r = i := by omega
    have seq : s = j := by dsimp at hr; omega
    exact hne (Prod.ext req seq)

theorem deleteCell_cells (p : Partition n) (c : RemovableCell p) :
    cells (deleteCell p c) = (cells p).erase c.val := by
  exact congrArg YoungDiagram.cells (YoungDiagram.ofPartition_toPartition _)

theorem addable_iff_exists_diagram (p : Partition n) (c : ℕ × ℕ) :
    IsAddable p c ↔ c ∉ cells p ∧ ∃ d : YoungDiagram, d.cells = insert c (cells p) := by
  constructor
  · intro h
    exact ⟨h.1, ⟨insert c (cells p), h.2⟩, rfl⟩
  · rintro ⟨hc, d, hd⟩
    exact ⟨hc, hd ▸ d.isLowerSet⟩

theorem addable_iff_row_end (p : Partition n) (c : ℕ × ℕ) :
    IsAddable p c ↔ c.2 = rowLength p c.1 ∧
      (c.1 = 0 ∨ rowLength p c.1 < rowLength p (c.1 - 1)) := by
  rcases c with ⟨i,j⟩
  constructor
  · intro h
    have hn : rowLength p i ≤ j := Nat.le_of_not_gt (fun hc => h.1 ((cell_iff p i j).mpr hc))
    have hx := h.2 (show (i,rowLength p i) ≤ (i,j) from ⟨le_rfl, hn⟩)
      (show (i,j) ∈ insert (i,j) (cells p) from Finset.mem_insert_self _ _)
    have heq : j = rowLength p i := by
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact (congrArg Prod.snd hx).symm
      · have := (cell_iff p _ _).mp hx
        omega
    refine ⟨heq, ?_⟩
    by_cases hi : i = 0
    · exact Or.inl hi
    · right
      have hx := h.2 (show (i-1,j) ≤ (i,j) from ⟨by omega, le_rfl⟩)
        (show (i,j) ∈ insert (i,j) (cells p) from Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp hx with hx | hx
      · have := congrArg Prod.fst hx
        omega
      · simpa only [heq] using (cell_iff p _ _).mp hx
  · rintro ⟨heq,hi⟩
    dsimp only [Prod.fst, Prod.snd] at heq hi
    have hn : (i,j) ∉ cells p := by rw [cell_iff, heq]; exact Nat.lt_irrefl _
    refine ⟨hn, ?_⟩
    intro y x hxy hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rcases x with ⟨a,b⟩
      by_cases hx : (a,b) = (i,j)
      · exact Finset.mem_insert.mpr (Or.inl hx)
      · apply Finset.mem_insert_of_mem
        apply (cell_iff p a b).mpr
        have ha : a ≤ i := hxy.1
        have hb : b ≤ j := hxy.2
        by_cases hai : a = i
        · have hbj : b < j := by
            by_contra hh
            exact hx (Prod.ext hai (by omega))
          simpa only [hai, heq] using hbj
        · have hai' : a ≤ i - 1 := by omega
          have hr := rowLength_antitone p hai'
          rcases hi with hi | hi
          · omega
          · omega
    · exact Finset.mem_insert_of_mem ((diagram p).isLowerSet hxy hy)

theorem addCell_cells (p : Partition n) (c : AddableCell p) :
    cells (addCell p c) = insert c.val (cells p) := by
  exact congrArg YoungDiagram.cells (YoungDiagram.ofPartition_toPartition _)

theorem deleted_cell_addable (p : Partition n) (c : RemovableCell p) :
    IsAddable (deleteCell p c) c.val := by
  change c.val ∉ cells (deleteCell p c) ∧
    IsLowerSet (↑(insert c.val (cells (deleteCell p c))) : Set (ℕ × ℕ))
  constructor
  · rw [deleteCell_cells]; exact Finset.notMem_erase _ _
  · rw [deleteCell_cells, Finset.insert_erase c.property.1]
    exact (diagram p).isLowerSet

theorem adjoined_cell_removable (p : Partition n) (c : AddableCell p) :
    IsRemovable (addCell p c) c.val := by
  change c.val ∈ cells (addCell p c) ∧
    IsLowerSet (↑((cells (addCell p c)).erase c.val) : Set (ℕ × ℕ))
  constructor
  · rw [addCell_cells]; exact Finset.mem_insert_self _ _
  · rw [addCell_cells, Finset.erase_insert c.property.1]
    exact (diagram p).isLowerSet


@[simp] theorem extendPermutation_castSucc (g : SymmetricGroup n) (i : Fin n) :
    extendPermutation g i.castSucc = (g i).castSucc := by
  simp [extendPermutation, Specs.AdvancedFiniteGroupRepresentations.extendPermutation]

@[simp] theorem extendPermutation_last (g : SymmetricGroup n) :
    extendPermutation g (Fin.last n) = Fin.last n := by
  simp [extendPermutation, Specs.AdvancedFiniteGroupRepresentations.extendPermutation]

theorem extendPermutation_one (n : ℕ) : extendPermutation (1 : SymmetricGroup n) = 1 := by
  ext i
  cases i using Fin.lastCases <;> simp

theorem extendPermutation_mul (g h : SymmetricGroup n) :
    extendPermutation (g * h) = extendPermutation g * extendPermutation h := by
  ext i
  cases i using Fin.lastCases <;> simp [Equiv.Perm.mul_apply]

theorem extendPermutation_injective (n : ℕ) : Function.Injective (@extendPermutation n) := by
  intro g h heq
  apply Equiv.ext
  intro i
  have := congrArg (fun g : SymmetricGroup (n+1) => g i.castSucc) heq
  simpa using this

private def restrictLast (g : SymmetricGroup (n+1))
    (hg : g (Fin.last n) = Fin.last n) : SymmetricGroup n where
  toFun i := ⟨(g i.castSucc).val, by
    have hne : g i.castSucc ≠ Fin.last n := by
      rw [← hg, Ne, g.injective.eq_iff]
      exact Fin.castSucc_ne_last i
    exact Fin.val_lt_last hne⟩
  invFun i := ⟨(g.symm i.castSucc).val, by
    have hne : g.symm i.castSucc ≠ Fin.last n := by
      intro h
      have hh := congrArg g h
      simp only [Equiv.apply_symm_apply, hg] at hh
      exact Fin.castSucc_ne_last i hh
    exact Fin.val_lt_last hne⟩
  left_inv i := by
    apply Fin.ext
    change (g.symm (⟨(g i.castSucc).val, _⟩ : Fin (n+1))).val = i.val
    have hh : (⟨(g i.castSucc).val, _⟩ : Fin (n+1)) = g i.castSucc := rfl
    rw [hh, Equiv.symm_apply_apply]
    rfl
  right_inv i := by
    apply Fin.ext
    change (g (⟨(g.symm i.castSucc).val, _⟩ : Fin (n+1))).val = i.val
    have hh : (⟨(g.symm i.castSucc).val, _⟩ : Fin (n+1)) = g.symm i.castSucc := rfl
    rw [hh, Equiv.apply_symm_apply]
    rfl

theorem lastLabelSubgroup_eq_range (g : SymmetricGroup (n+1)) :
    g ∈ lastLabelSubgroup n ↔ ∃ h : SymmetricGroup n, extendPermutation h = g := by
  constructor
  · intro hg
    refine ⟨restrictLast g hg, ?_⟩
    apply Equiv.ext
    intro i
    cases i using Fin.lastCases with
    | last => exact (extendPermutation_last _).trans hg.symm
    | cast i =>
      rw [extendPermutation_castSucc]
      rfl
  · rintro ⟨h, rfl⟩
    exact extendPermutation_last h

theorem hook_mem_iff (c : Cell p) (d : ℕ × ℕ) :
    d ∈ hook c ↔ d ∈ cells p ∧
      ((d.1 = c.val.1 ∧ c.val.2 ≤ d.2) ∨ (d.2 = c.val.2 ∧ c.val.1 ≤ d.1)) :=
  Finset.mem_filter

private theorem hook_eq_union (c : Cell p) :
    hook c = ({c.val.1} ×ˢ Finset.Ico c.val.2 (rowLength p c.val.1)) ∪
      (Finset.Ico (c.val.1+1) (columnLength p c.val.2) ×ˢ {c.val.2}) := by
  ext d
  rcases d with ⟨a,b⟩
  rw [hook_mem_iff]
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
  constructor
  · rintro ⟨hd, (⟨ha,hb⟩ | ⟨hb,ha⟩)⟩
    · left
      refine ⟨ha, hb, ?_⟩
      simpa only [ha] using (cell_iff p _ _).mp hd
    · by_cases h : a = c.val.1
      · left
        refine ⟨h, ?_, ?_⟩
        · omega
        · simpa only [h] using (cell_iff p _ _).mp hd
      · right
        refine ⟨⟨by omega, ?_⟩, hb⟩
        simpa only [hb] using (cell_iff_column p _ _).mp hd
  · rintro (⟨ha,hb,hlt⟩ | ⟨⟨ha,hlt⟩,hb⟩)
    · refine ⟨?_, Or.inl ⟨ha,hb⟩⟩
      apply (cell_iff p _ _).mpr
      simpa only [ha] using hlt
    · refine ⟨?_, Or.inr ⟨hb, by omega⟩⟩
      apply (cell_iff_column p _ _).mpr
      simpa only [hb] using hlt

theorem hookLength_formula (c : Cell p) :
    hookLength c = (rowLength p c.val.1 - (c.val.2 + 1)) +
      (columnLength p c.val.2 - (c.val.1 + 1)) + 1 := by
  have hdis : Disjoint
      ({c.val.1} ×ˢ Finset.Ico c.val.2 (rowLength p c.val.1))
      (Finset.Ico (c.val.1+1) (columnLength p c.val.2) ×ˢ {c.val.2}) := by
    apply Finset.disjoint_product.mpr
    left
    simp
  change (hook c).card = _
  rw [hook_eq_union, Finset.card_union_of_disjoint hdis]
  simp only [Finset.card_product, Finset.card_singleton, Nat.card_Ico, one_mul, mul_one]
  have hr := (cell_iff p c.val.1 c.val.2).mp c.property
  omega

theorem hookLength_oneBased (c : Cell p) (i j : ℕ)
    (hi : i = c.val.1 + 1) (hj : j = c.val.2 + 1) :
    hookLength c = (rowLength p (i - 1) - j) +
      (columnLength p (j - 1) - i) + 1 := by
  subst i j
  simpa using hookLength_formula c

abbrev symmetricGroupEmbedding := Specs.AdvancedFiniteGroupRepresentations.symmetricGroupEmbedding

theorem symmetricGroupEmbedding_injective (n : ℕ) :
    Function.Injective (symmetricGroupEmbedding n) := extendPermutation_injective n

@[instance] theorem removableCell_finite (p : Partition n) : Finite (RemovableCell p) := by
  let f : RemovableCell p → Cell p := fun c => ⟨c.val, c.property.1⟩
  apply Finite.of_injective f
  intro a b hab
  exact Subtype.ext (congrArg (fun c : Cell p => c.val) hab)

theorem hookLength_positive (c : Cell p) : 0 < hookLength c := by
  rw [hookLength_formula]
  omega

end AdvancedFiniteGroupRepresentations
