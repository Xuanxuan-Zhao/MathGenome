import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardBasisRationalModel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.RestrictionFiltration
import Mathlib.LinearAlgebra.Isomorphisms

open scoped BigOperators Classical

noncomputable section
namespace AdvancedFiniteGroupRepresentations

abbrev tabloidRow := @Specs.AdvancedFiniteGroupRepresentations.tabloidRow
abbrev removableCorners := @Specs.AdvancedFiniteGroupRepresentations.removableCorners
abbrev cornerCount := @Specs.AdvancedFiniteGroupRepresentations.cornerCount
abbrev cornerIndex := @Specs.AdvancedFiniteGroupRepresentations.cornerIndex
abbrev restrictionFiltration := @Specs.AdvancedFiniteGroupRepresentations.restrictionFiltration
abbrev RestrictionStepQuotient := @Specs.AdvancedFiniteGroupRepresentations.RestrictionStepQuotient

@[simp] theorem tabloidRow_tabloid {n : ℕ} {p : Partition n} (t : Tableau p) :
    tabloidRow (tabloid t) = labelRow t := rfl

/-- The row of every label determines the tabloid. -/
theorem tabloidRow_injective {n : ℕ} (p : Partition n) :
    Function.Injective (tabloidRow (p := p)) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro t u h
  exact Quotient.sound h

@[simp] theorem tabloidRow_smul {n : ℕ} {p : Partition n}
    (g : SymmetricGroup n) (q : Tabloid p) (a : Fin n) :
    tabloidRow (g • q) a = tabloidRow q (g.symm a) := by
  refine Quotient.inductionOn q ?_
  intro t
  change tabloidRow (g • tabloid t) a = labelRow t (g.symm a)
  rw [tabloid_smul]
  exact labelRow_smul g t a

/-- The largest entry in a standard tableau is at a removable corner. -/
theorem standard_last_removable {n : ℕ} {p : Partition (n + 1)}
    (t : StandardTableau p) : IsRemovable p (t.val.symm (Fin.last n)).val := by
  let c := t.val.symm (Fin.last n)
  have ht : t.val c = Fin.last n := t.val.apply_symm_apply _
  have hr : rowLength p c.val.1 = c.val.2 + 1 := by
    have hc : c.val.2 < rowLength p c.val.1 := (cell_iff p _ _).mp c.property
    by_contra h
    have hd : (c.val.1, c.val.2 + 1) ∈ cells p := by
      apply (cell_iff p _ _).mpr
      omega
    have hh := t.property.1 c ⟨_, hd⟩ rfl (Nat.lt_succ_self _)
    rw [ht] at hh
    exact (not_lt_of_ge (Fin.le_last _)) hh
  have hb : rowLength p (c.val.1 + 1) < rowLength p c.val.1 := by
    by_contra h
    have hd : (c.val.1 + 1, c.val.2) ∈ cells p :=
      (cell_iff p _ _).mpr (by omega)
    have hh := t.property.2 c ⟨_, hd⟩ rfl (Nat.lt_succ_self _)
    rw [ht] at hh
    exact (not_lt_of_ge (Fin.le_last _)) hh
  exact (removable_iff_row_end p _).mpr ⟨hr.symm, hb⟩

theorem cornerIndex_lt_count {n : ℕ} (p : Partition n) (c : RemovableCell p) :
    cornerIndex p c < cornerCount p := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro h
  have hc : c.val ∈ removableCorners p :=
    Finset.mem_filter.mpr ⟨c.property.1, c.property⟩
  have hh : c.val ∈ (removableCorners p).filter (fun d => d.1 < c.val.1) := by
    rw [h]
    exact hc
  have hh' := (Finset.mem_filter.mp hh).2
  exact (Nat.lt_irrefl _) hh'

/-- There is at most one removable box in any given row. -/
theorem removableCell_row_injective {n : ℕ} (p : Partition n) :
    Function.Injective (fun c : RemovableCell p => c.val.1) := by
  intro c d h
  change c.val.1 = d.val.1 at h
  have hc := ((removable_iff_row_end p c.val).mp c.property).1
  have hd := ((removable_iff_row_end p d.val).mp d.property).1
  apply Subtype.ext
  apply Prod.ext h
  rw [h] at hc
  omega

theorem cornerIndex_strictMono_row {n : ℕ} (p : Partition n)
    {c d : RemovableCell p} (hcd : c.val.1 < d.val.1) :
    cornerIndex p c < cornerIndex p d := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx, hxc.trans hcd⟩
  · intro h
    have hc : c.val ∈ (removableCorners p).filter (fun x => x.1 < d.val.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨c.property.1, c.property⟩, hcd⟩
    have hh : c.val ∈ (removableCorners p).filter (fun x => x.1 < c.val.1) := by
      rw [h]
      exact hc
    exact (Nat.lt_irrefl _) (Finset.mem_filter.mp hh).2

theorem cornerIndex_lt_iff {n : ℕ} (p : Partition n) (c d : RemovableCell p) :
    cornerIndex p c < cornerIndex p d ↔ c.val.1 < d.val.1 := by
  constructor
  · intro h
    rcases lt_trichotomy c.val.1 d.val.1 with hcd | hcd | hcd
    · exact hcd
    · have := removableCell_row_injective p hcd
      subst d
      exact (Nat.lt_irrefl _ h).elim
    · have := cornerIndex_strictMono_row p hcd
      omega
  · exact cornerIndex_strictMono_row p

theorem cornerIndex_injective {n : ℕ} (p : Partition n) :
    Function.Injective (cornerIndex p) := by
  intro c d h
  apply removableCell_row_injective p
  rcases lt_trichotomy c.val.1 d.val.1 with hcd | hcd | hcd
  · have := cornerIndex_strictMono_row p hcd
    omega
  · exact hcd
  · have := cornerIndex_strictMono_row p hcd
    omega

/-- The source's ordered list of corners, expressed without an arbitrary sort. -/
theorem cornerIndex_order {n : ℕ} (p : Partition n) :
    (∀ c d : RemovableCell p, cornerIndex p c < cornerIndex p d ↔ c.val.1 < d.val.1) ∧
    (∀ i : Fin (cornerCount p), ∃! c : RemovableCell p, cornerIndex p c = i.val) := by
  classical
  refine ⟨cornerIndex_lt_iff p, ?_⟩
  let : Fintype (RemovableCell p) := Fintype.ofFinite _
  let e : RemovableCell p ≃ ↥(removableCorners p) :=
    { toFun := fun c => ⟨c.val, Finset.mem_filter.mpr ⟨c.property.1, c.property⟩⟩
      invFun := fun c => ⟨c.val, (Finset.mem_filter.mp c.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card (RemovableCell p) = Fintype.card (Fin (cornerCount p)) := by
    rw [Fintype.card_congr e, Fintype.card_coe, Fintype.card_fin]
    rfl
  let f : RemovableCell p → Fin (cornerCount p) :=
    fun c => ⟨cornerIndex p c, cornerIndex_lt_count p c⟩
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨fun _ _ h => cornerIndex_injective p (congrArg Fin.val h), hcard⟩
  intro i
  obtain ⟨c, hc⟩ := hf.surjective i
  refine ⟨c, congrArg Fin.val hc, ?_⟩
  intro d hd
  exact cornerIndex_injective p (hd.trans (congrArg Fin.val hc).symm)

theorem restrictionFiltration_zero {n : ℕ} (p : Partition (n + 1)) :
    restrictionFiltration p 0 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨t, c, hc, _, _⟩
    exact (Nat.not_lt_zero _ hc).elim
  · exact bot_le

theorem restrictionFiltration_mono {n : ℕ} (p : Partition (n + 1)) :
    Monotone (restrictionFiltration p) := by
  intro i j hij
  apply Submodule.span_mono
  rintro v ⟨t, c, hc, ht, hv⟩
  exact ⟨t, c, hc.trans_le hij, ht, hv⟩

theorem restrictionFiltration_le_specht {n : ℕ} (p : Partition (n + 1)) (i : ℕ) :
    restrictionFiltration p i ≤ spechtSpan p := by
  apply Submodule.span_le.mpr
  rintro v ⟨t, c, hc, ht, rfl⟩
  exact polytabloid_mem_specht t.val

theorem restrictionFiltration_top {n : ℕ} (p : Partition (n + 1)) :
    restrictionFiltration p (cornerCount p) = spechtSpan p := by
  apply le_antisymm (restrictionFiltration_le_specht p _)
  rw [← standardPolytabloids_span p]
  apply Submodule.span_le.mpr
  rintro v ⟨t, rfl⟩
  let c : RemovableCell p := ⟨_, standard_last_removable t⟩
  exact Submodule.subset_span ⟨t, c, cornerIndex_lt_count p c, rfl, rfl⟩

/-- Inclusion of the erased diagram, retaining the original row and column. -/
def survivingCell {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p)
    (a : Cell (deleteCell p c)) : Cell p :=
  ⟨a.val, by
    have ha : a.val ∈ cells (deleteCell p c) := a.property
    rw [deleteCell_cells] at ha
    exact Finset.mem_of_mem_erase ha⟩

theorem survivingCell_ne {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p)
    (a : Cell (deleteCell p c)) : (survivingCell c a).val ≠ c.val := by
  have ha : a.val ∈ cells (deleteCell p c) := a.property
  rw [deleteCell_cells] at ha
  exact (Finset.mem_erase.mp ha).1

/-- Delete the greatest label from a tableau which places it at `c`. -/
def deleteTableau {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p)
    (t : Tableau p) (ht : t ⟨c.val, c.property.1⟩ = Fin.last n) :
    Tableau (deleteCell p c) where
  toFun a := ⟨(t (survivingCell c a)).val, Fin.val_lt_last (by
    intro h
    have := t.injective (h.trans ht.symm)
    exact survivingCell_ne c a (congrArg Subtype.val this))⟩
  invFun a := ⟨(t.symm a.castSucc).val, by
    change (t.symm a.castSucc).val ∈ cells (deleteCell p c)
    rw [deleteCell_cells]
    refine Finset.mem_erase.mpr ⟨?_, (t.symm a.castSucc).property⟩
    intro h
    have h' : t.symm a.castSucc = ⟨c.val, c.property.1⟩ := Subtype.ext h
    have := congrArg t h'
    rw [t.apply_symm_apply, ht] at this
    exact Fin.castSucc_ne_last a this⟩
  left_inv a := by
    apply Subtype.ext
    change (t.symm (⟨(t (survivingCell c a)).val, _⟩ : Fin (n+1))).val = a.val
    change (t.symm (t (survivingCell c a))).val = a.val
    rw [t.symm_apply_apply]
    rfl
  right_inv a := by
    apply Fin.ext
    change (t (survivingCell c ⟨(t.symm a.castSucc).val, _⟩)).val = a.val
    change (t (t.symm a.castSucc)).val = a.val
    rw [t.apply_symm_apply]
    rfl

@[simp] theorem deleteTableau_castSucc {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) (a : Cell (deleteCell p c)) :
    (deleteTableau c t ht a).castSucc = t (survivingCell c a) := rfl

@[simp] theorem deleteTableau_labelRow {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) (a : Fin n) :
    labelRow (deleteTableau c t ht) a = labelRow t a.castSucc := rfl

@[simp] theorem deleteTableau_labelColumn {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) (a : Fin n) :
    labelColumn (deleteTableau c t ht) a = labelColumn t a.castSucc := rfl

theorem deleteTableau_standard {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : StandardTableau p) (ht) :
    IsStandard (deleteTableau c t.val ht) := by
  constructor
  · intro a b hab hlt
    exact t.property.1 (survivingCell c a) (survivingCell c b) hab hlt
  · intro a b hab hlt
    exact t.property.2 (survivingCell c a) (survivingCell c b) hab hlt

/-- Reorder only the selected row so the greatest label occupies its corner. -/
def moveLastToCorner {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) : Tableau p :=
  (Equiv.swap ⟨c.val, c.property.1⟩ (t.symm (Fin.last n))).trans t

@[simp] theorem moveLastToCorner_corner {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) :
    moveLastToCorner c t ⟨c.val, c.property.1⟩ = Fin.last n := by
  simp [moveLastToCorner]

theorem moveLastToCorner_rows {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (h : labelRow t (Fin.last n) = c.val.1) :
    labelRow (moveLastToCorner c t) = labelRow t := by
  classical
  funext a
  change ((Equiv.swap ⟨c.val, c.property.1⟩ (t.symm (Fin.last n))) (t.symm a)).val.1 =
    (t.symm a).val.1
  rw [Equiv.swap_apply_def]
  split_ifs with ha hb
  · rw [ha]
    exact h
  · rw [hb]
    exact h.symm
  · rfl

/-- A surviving row-set tabloid exists whenever the last label is in the row. -/
theorem exists_deletedTabloid {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p) (h : tabloidRow q (Fin.last n) = c.val.1) :
    ∃ q' : Tabloid (deleteCell p c),
      ∀ a : Fin n, tabloidRow q' a = tabloidRow q a.castSucc := by
  revert h
  refine Quotient.inductionOn q ?_
  intro t h
  refine ⟨tabloid (deleteTableau c (moveLastToCorner c t) (moveLastToCorner_corner c t)), ?_⟩
  intro a
  change labelRow (deleteTableau c (moveLastToCorner c t) _) a = labelRow t a.castSucc
  rw [deleteTableau_labelRow, moveLastToCorner_rows c t h]

/-- The deleted tabloid is specified uniquely by the surviving label rows. -/
def deletedTabloid {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p) (h : tabloidRow q (Fin.last n) = c.val.1) :
    Tabloid (deleteCell p c) := (exists_deletedTabloid c q h).choose

@[simp] theorem deletedTabloid_rows {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p) (h) (a : Fin n) :
    tabloidRow (deletedTabloid c q h) a = tabloidRow q a.castSucc :=
  (exists_deletedTabloid c q h).choose_spec a

theorem deletedTabloid_unique {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p) (h)
    (q' : Tabloid (deleteCell p c))
    (hq' : ∀ a : Fin n, tabloidRow q' a = tabloidRow q a.castSucc) :
    q' = deletedTabloid c q h := by
  apply tabloidRow_injective
  funext a
  rw [hq', deletedTabloid_rows]

/-- Deletion on the whole permutation module, zero off the selected row. -/
def tabloidDeletion {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p) :
    PermutationModule p →ₗ[ℂ] PermutationModule (deleteCell p c) :=
  (Finsupp.lsum ℂ (fun q => if h : tabloidRow q (Fin.last n) = c.val.1
    then MonoidAlgebra.lsingle (deletedTabloid c q h) else 0)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem tabloidDeletion_single {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p) (z : ℂ) :
    tabloidDeletion c (MonoidAlgebra.single q z) =
      if h : tabloidRow q (Fin.last n) = c.val.1
      then MonoidAlgebra.single (deletedTabloid c q h) z else 0 := by
  classical
  simp only [tabloidDeletion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single, Finsupp.lsum_single]
  split_ifs <;> simp

theorem tabloidDeletion_off_row {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p)
    (h : tabloidRow q (Fin.last n) ≠ c.val.1) (z : ℂ) :
    tabloidDeletion c (MonoidAlgebra.single q z) = 0 := by
  rw [tabloidDeletion_single, dite_eq_right h]

theorem tabloidDeletion_on_row {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (q : Tabloid p)
    (h : tabloidRow q (Fin.last n) = c.val.1) :
    ∃! q' : Tabloid (deleteCell p c),
      (∀ a : Fin n, tabloidRow q' a = tabloidRow q a.castSucc) ∧
      tabloidDeletion c (MonoidAlgebra.single q 1) = MonoidAlgebra.single q' 1 := by
  refine ⟨deletedTabloid c q h, ⟨deletedTabloid_rows c q h, ?_⟩, ?_⟩
  · rw [tabloidDeletion_single, dite_eq_left h]
  · intro q' hq'
    exact deletedTabloid_unique c q h q' hq'.1

@[simp] theorem extendPermutation_symm_last {n : ℕ} (g : SymmetricGroup n) :
    (extendPermutation g).symm (Fin.last n) = Fin.last n := by
  apply (extendPermutation g).injective
  simp

@[simp] theorem extendPermutation_symm_castSucc {n : ℕ}
    (g : SymmetricGroup n) (a : Fin n) :
    (extendPermutation g).symm a.castSucc = (g.symm a).castSucc := by
  apply (extendPermutation g).injective
  simp

@[simp] theorem tabloidRow_extend_last {n : ℕ} {p : Partition (n + 1)}
    (g : SymmetricGroup n) (q : Tabloid p) :
    tabloidRow (extendPermutation g • q) (Fin.last n) = tabloidRow q (Fin.last n) := by
  rw [tabloidRow_smul, extendPermutation_symm_last]

theorem deletedTabloid_smul {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (g : SymmetricGroup n) (q : Tabloid p)
    (h : tabloidRow q (Fin.last n) = c.val.1) :
    deletedTabloid c (extendPermutation g • q) (by simpa using h) =
      g • deletedTabloid c q h := by
  symm
  apply deletedTabloid_unique
  intro a
  rw [tabloidRow_smul, deletedTabloid_rows, tabloidRow_smul,
    extendPermutation_symm_castSucc]

/-- This is equivariance for the original fixed-last-label subgroup action. -/
theorem tabloidDeletion_equivariant {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (g : SymmetricGroup n) (v : PermutationModule p) :
    tabloidDeletion c (permutationRepresentation p (extendPermutation g) v) =
      permutationRepresentation (deleteCell p c) g (tabloidDeletion c v) := by
  classical
  have hmap : (tabloidDeletion c).comp (permutationRepresentation p (extendPermutation g)) =
      (permutationRepresentation (deleteCell p c) g).comp (tabloidDeletion c) := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
      permutationRepresentation_basis, tabloidDeletion_single]
    by_cases h : tabloidRow q (Fin.last n) = c.val.1
    · rw [dite_eq_left h, dite_eq_left (show tabloidRow (extendPermutation g • q) (Fin.last n) = c.val.1
          by simpa using h), deletedTabloid_smul, permutationRepresentation_basis]
    · rw [dite_eq_right h, dite_eq_right (show tabloidRow (extendPermutation g • q) (Fin.last n) ≠ c.val.1
          by simpa using h), map_zero]
  exact LinearMap.congr_fun hmap v

/-- A corner is the bottom cell of its column. -/
theorem removableCell_column_max {n : ℕ} {p : Partition n}
    (c : RemovableCell p) (a : Cell p) (ha : a.val.2 = c.val.2) :
    a.val.1 ≤ c.val.1 := by
  have hc := (removable_iff_row_end p c.val).mp c.property
  have hmem : a.val.2 < rowLength p a.val.1 := (cell_iff p _ _).mp a.property
  by_contra h
  have := rowLength_antitone p (show c.val.1 + 1 ≤ a.val.1 by omega)
  omega

/-- Column permutations cannot move the entry of a corner to a lower row. -/
theorem column_last_row_le {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val, c.property.1⟩ = Fin.last n) (g : columnSubgroup t) :
    labelRow (g.val • t) (Fin.last n) ≤ c.val.1 := by
  have hlast : t.symm (Fin.last n) = ⟨c.val, c.property.1⟩ :=
    (t.symm_apply_eq).mpr ht.symm
  have hcol := g⁻¹.property (Fin.last n)
  change labelColumn t (g.val.symm (Fin.last n)) = labelColumn t (Fin.last n) at hcol
  change (t.symm (g.val.symm (Fin.last n))).val.2 =
    (t.symm (Fin.last n)).val.2 at hcol
  rw [hlast] at hcol
  rw [labelRow_smul]
  exact removableCell_column_max c _ hcol

/-- The upper-triangular zero formula in the branching argument. -/
theorem tabloidDeletion_polytabloid_of_row_lt {n : ℕ} {p : Partition (n + 1)}
    (c d : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val, c.property.1⟩ = Fin.last n) (hcd : c.val.1 < d.val.1) :
    tabloidDeletion d (polytabloid t) = 0 := by
  classical
  rw [polytabloid_sum, map_sum]
  apply Finset.sum_eq_zero
  intro g _
  apply tabloidDeletion_off_row
  change labelRow (g.val • t) (Fin.last n) ≠ d.val.1
  have := column_last_row_le c t ht g
  omega

/-- Insert the greatest label at the erased corner. -/
def insertTableau {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau (deleteCell p c)) : Tableau p where
  toFun a := if h : a.val = c.val then Fin.last n else
    (t ⟨a.val, by
      change a.val ∈ cells (deleteCell p c)
      rw [deleteCell_cells]
      exact Finset.mem_erase.mpr ⟨h, a.property⟩⟩).castSucc
  invFun := Fin.lastCases ⟨c.val, c.property.1⟩ (fun a => survivingCell c (t.symm a))
  left_inv a := by
    dsimp only
    split_ifs with h
    · simp only [Fin.lastCases_last]
      exact Subtype.ext h.symm
    · simp only [Fin.lastCases_castSucc, t.symm_apply_apply]
      rfl
  right_inv a := by
    cases a using Fin.lastCases with
    | last => simp
    | cast a =>
      simp only [Fin.lastCases_castSucc, dite_eq_right (survivingCell_ne c (t.symm a))]
      change (t (t.symm a)).castSucc = a.castSucc
      rw [t.apply_symm_apply]

@[simp] theorem insertTableau_corner {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau (deleteCell p c)) :
    insertTableau c t ⟨c.val, c.property.1⟩ = Fin.last n := by
  classical
  simp [insertTableau]

@[simp] theorem insertTableau_survivingCell {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau (deleteCell p c)) (a : Cell (deleteCell p c)) :
    insertTableau c t (survivingCell c a) = (t a).castSucc := by
  classical
  change (if h : (survivingCell c a).val = c.val then _ else _) = _
  rw [dite_eq_right (survivingCell_ne c a)]
  rfl

@[simp] theorem deleteTableau_insertTableau {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau (deleteCell p c)) :
    deleteTableau c (insertTableau c t) (insertTableau_corner c t) = t := by
  apply Equiv.ext
  intro a
  apply Fin.castSucc_injective
  rw [deleteTableau_castSucc, insertTableau_survivingCell]

@[simp] theorem insertTableau_deleteTableau {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) :
    insertTableau c (deleteTableau c t ht) = t := by
  classical
  apply Equiv.ext
  intro a
  by_cases ha : a.val = c.val
  · have ha' : a = ⟨c.val, c.property.1⟩ := Subtype.ext ha
    rw [ha', insertTableau_corner, ht]
  · let b : Cell (deleteCell p c) := ⟨a.val, by
      change a.val ∈ cells (deleteCell p c)
      rw [deleteCell_cells]
      exact Finset.mem_erase.mpr ⟨ha, a.property⟩⟩
    change insertTableau c (deleteTableau c t ht) (survivingCell c b) = _
    rw [insertTableau_survivingCell, deleteTableau_castSucc]
    rfl

theorem insertTableau_standard {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : StandardTableau (deleteCell p c)) :
    IsStandard (insertTableau c t.val) := by
  classical
  obtain ⟨rowend, _⟩ := (removable_iff_row_end p c.val).mp c.property
  have surv : ∀ a : Cell p, a.val ≠ c.val → ∃ b : Cell (deleteCell p c), survivingCell c b = a := by
    intro a ha
    refine ⟨⟨a.val, ?_⟩, rfl⟩
    change a.val ∈ cells (deleteCell p c)
    rw [deleteCell_cells]
    exact Finset.mem_erase.mpr ⟨ha, a.property⟩
  constructor
  · intro a b hab hlt
    have ha : a.val ≠ c.val := by
      intro h
      have hb : b.val.2 < rowLength p b.val.1 := (cell_iff p _ _).mp b.property
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      rw [← h1, hab] at rowend
      omega
    obtain ⟨a', rfl⟩ := surv a ha
    by_cases hb : b.val = c.val
    · rw [show b = ⟨c.val, c.property.1⟩ from Subtype.ext hb,
        insertTableau_corner, insertTableau_survivingCell]
      exact Fin.castSucc_lt_last _
    · obtain ⟨b', rfl⟩ := surv b hb
      rw [insertTableau_survivingCell, insertTableau_survivingCell]
      exact t.property.1 a' b' hab hlt
  · intro a b hab hlt
    have ha : a.val ≠ c.val := by
      intro h
      have hh := removableCell_column_max c b (hab.symm.trans (congrArg Prod.snd h))
      have h1 := congrArg Prod.fst h
      omega
    obtain ⟨a', rfl⟩ := surv a ha
    by_cases hb : b.val = c.val
    · rw [show b = ⟨c.val, c.property.1⟩ from Subtype.ext hb,
        insertTableau_corner, insertTableau_survivingCell]
      exact Fin.castSucc_lt_last _
    · obtain ⟨b', rfl⟩ := surv b hb
      rw [insertTableau_survivingCell, insertTableau_survivingCell]
      exact t.property.2 a' b' hab hlt

@[simp] theorem deletedTabloid_tabloid {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) :
    deletedTabloid c (tabloid t) (by
      change (t.symm (Fin.last n)).val.1 = c.val.1
      rw [(t.symm_apply_eq).mpr ht.symm]) = tabloid (deleteTableau c t ht) := by
  symm
  apply deletedTabloid_unique
  exact deleteTableau_labelRow c t ht

/-- A column permutation leaves the greatest label in the corner's row
exactly when it fixes that label. -/
theorem column_last_row_eq_iff {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht : t ⟨c.val, c.property.1⟩ = Fin.last n)
    (g : columnSubgroup t) :
    labelRow (g.val • t) (Fin.last n) = c.val.1 ↔ g.val (Fin.last n) = Fin.last n := by
  have hlast : t.symm (Fin.last n) = ⟨c.val, c.property.1⟩ :=
    (t.symm_apply_eq).mpr ht.symm
  constructor
  · intro h
    have hcol := g⁻¹.property (Fin.last n)
    change (t.symm (g.val.symm (Fin.last n))).val.2 =
      (t.symm (Fin.last n)).val.2 at hcol
    rw [hlast] at hcol
    rw [labelRow_smul] at h
    have heq : t.symm (g.val.symm (Fin.last n)) = ⟨c.val, c.property.1⟩ :=
      Subtype.ext (Prod.ext h hcol)
    have hh := congrArg t heq
    rw [t.apply_symm_apply, ht] at hh
    exact ((g.val.apply_symm_apply (Fin.last n)).symm.trans (congrArg g.val hh)).symm
  · intro h
    rw [labelRow_smul]
    have hh : g.val.symm (Fin.last n) = Fin.last n := by
      apply g.val.injective
      simpa using h.symm
    change (t.symm (g.val.symm (Fin.last n))).val.1 = c.val.1
    rw [hh, hlast]

/-- Extending a smaller column permutation fixes the removed label. -/
def extendColumnPermutation {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht)
    (g : columnSubgroup (deleteTableau c t ht)) : columnSubgroup t :=
  ⟨extendPermutation g.val, by
    intro a
    cases a using Fin.lastCases with
    | last => rw [extendPermutation_last]
    | cast a =>
      rw [extendPermutation_castSucc]
      exact g.property a⟩

theorem extendColumnPermutation_injective {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) :
    Function.Injective (extendColumnPermutation c t ht) := by
  intro g h heq
  exact Subtype.ext (extendPermutation_injective n (congrArg Subtype.val heq))

theorem extendColumnPermutation_range {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) (g : columnSubgroup t) :
    g ∈ Set.range (extendColumnPermutation c t ht) ↔ g.val (Fin.last n) = Fin.last n := by
  constructor
  · rintro ⟨h, rfl⟩
    exact extendPermutation_last h.val
  · intro hg
    obtain ⟨h, hh⟩ := (lastLabelSubgroup_eq_range g.val).mp hg
    have hc : h ∈ columnSubgroup (deleteTableau c t ht) := by
      intro a
      change labelColumn t (h a).castSucc = labelColumn t a.castSucc
      rw [← extendPermutation_castSucc, hh]
      exact g.property a.castSucc
    exact ⟨⟨h, hc⟩, Subtype.ext hh⟩

@[simp] theorem permutationSign_extendPermutation {n : ℕ} (g : SymmetricGroup n) :
    permutationSign (extendPermutation g) = permutationSign g := by
  let e : Fin n ≃ {a : Fin (n+1) // a ≠ Fin.last n} :=
    { toFun := fun a => ⟨a.castSucc, Fin.castSucc_ne_last a⟩
      invFun := fun a => ⟨a.val.val, Fin.val_lt_last a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have heq : extendPermutation g = g.extendDomain e := by
    apply Equiv.ext
    intro a
    cases a using Fin.lastCases with
    | last =>
      rw [extendPermutation_last, Equiv.Perm.extendDomain_apply_not_subtype]
      simp
    | cast a =>
      rw [extendPermutation_castSucc]
      exact (Equiv.Perm.extendDomain_apply_image g e a).symm
  change ((Equiv.Perm.sign (extendPermutation g) : ℤ) : ℂ) =
    ((Equiv.Perm.sign g : ℤ) : ℂ)
  rw [heq, Equiv.Perm.sign_extendDomain]

@[simp] theorem tabloidDeletion_tableau {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) (z : ℂ) :
    tabloidDeletion c (MonoidAlgebra.single (tabloid t) z) =
      MonoidAlgebra.single (tabloid (deleteTableau c t ht)) z := by
  have h : tabloidRow (tabloid t) (Fin.last n) = c.val.1 := by
    change (t.symm (Fin.last n)).val.1 = c.val.1
    rw [(t.symm_apply_eq).mpr ht.symm]
  rw [tabloidDeletion_single, dite_eq_left h, deletedTabloid_tabloid c t ht]

/-- Restriction of the column sum gives the actual smaller polytabloid. -/
theorem tabloidDeletion_polytabloid {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (t : Tableau p) (ht) :
    tabloidDeletion c (polytabloid t) = polytabloid (deleteTableau c t ht) := by
  classical
  rw [polytabloid_sum, map_sum, polytabloid_sum]
  symm
  apply Fintype.sum_of_injective (extendColumnPermutation c t ht)
    (extendColumnPermutation_injective c t ht)
  · intro g hg
    apply tabloidDeletion_off_row
    change labelRow (g.val • t) (Fin.last n) ≠ c.val.1
    intro hrow
    exact hg ((extendColumnPermutation_range c t ht g).mpr
      ((column_last_row_eq_iff c t ht g).mp hrow))
  · intro g
    change MonoidAlgebra.single (tabloid (g.val • deleteTableau c t ht)) (permutationSign g.val) =
      tabloidDeletion c (MonoidAlgebra.single (tabloid (extendPermutation g.val • t))
        (permutationSign (extendPermutation g.val)))
    rw [permutationSign_extendPermutation]
    conv_rhs => rw [← tabloid_smul, ← permutationRepresentation_basis]
    rw [tabloidDeletion_equivariant, tabloidDeletion_tableau c t ht,
      permutationRepresentation_basis, tabloid_smul]

/-- Corner occupied by the greatest entry of a standard tableau. -/
def standardCorner {n : ℕ} {p : Partition (n + 1)} (t : StandardTableau p) :
    RemovableCell p := ⟨_, standard_last_removable t⟩

@[simp] theorem standardCorner_label {n : ℕ} {p : Partition (n + 1)}
    (t : StandardTableau p) : t.val ⟨(standardCorner t).val, (standardCorner t).property.1⟩ = Fin.last n :=
  t.val.apply_symm_apply _

theorem standardCorner_eq {n : ℕ} {p : Partition (n + 1)}
    (t : StandardTableau p) (c : RemovableCell p)
    (h : (t.val.symm (Fin.last n)).val = c.val) : standardCorner t = c := Subtype.ext h

/-- Extend the standard-basis coordinate functionals to the ambient module.
Only their values on the original Specht subspace will be used. -/
def standardCoordinate {n : ℕ} (p : Partition n) (t : StandardTableau p) :
    PermutationModule p →ₗ[ℂ] ℂ :=
  (standardBasis p).coord t ∘ₗ (spechtSpan p).subtype.leftInverse

@[simp] theorem standardCoordinate_val {n : ℕ} (p : Partition n)
    (t : StandardTableau p) (v : SpechtModule p) :
    standardCoordinate p t v.val = (standardBasis p).repr v t := by
  change (standardBasis p).coord t ((spechtSpan p).subtype.leftInverse ((spechtSpan p).subtype v)) = _
  rw [LinearMap.leftInverse_apply_of_inj (spechtSpan p).ker_subtype]
  rfl

@[simp] theorem standardCoordinate_polytabloid {n : ℕ} (p : Partition n)
    (t u : StandardTableau p) :
    standardCoordinate p t (polytabloid u.val) = if u = t then 1 else 0 := by
  classical
  rw [← standardBasis_val p u, standardCoordinate_val, Module.Basis.repr_self_apply]

theorem standardPolytabloid_mem_filtration {n : ℕ} {p : Partition (n + 1)}
    (t : StandardTableau p) (i : ℕ) (h : cornerIndex p (standardCorner t) < i) :
    polytabloid t.val ∈ restrictionFiltration p i :=
  Submodule.subset_span ⟨t, standardCorner t, h, rfl, rfl⟩

/-- Membership in the source's filtration is precisely a restriction on
standard-basis coordinates. -/
theorem mem_restrictionFiltration_iff {n : ℕ} {p : Partition (n + 1)}
    (v : PermutationModule p) (i : ℕ) :
    v ∈ restrictionFiltration p i ↔ v ∈ spechtSpan p ∧
      ∀ t : StandardTableau p, i ≤ cornerIndex p (standardCorner t) → standardCoordinate p t v = 0 := by
  classical
  constructor
  · intro hv
    refine ⟨restrictionFiltration_le_specht p i hv, ?_⟩
    intro t ht
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, c, hc, hu, rfl⟩ := hx
      change cornerIndex p c < i at hc
      have hcorner := standardCorner_eq u c hu
      have hut : u ≠ t := by
        intro h
        subst u
        rw [hcorner] at ht
        omega
      simp [hut]
    | zero => exact map_zero _
    | add x y hx hy hcx hcy => rw [map_add, hcx, hcy, add_zero]
    | smul z x hx hcx => rw [map_smul, hcx, smul_zero]
  · rintro ⟨hv, hcoords⟩
    let : Finite (StandardTableau p) := standardTableau_finite p
    let : Fintype (StandardTableau p) := Fintype.ofFinite _
    let w : SpechtModule p := ⟨v, hv⟩
    have heq : ∑ t : StandardTableau p, (standardBasis p).repr w t • polytabloid t.val = v := by
      have := congrArg (fun x : SpechtModule p => x.val) ((standardBasis p).sum_repr w)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, standardBasis_val] using this
    rw [← heq]
    apply Submodule.sum_mem
    intro t _
    by_cases ht : cornerIndex p (standardCorner t) < i
    · exact Submodule.smul_mem _ _ (standardPolytabloid_mem_filtration t i ht)
    · have hh := hcoords t (Nat.le_of_not_gt ht)
      have hz : (standardBasis p).repr w t = 0 := (standardCoordinate_val p t w).symm.trans hh
      rw [hz, zero_smul]
      exact Submodule.zero_mem _

/-- On the last nonzero layer, deletion reads the original standard coordinate. -/
theorem standardCoordinate_deletion {n : ℕ} {p : Partition (n + 1)}
    (t : StandardTableau p) (v : PermutationModule p)
    (hv : v ∈ restrictionFiltration p (cornerIndex p (standardCorner t) + 1)) :
    standardCoordinate (deleteCell p (standardCorner t))
      ⟨deleteTableau (standardCorner t) t.val (standardCorner_label t),
        deleteTableau_standard (standardCorner t) t (standardCorner_label t)⟩
      (tabloidDeletion (standardCorner t) v) = standardCoordinate p t v := by
  classical
  let c := standardCorner t
  let t' : StandardTableau (deleteCell p c) :=
    ⟨deleteTableau c t.val (standardCorner_label t),
      deleteTableau_standard c t (standardCorner_label t)⟩
  change standardCoordinate (deleteCell p c) t' (tabloidDeletion c v) = standardCoordinate p t v
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, d, hd, hu, rfl⟩ := hx
    have hu' : standardCorner u = d := standardCorner_eq u d hu
    have huLast : u.val ⟨d.val, d.property.1⟩ = Fin.last n := by
      rw [← hu']
      exact standardCorner_label u
    by_cases hdc : d = c
    · have huLastC : u.val ⟨c.val, c.property.1⟩ = Fin.last n := by
        simpa only [hdc] using huLast
      rw [tabloidDeletion_polytabloid c u.val huLastC]
      let u' : StandardTableau (deleteCell p c) :=
        ⟨deleteTableau c u.val huLastC, deleteTableau_standard c u huLastC⟩
      change standardCoordinate (deleteCell p c) t' (polytabloid u'.val) = _
      rw [standardCoordinate_polytabloid, standardCoordinate_polytabloid]
      have heq : u' = t' ↔ u = t := by
        constructor
        · intro h
          apply Subtype.ext
          have hh := congrArg (fun z : StandardTableau (deleteCell p c) => insertTableau c z.val) h
          simpa only [u', t', insertTableau_deleteTableau] using hh
        · intro h
          subst u
          rfl
      rw [heq]
    · change cornerIndex p d < cornerIndex p c + 1 at hd
      have hlt : cornerIndex p d < cornerIndex p c := by
        have hne : cornerIndex p d ≠ cornerIndex p c := fun h => hdc (cornerIndex_injective p h)
        omega
      have hrow := (cornerIndex_lt_iff p d c).mp hlt
      rw [tabloidDeletion_polytabloid_of_row_lt d c u.val huLast hrow, map_zero,
        standardCoordinate_polytabloid]
      have hut : u ≠ t := by
        intro h
        subst u
        exact hdc hu'.symm
      simp [hut]
  | zero => simp
  | add x y hx hy hcx hcy => simp only [map_add, hcx, hcy]
  | smul z x hx hcx => simp only [map_smul, hcx]

/-- Deletion kills all the earlier layers. -/
theorem tabloidDeletion_filtration_zero {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (i : ℕ) (hi : i ≤ cornerIndex p c)
    (v : PermutationModule p) (hv : v ∈ restrictionFiltration p i) :
    tabloidDeletion c v = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, d, hd, ht, rfl⟩ := hx
    have hdLast : t.val ⟨d.val, d.property.1⟩ = Fin.last n := by
      rw [← standardCorner_eq t d ht]
      exact standardCorner_label t
    exact tabloidDeletion_polytabloid_of_row_lt d c t.val hdLast
      ((cornerIndex_lt_iff p d c).mp (hd.trans_le hi))
  | zero => exact map_zero _
  | add x y hx hy hcx hcy => rw [map_add, hcx, hcy, add_zero]
  | smul z x hx hcx => rw [map_smul, hcx, smul_zero]

/-- The kernel on a single layer is exactly the preceding layer. -/
theorem tabloidDeletion_step_kernel {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (v : PermutationModule p)
    (hv : v ∈ restrictionFiltration p (cornerIndex p c + 1))
    (hz : tabloidDeletion c v = 0) : v ∈ restrictionFiltration p (cornerIndex p c) := by
  obtain ⟨hs, hcoords⟩ := (mem_restrictionFiltration_iff v _).mp hv
  apply (mem_restrictionFiltration_iff v _).mpr ⟨hs, ?_⟩
  intro t ht
  by_cases hlt : cornerIndex p c < cornerIndex p (standardCorner t)
  · exact hcoords t hlt
  · have heq : standardCorner t = c := cornerIndex_injective p (by omega)
    subst c
    have hh := standardCoordinate_deletion t v hv
    rw [hz, map_zero] at hh
    exact hh.symm

/-- Kernel description used to prove invariance without assuming it. -/
theorem restrictionFiltration_kernel_iff {n : ℕ} {p : Partition (n + 1)}
    (v : PermutationModule p) (i : ℕ) :
    v ∈ restrictionFiltration p i ↔ v ∈ spechtSpan p ∧
      ∀ c : RemovableCell p, i ≤ cornerIndex p c → tabloidDeletion c v = 0 := by
  constructor
  · intro hv
    exact ⟨restrictionFiltration_le_specht p i hv,
      fun c hc => tabloidDeletion_filtration_zero c i hc v hv⟩
  · rintro ⟨hs, hker⟩
    have hreduce : ∀ k, k ≤ cornerCount p →
        v ∈ restrictionFiltration p k → v ∈ restrictionFiltration p i := by
      intro k
      induction k with
      | zero =>
        intro _ hv
        exact restrictionFiltration_mono p (Nat.zero_le i) hv
      | succ k ih =>
        intro hk hv
        by_cases hik : i ≤ k
        · obtain ⟨c, hc, _⟩ := (cornerIndex_order p).2 ⟨k, by omega⟩
          have hc' : cornerIndex p c = k := hc
          apply ih (by omega)
          have hv' := tabloidDeletion_step_kernel c v (by simpa only [hc'] using hv)
            (hker c (by omega))
          simpa only [hc'] using hv' 
        · exact restrictionFiltration_mono p (by omega) hv
    apply hreduce (cornerCount p) le_rfl
    rw [restrictionFiltration_top]
    exact hs

theorem restrictionFiltration_invariant {n : ℕ} (p : Partition (n + 1))
    (i : ℕ) (g : SymmetricGroup n) (v : PermutationModule p)
    (hv : v ∈ restrictionFiltration p i) :
    permutationRepresentation p (extendPermutation g) v ∈ restrictionFiltration p i := by
  obtain ⟨hs, hker⟩ := (restrictionFiltration_kernel_iff v i).mp hv
  apply (restrictionFiltration_kernel_iff _ i).mpr
  refine ⟨specht_stable _ v hs, ?_⟩
  intro c hc
  rw [tabloidDeletion_equivariant, hker c hc, map_zero]

theorem tabloidDeletion_step_mem {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (v : PermutationModule p)
    (hv : v ∈ restrictionFiltration p (cornerIndex p c + 1)) :
    tabloidDeletion c v ∈ spechtSpan (deleteCell p c) := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, d, hd, ht, rfl⟩ := hx
    change cornerIndex p d < cornerIndex p c + 1 at hd
    have hdLast : t.val ⟨d.val, d.property.1⟩ = Fin.last n := by
      rw [← standardCorner_eq t d ht]
      exact standardCorner_label t
    by_cases hdc : d = c
    · have hcLast : t.val ⟨c.val, c.property.1⟩ = Fin.last n := by simpa only [hdc] using hdLast
      rw [tabloidDeletion_polytabloid c t.val hcLast]
      exact polytabloid_mem_specht _
    · have hlt : cornerIndex p d < cornerIndex p c := by
        have hne : cornerIndex p d ≠ cornerIndex p c := fun h => hdc (cornerIndex_injective p h)
        omega
      rw [tabloidDeletion_polytabloid_of_row_lt d c t.val hdLast
        ((cornerIndex_lt_iff p d c).mp hlt)]
      exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (spechtSpan (deleteCell p c)).zero_mem
  | add x y hx hy hcx hcy => simpa only [map_add] using Submodule.add_mem _ hcx hcy
  | smul z x hx hcx => simpa only [map_smul] using Submodule.smul_mem _ z hcx

/-- The actual deletion map on the current filtration term, with its proved
Specht codomain. -/
def restrictionStepDeletion {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p) :
    restrictionFiltration p (cornerIndex p c + 1) →ₗ[ℂ] SpechtModule (deleteCell p c) :=
  ((tabloidDeletion c).comp (restrictionFiltration p (cornerIndex p c + 1)).subtype).codRestrict
    (spechtSpan (deleteCell p c)) (fun v => tabloidDeletion_step_mem c v.val v.property)

@[simp] theorem restrictionStepDeletion_val {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (v : restrictionFiltration p (cornerIndex p c + 1)) :
    (restrictionStepDeletion c v).val = tabloidDeletion c v.val := rfl

/-- Inserting the greatest entry provides a preimage of each smaller standard
polytabloid, so deletion is onto the whole smaller Specht module. -/
theorem restrictionStepDeletion_surjective {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) : Function.Surjective (restrictionStepDeletion c) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  rw [← (standardBasis (deleteCell p c)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  let u : StandardTableau p := ⟨insertTableau c t.val, insertTableau_standard c t⟩
  have hu : standardCorner u = c := by
    apply Subtype.ext
    change (u.val.symm (Fin.last n)).val = c.val
    have hh : u.val ⟨c.val, c.property.1⟩ = Fin.last n := insertTableau_corner c t.val
    exact congrArg Subtype.val ((u.val.symm_apply_eq).mpr hh.symm)
  let v : restrictionFiltration p (cornerIndex p c + 1) :=
    ⟨polytabloid u.val, standardPolytabloid_mem_filtration u _ (by rw [hu]; omega)⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change tabloidDeletion c (polytabloid (insertTableau c t.val)) = _
  rw [tabloidDeletion_polytabloid c _ (insertTableau_corner c t.val),
    deleteTableau_insertTableau, standardBasis_val]

theorem restrictionStepDeletion_ker {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) :
    LinearMap.ker (restrictionStepDeletion c) =
      (restrictionFiltration p (cornerIndex p c)).comap
        (restrictionFiltration p (cornerIndex p c + 1)).subtype := by
  apply Submodule.ext
  intro v
  change restrictionStepDeletion c v = 0 ↔ v.val ∈ restrictionFiltration p (cornerIndex p c)
  constructor
  · intro h
    apply tabloidDeletion_step_kernel c v.val v.property
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact tabloidDeletion_filtration_zero c _ le_rfl v.val h

/-- The quotient identification is induced by deletion on all representatives. -/
def restrictionStepEquiv {n : ℕ} {p : Partition (n + 1)} (c : RemovableCell p) :
    RestrictionStepQuotient p c ≃ₗ[ℂ] SpechtModule (deleteCell p c) :=
  (Submodule.quotEquivOfEq _ _ (restrictionStepDeletion_ker c).symm).trans
    ((restrictionStepDeletion c).quotKerEquivOfSurjective (restrictionStepDeletion_surjective c))

@[simp] theorem restrictionStepEquiv_mk {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (v : restrictionFiltration p (cornerIndex p c + 1)) :
    (restrictionStepEquiv c (Submodule.Quotient.mk v)).val = tabloidDeletion c v.val := rfl

theorem restrictionStepEquiv_equivariant {n : ℕ} {p : Partition (n + 1)}
    (c : RemovableCell p) (g : SymmetricGroup n)
    (v w : restrictionFiltration p (cornerIndex p c + 1))
    (hw : w.val = permutationRepresentation p (extendPermutation g) v.val) :
    (restrictionStepEquiv c (Submodule.Quotient.mk w)).val =
      permutationRepresentation (deleteCell p c) g
        (restrictionStepEquiv c (Submodule.Quotient.mk v)).val := by
  rw [restrictionStepEquiv_mk, restrictionStepEquiv_mk, hw, tabloidDeletion_equivariant]

/-- FR-B04: restriction filtration and its deletion-induced equivariant
successive quotient identifications, including ambient size one. -/
theorem restriction_filtration : Specs.AdvancedFiniteGroupRepresentations.restriction_filtrationType := by
  intro n p
  refine ⟨fun c => tabloidDeletion c, ?_, ?_, ?_, restrictionFiltration_zero p,
    restrictionFiltration_mono p, restrictionFiltration_top p, restrictionFiltration_invariant p, ?_⟩
  · intro c q h
    exact tabloidDeletion_off_row c q h 1
  · exact fun c q h => tabloidDeletion_on_row c q h
  · exact fun c g v => tabloidDeletion_equivariant c g v
  · intro c
    exact ⟨restrictionStepEquiv c, restrictionStepEquiv_mk c, restrictionStepEquiv_equivariant c⟩

end AdvancedFiniteGroupRepresentations
