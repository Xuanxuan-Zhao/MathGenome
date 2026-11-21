import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardTableaux
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CornerRecurrence
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

variable {n : ℕ} {p : Partition (n+1)}

/-- The inclusion of the cells left after deletion. -/
def cornerCellInclusion (c : RemovableCell p) (a : Cell (deleteCell p c)) : Cell p :=
  ⟨a.val, Finset.mem_of_mem_erase (by rw [← deleteCell_cells]; exact a.property)⟩

@[simp] theorem cornerCellInclusion_val (c : RemovableCell p) (a : Cell (deleteCell p c)) :
    (cornerCellInclusion c a).val = a.val := rfl

theorem cornerCellInclusion_ne (c : RemovableCell p) (a : Cell (deleteCell p c)) :
    a.val ≠ c.val := by
  have h : a.val ∈ cells (deleteCell p c) := a.property
  rw [deleteCell_cells] at h
  exact (Finset.mem_erase.mp h).1

/-- A cell other than the corner belongs to the deleted diagram. -/
def cornerCellRestriction (c : RemovableCell p) (a : Cell p) (h : a.val ≠ c.val) :
    Cell (deleteCell p c) :=
  ⟨a.val, by
    change a.val ∈ cells (deleteCell p c)
    rw [deleteCell_cells]
    exact Finset.mem_erase.mpr ⟨h, a.property⟩⟩

/-- Put the new greatest label in a chosen corner. -/
def fillCornerLabel (c : RemovableCell p) (s : Tableau (deleteCell p c))
    (a : Cell p) : Fin (n+1) :=
  if h : a.val = c.val then Fin.last n
  else (s (cornerCellRestriction c a h)).castSucc

@[simp] theorem fillCornerLabel_corner (c : RemovableCell p) (s : Tableau (deleteCell p c)) :
    fillCornerLabel c s ⟨c.val, c.property.1⟩ = Fin.last n := by
  simp [fillCornerLabel]

@[simp] theorem fillCornerLabel_inclusion (c : RemovableCell p)
    (s : Tableau (deleteCell p c)) (a : Cell (deleteCell p c)) :
    fillCornerLabel c s (cornerCellInclusion c a) = (s a).castSucc := by
  simp [fillCornerLabel, cornerCellInclusion_ne, cornerCellRestriction, cornerCellInclusion]

theorem fillCornerLabel_bijective (c : RemovableCell p) (s : Tableau (deleteCell p c)) :
    Function.Bijective (fillCornerLabel c s) := by
  classical
  constructor
  · intro a b hab
    by_cases ha : a.val = c.val <;> by_cases hb : b.val = c.val
    · exact Subtype.ext (ha.trans hb.symm)
    · simp only [fillCornerLabel, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim (Fin.castSucc_ne_last _ hab.symm)
    · simp only [fillCornerLabel, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim (Fin.castSucc_ne_last _ hab)
    · simp only [fillCornerLabel, dite_eq_right ha, dite_eq_right hb] at hab
      exact Subtype.ext (congrArg (fun x : Cell (deleteCell p c) => x.val) (s.injective (Fin.castSucc_injective _ hab)))
  · intro i
    cases i using Fin.lastCases with
    | last => exact ⟨⟨c.val, c.property.1⟩, fillCornerLabel_corner c s⟩
    | cast i =>
      refine ⟨cornerCellInclusion c (s.symm i), ?_⟩
      simp

def fillCornerTableau (c : RemovableCell p) (s : Tableau (deleteCell p c)) : Tableau p :=
  Equiv.ofBijective (fillCornerLabel c s) (fillCornerLabel_bijective c s)

/-- A corner is maximal in the coordinatewise order on cells. -/
theorem corner_maximal (c : RemovableCell p) (a : Cell p) (h : c.val ≤ a.val) :
    a.val = c.val := by
  by_contra hn
  have ha : a.val ∈ (cells p).erase c.val := Finset.mem_erase.mpr ⟨hn, a.property⟩
  exact (Finset.notMem_erase _ _) (c.property.2 h ha)

theorem fillCornerLabel_increasing (c : RemovableCell p)
    (s : StandardTableau (deleteCell p c)) (a b : Cell p)
    (h : (a.val.1 = b.val.1 ∧ a.val.2 < b.val.2) ∨
         (a.val.2 = b.val.2 ∧ a.val.1 < b.val.1)) :
    fillCornerLabel c s.val a < fillCornerLabel c s.val b := by
  classical
  have hab : a.val ≤ b.val := by
    rcases h with ⟨hr,hc⟩ | ⟨hc,hr⟩ <;> exact ⟨by omega, by omega⟩
  have hne : a.val ≠ b.val := by
    intro he
    rcases h with ⟨_,hc⟩ | ⟨_,hr⟩
    · have := congrArg Prod.snd he; omega
    · have := congrArg Prod.fst he; omega
  have ha : a.val ≠ c.val := by
    intro he
    have hh := corner_maximal c b (he ▸ hab)
    exact hne (he.trans hh.symm)
  rw [fillCornerLabel, dite_eq_right ha]
  by_cases hb : b.val = c.val
  · rw [fillCornerLabel, dite_eq_left hb]
    exact Fin.castSucc_lt_last _
  · rw [fillCornerLabel, dite_eq_right hb]
    change s.val (cornerCellRestriction c a ha) < s.val (cornerCellRestriction c b hb)
    rcases h with ⟨hr,hc⟩ | ⟨hc,hr⟩
    · exact s.property.1 _ _ hr hc
    · exact s.property.2 _ _ hc hr

def fillCorner (c : RemovableCell p) (s : StandardTableau (deleteCell p c)) :
    StandardTableau p :=
  ⟨fillCornerTableau c s.val, by
    constructor
    · intro a b hr hc
      exact fillCornerLabel_increasing c s a b (Or.inl ⟨hr,hc⟩)
    · intro a b hc hr
      exact fillCornerLabel_increasing c s a b (Or.inr ⟨hc,hr⟩)⟩

/-- A standard labeling is monotone for the coordinatewise order. -/
theorem standardTableau_monotone (t : StandardTableau p) (a b : Cell p)
    (h : a.val ≤ b.val) : t.val a ≤ t.val b := by
  let d : Cell p := ⟨(a.val.1,b.val.2),
    (diagram p).isLowerSet (show (a.val.1,b.val.2) ≤ b.val from ⟨h.1,le_rfl⟩) b.property⟩
  apply le_trans (b := t.val d)
  · rcases lt_or_eq_of_le h.2 with hc | hc
    · exact le_of_lt (t.property.1 a d rfl hc)
    · have hd : a = d := Subtype.ext (Prod.ext rfl hc)
      rw [hd]
  · rcases lt_or_eq_of_le h.1 with hr | hr
    · exact le_of_lt (t.property.2 d b rfl hr)
    · have hd : d = b := Subtype.ext (Prod.ext hr rfl)
      rw [hd]

/-- The greatest label of a standard tableau lies in a removable cell. -/
def greatestLabelCorner (t : StandardTableau p) : RemovableCell p :=
  ⟨(t.val.symm (Fin.last n)).val, (t.val.symm (Fin.last n)).property, by
    intro y x hxy hy
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
    have hx : x ∈ cells p := (diagram p).isLowerSet hxy hy
    refine Finset.mem_erase.mpr ⟨?_, hx⟩
    intro he
    let b : Cell p := ⟨y,hy⟩
    have hh := standardTableau_monotone t (t.val.symm (Fin.last n)) b (he ▸ hxy)
    rw [Equiv.apply_symm_apply] at hh
    have hb : t.val b = Fin.last n := le_antisymm (Fin.le_last _) hh
    have hb' : b = t.val.symm (Fin.last n) := t.val.injective (by simpa using hb)
    exact hne (congrArg (fun a : Cell p => a.val) hb')⟩

@[simp] theorem greatestLabelCorner_label (t : StandardTableau p) :
    t.val ⟨(greatestLabelCorner t).val, (greatestLabelCorner t).property.1⟩ = Fin.last n :=
  t.val.apply_symm_apply _

/-- Restrict a labeling whose greatest label is at `c` to the remaining cells. -/
def restrictCornerLabel (c : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val,c.property.1⟩ = Fin.last n) (a : Cell (deleteCell p c)) : Fin n :=
  ⟨(t (cornerCellInclusion c a)).val, by
    apply Fin.val_lt_last
    intro hh
    have he : cornerCellInclusion c a = ⟨c.val,c.property.1⟩ :=
      t.injective (hh.trans ht.symm)
    exact cornerCellInclusion_ne c a (congrArg (fun a : Cell p => a.val) he)⟩

@[simp] theorem castSucc_restrictCornerLabel (c : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val,c.property.1⟩ = Fin.last n) (a : Cell (deleteCell p c)) :
    (restrictCornerLabel c t ht a).castSucc = t (cornerCellInclusion c a) := by
  apply Fin.ext
  rfl

theorem restrictCornerLabel_bijective (c : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val,c.property.1⟩ = Fin.last n) :
    Function.Bijective (restrictCornerLabel c t ht) := by
  constructor
  · intro a b h
    have hh := congrArg Fin.castSucc h
    simp only [castSucc_restrictCornerLabel] at hh
    exact Subtype.ext (congrArg (fun a : Cell p => a.val) (t.injective hh))
  · intro i
    let a := t.symm i.castSucc
    have ha : a.val ≠ c.val := by
      intro he
      have he' : a = ⟨c.val,c.property.1⟩ := Subtype.ext he
      have hh : t a = i.castSucc := t.apply_symm_apply _
      rw [he', ht] at hh
      exact Fin.castSucc_ne_last i hh.symm
    refine ⟨cornerCellRestriction c a ha, ?_⟩
    apply Fin.castSucc_injective
    rw [castSucc_restrictCornerLabel]
    change t a = i.castSucc
    exact t.apply_symm_apply _

def restrictCornerTableau (c : RemovableCell p) (t : Tableau p)
    (ht : t ⟨c.val,c.property.1⟩ = Fin.last n) : Tableau (deleteCell p c) :=
  Equiv.ofBijective (restrictCornerLabel c t ht) (restrictCornerLabel_bijective c t ht)

def restrictCorner (c : RemovableCell p) (t : StandardTableau p)
    (ht : t.val ⟨c.val,c.property.1⟩ = Fin.last n) : StandardTableau (deleteCell p c) :=
  ⟨restrictCornerTableau c t.val ht, by
    constructor
    · intro a b hr hc
      change (restrictCornerLabel c t.val ht a).val < (restrictCornerLabel c t.val ht b).val
      exact t.property.1 (cornerCellInclusion c a) (cornerCellInclusion c b) hr hc
    · intro a b hc hr
      change (restrictCornerLabel c t.val ht a).val < (restrictCornerLabel c t.val ht b).val
      exact t.property.2 (cornerCellInclusion c a) (cornerCellInclusion c b) hc hr⟩

@[simp] theorem greatestLabelCorner_fillCorner (c : RemovableCell p)
    (s : StandardTableau (deleteCell p c)) : greatestLabelCorner (fillCorner c s) = c := by
  apply Subtype.ext
  change ((fillCorner c s).val.symm (Fin.last n)).val = c.val
  have he : (fillCorner c s).val.symm (Fin.last n) = (⟨c.val,c.property.1⟩ : Cell p) := by
    apply (fillCorner c s).val.injective
    rw [Equiv.apply_symm_apply]
    exact (fillCornerLabel_corner c s.val).symm
  exact congrArg (fun a : Cell p => a.val) he

@[simp] theorem fillCorner_restrictCorner (c : RemovableCell p) (t : StandardTableau p)
    (ht : t.val ⟨c.val,c.property.1⟩ = Fin.last n) :
    fillCorner c (restrictCorner c t ht) = t := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro a
  change fillCornerLabel c (restrictCornerTableau c t.val ht) a = t.val a
  by_cases ha : a.val = c.val
  · rw [fillCornerLabel, dite_eq_left ha]
    have he : a = ⟨c.val,c.property.1⟩ := Subtype.ext ha
    rw [he, ht]
  · rw [fillCornerLabel, dite_eq_right ha]
    change (restrictCornerLabel c t.val ht (cornerCellRestriction c a ha)).castSucc = t.val a
    rw [castSucc_restrictCornerLabel]
    rfl

/-- Standard tableaux are the disjoint union of tableaux obtained by deleting one corner. -/
def cornerTableauEquiv (p : Partition (n+1)) :
    (Σ c : RemovableCell p, StandardTableau (deleteCell p c)) ≃ StandardTableau p := by
  apply Equiv.ofBijective (fun s => fillCorner s.1 s.2)
  constructor
  · rintro ⟨c,s⟩ ⟨d,u⟩ h
    have hcd : c = d := by
      have hh := congrArg greatestLabelCorner h
      simpa only [greatestLabelCorner_fillCorner] using hh
    subst d
    have hsu : s = u := by
      apply Subtype.ext
      apply Equiv.ext
      intro a
      have hh := congrArg (fun t : StandardTableau p => t.val (cornerCellInclusion c a)) h
      change fillCornerLabel c s.val (cornerCellInclusion c a) =
        fillCornerLabel c u.val (cornerCellInclusion c a) at hh
      simp only [fillCornerLabel_inclusion] at hh
      exact Fin.castSucc_injective _ hh
    cases hsu
    rfl
  · intro t
    exact ⟨⟨greatestLabelCorner t,
      restrictCorner (greatestLabelCorner t) t (greatestLabelCorner_label t)⟩,
      fillCorner_restrictCorner _ _ _⟩

/-- The empty diagram has exactly one standard tableau. -/
theorem cornerRecurrence_empty : standardTableauCount emptyPartition = 1 :=
  empty_standardTableauCount

/-- Count tableaux by the removable cell occupied by their greatest label. -/
theorem cornerRecurrence {n : ℕ} (p : Partition n) (hn : 0 < n) :
    letI := Fintype.ofFinite (RemovableCell p)
    standardTableauCount p = ∑ c : RemovableCell p, standardTableauCount (deleteCell p c) := by
  cases n with
  | zero => omega
  | succ n =>
    let : Fintype (RemovableCell p) := Fintype.ofFinite _
    let : ∀ c : RemovableCell p, Finite (StandardTableau (deleteCell p c)) :=
      fun c => standardTableau_finite (deleteCell p c)
    change Nat.card (StandardTableau p) =
      ∑ c : RemovableCell p, Nat.card (StandardTableau (deleteCell p c))
    rw [← Nat.card_congr (cornerTableauEquiv p), Nat.card_sigma]

end AdvancedFiniteGroupRepresentations
