import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardTableaux
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardIndependence
import Mathlib.Order.PiLex
import Mathlib.Order.Preorder.Finite

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

variable {n : ℕ} {p : Partition n}

/-- A tabloid records the row of each label. -/
def tabloidRowWord (q : Tabloid p) : Lex (Fin n → ℕ) :=
  toLex (Quotient.lift labelRow (fun _ _ h => h) q)

@[simp] theorem tabloidRowWord_mk (t : Tableau p) :
    tabloidRowWord (tabloid t) = toLex (labelRow t) := rfl

theorem tabloidRowWord_injective : Function.Injective (tabloidRowWord (p := p)) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro t u h
  exact Quotient.sound h

/-- Entries in a fixed row, in their geometric left-to-right order. -/
def rowEntry (t : Tableau p) (i : ℕ) (j : Fin (rowLength p i)) : Fin n :=
  t ⟨(i, j.val), (cell_iff p i j.val).mpr j.isLt⟩

theorem rowEntry_strictMono (t : Tableau p) (ht : RowIncreasing t) (i : ℕ) :
    StrictMono (rowEntry t i) := by
  intro a b hab
  exact ht _ _ rfl hab

theorem rowEntry_range (t : Tableau p) (i : ℕ) :
    Set.range (rowEntry t i) = rowLabels t i := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    change (t.symm (t _)).val.1 = i
    simp
  · intro ha
    have hr : (t.symm a).val.1 = i := ha
    have hj : (t.symm a).val.2 < rowLength p i := by
      simpa only [hr] using (cell_iff p _ _).mp (t.symm a).property
    refine ⟨⟨(t.symm a).val.2, hj⟩, ?_⟩
    apply t.symm.injective
    simp only [rowEntry, Equiv.symm_apply_apply]
    apply Subtype.ext
    exact Prod.ext hr.symm rfl

/-- Sorting the labels within each row recovers a row-increasing tableau. -/
theorem rowIncreasing_tabloid_injective (t u : Tableau p)
    (ht : RowIncreasing t) (hu : RowIncreasing u) (h : tabloid t = tabloid u) : t = u := by
  have he (i : ℕ) : rowEntry t i = rowEntry u i := by
    have hr : Set.range (rowEntry t i) = Set.range (rowEntry u i) := by
      rw [rowEntry_range, rowEntry_range, (tabloid_eq_iff t u).mp h i]
    have hh := (OrderEmbedding.range_eq_iff
      (f := OrderEmbedding.ofStrictMono _ (rowEntry_strictMono t ht i))
      (g := OrderEmbedding.ofStrictMono _ (rowEntry_strictMono u hu i))).mp hr
    exact congrArg DFunLike.coe hh
  apply Equiv.ext
  intro c
  have hj := (cell_iff p _ _).mp c.property
  exact congrFun (he c.val.1) ⟨c.val.2, hj⟩

/-- In an increasing column, the ordering of labels reflects their row order. -/
theorem columnIncreasing_row_lt (t : Tableau p) (ht : ColumnIncreasing t)
    {a b : Fin n} (hab : a < b) (hc : labelColumn t a = labelColumn t b) :
    labelRow t a < labelRow t b := by
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
  · have hh := ht (t.symm b) (t.symm a) hc.symm hlt
    simp only [Equiv.apply_symm_apply] at hh
    exact not_lt_of_ge hab.le hh
  · have hh : t.symm a = t.symm b :=
      Subtype.ext (Prod.ext heq.symm hc)
    exact hab.ne (t.symm.injective hh)

/-- A nontrivial column permutation moves the smallest changed label down.
Hence the original row word is the unique lexicographic minimum of its column orbit. -/
theorem column_rowWord_lt (t : Tableau p) (ht : ColumnIncreasing t)
    (c : columnSubgroup t) (hc : c ≠ 1) :
    tabloidRowWord (tabloid t) < tabloidRowWord (tabloid (c.val • t)) := by
  classical
  have hex : ∃ a : Fin n, c.val.symm a ≠ a := by
    by_contra! hn
    apply hc
    apply Subtype.ext
    apply Equiv.ext
    intro a
    have hh := hn (c.val a)
    simpa using hh.symm
  obtain ⟨a, ha, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min
    {a | c.val.symm a ≠ a} hex
  have hfix : ∀ b < a, c.val.symm b = b := by
    intro b hb
    by_contra hne
    exact hmin b hne hb
  have hab : a < c.val.symm a := by
    rcases lt_trichotomy a (c.val.symm a) with h | h | h
    · exact h
    · exact False.elim (ha h.symm)
    · have hh := hfix _ h
      exact False.elim (ha (c.val.symm.injective hh))
  refine ⟨a, ?_, ?_⟩
  · intro b hb
    change labelRow t b = labelRow t (c.val.symm b)
    rw [hfix b hb]
  · change labelRow t a < labelRow t (c.val.symm a)
    apply columnIncreasing_row_lt t ht hab
    exact ((columnSubgroup t).inv_mem c.property a).symm

/-- Every nonzero tabloid coefficient lies on or above the leading row word. -/
theorem polytabloid_rowWord_le (t : Tableau p) (ht : ColumnIncreasing t)
    (q : Tabloid p) (hq : (polytabloid t).coeff q ≠ 0) :
    tabloidRowWord (tabloid t) ≤ tabloidRowWord q := by
  classical
  by_contra hn
  apply hq
  rw [polytabloid_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro c _
  have hne : tabloid (c.val • t) ≠ q := by
    intro heq
    apply hn
    rw [← heq]
    by_cases hc : c = 1
    · simp [hc]
    · exact (column_rowWord_lt t ht c hc).le
  exact Finsupp.single_eq_of_ne hne.symm

/-- FR B01. These are the original polytabloids in the tabloid permutation module. -/
theorem standard_polytabloids_linearIndependent (p : Partition n) :
    LinearIndependent ℂ (fun t : StandardTableau p => polytabloid t.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let s' := s.filter (fun t => g t ≠ 0)
  have hs' : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨t, ht, hmin⟩ := s'.exists_min_image
    (fun t => tabloidRowWord (tabloid t.val)) hs'
  have hts : t ∈ s := (Finset.mem_filter.mp ht).1
  have hgt : g t ≠ 0 := (Finset.mem_filter.mp ht).2
  have hz : ∀ j ∈ s, j ≠ t →
      g j * (polytabloid j.val).coeff (tabloid t.val) = 0 := by
    intro j hj hjt
    by_cases hgj : g j = 0
    · simp [hgj]
    · have hle := hmin j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
      have hc : (polytabloid j.val).coeff (tabloid t.val) = 0 := by
        by_contra hne
        have hge := polytabloid_rowWord_le j.val j.property.2 _ hne
        have heq := tabloidRowWord_injective (le_antisymm hge hle)
        exact hjt (Subtype.ext
          (rowIncreasing_tabloid_injective j.val t.val j.property.1 t.property.1 heq))
      rw [hc, mul_zero]
  have hh := congrArg (fun v : PermutationModule p => v.coeff (tabloid t.val)) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, smul_eq_mul, MonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hh
  rw [Finset.sum_eq_single t (fun j hj hjt => hz j hj hjt)
    (fun h => False.elim (h hts)), polytabloid_coefficient, mul_one] at hh
  exact hgt hh

end AdvancedFiniteGroupRepresentations
