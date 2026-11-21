import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Tabloids
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.RowColumnTest
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev RowColumnCollision := @Specs.AdvancedFiniteGroupRepresentations.RowColumnCollision

variable {n : ℕ} {p q : Partition n}

private theorem noCollision_injective (t : Tableau p) (u : Tableau q)
    (h : ¬ RowColumnCollision t u) {a b : Fin n}
    (hc : labelColumn t a = labelColumn t b) (hr : labelRow u a = labelRow u b) : a = b := by
  by_contra hab
  exact h ⟨a, b, hab, hc, hr⟩

/-- Labels in the first k rows of u. -/
private def initialLabels (u : Tableau q) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => labelRow u a < k)

/-- Labels in column j of t and the first k rows of u. -/
private def columnSlice (t : Tableau p) (u : Tableau q) (j k : ℕ) : Finset (Fin n) :=
  (initialLabels u k).filter (fun a => labelColumn t a = j)

private theorem mem_columnSlice (t : Tableau p) (u : Tableau q) (j k : ℕ) (a : Fin n) :
    a ∈ columnSlice t u j k ↔ labelRow u a < k ∧ labelColumn t a = j := by
  simp [columnSlice, initialLabels]

private theorem label_cell (t : Tableau p) (a : Fin n) :
    (labelRow t a, labelColumn t a) ∈ cells p := (t.symm a).property

private theorem row_column_injective (t : Tableau p) {a b : Fin n}
    (hr : labelRow t a = labelRow t b) (hc : labelColumn t a = labelColumn t b) : a = b := by
  apply t.symm.injective
  exact Subtype.ext (Prod.ext hr hc)

private theorem initialLabels_card (u : Tableau q) (k : ℕ) :
    (initialLabels u k).card = ∑ i ∈ Finset.range k, rowLength q i := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n))
    (Finset.range k) (labelRow u)
  have hr : ∀ i, (Finset.univ.filter (fun a : Fin n => labelRow u a = i)).card =
      rowLength q i := by
    intro i
    have h := rowLabels_card u i
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      rowLabels, Specs.AdvancedFiniteGroupRepresentations.rowLabels, Set.mem_ofPred_eq] using h
  simpa only [hr, Finset.mem_range, initialLabels] using hf.symm

private theorem columnSlice_self_card (t : Tableau p) (j k : ℕ) :
    (columnSlice t t j k).card = min k (columnLength p j) := by
  classical
  rw [← Finset.card_range (min k (columnLength p j))]
  apply Finset.card_bij (fun a _ => labelRow t a)
  · intro a ha
    obtain ⟨hr, hc⟩ := (mem_columnSlice t t j k a).mp ha
    rw [Finset.mem_range, lt_min_iff]
    refine ⟨hr, ?_⟩
    have hh := (cell_iff_column p _ _).mp (label_cell t a)
    simpa only [hc] using hh
  · intro a ha b hb he
    exact row_column_injective t he
      (((mem_columnSlice t t j k a).mp ha).2.trans
        ((mem_columnSlice t t j k b).mp hb).2.symm)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    let c : Cell p := ⟨(i,j), (cell_iff_column p i j).mpr (lt_min_iff.mp hi').2⟩
    refine ⟨t c, ?_, ?_⟩
    · rw [mem_columnSlice]
      simpa [labelRow, labelColumn, Specs.AdvancedFiniteGroupRepresentations.labelRow,
        Specs.AdvancedFiniteGroupRepresentations.labelColumn, c] using (lt_min_iff.mp hi').1
    · simp [labelRow, Specs.AdvancedFiniteGroupRepresentations.labelRow, c]

private theorem columnSlice_card_le (t : Tableau p) (u : Tableau q)
    (h : ¬ RowColumnCollision t u) (j k : ℕ) :
    (columnSlice t u j k).card ≤ (columnSlice t t j k).card := by
  classical
  rw [columnSlice_self_card, le_min_iff]
  constructor
  · suffices (columnSlice t u j k).card ≤ (Finset.range k).card by simpa using this
    apply Finset.card_le_card_of_injOn (f := labelRow u)
    · intro a ha
      exact Finset.mem_range.mpr ((mem_columnSlice t u j k a).mp ha).1
    · intro a ha b hb he
      exact noCollision_injective t u h
        (((mem_columnSlice t u j k a).mp ha).2.trans
          ((mem_columnSlice t u j k b).mp hb).2.symm) he
  · suffices (columnSlice t u j k).card ≤ (Finset.range (columnLength p j)).card by
      simpa using this
    apply Finset.card_le_card_of_injOn (f := labelRow t)
    · intro a ha
      have hc := ((mem_columnSlice t u j k a).mp ha).2
      have hh := (cell_iff_column p _ _).mp (label_cell t a)
      exact Finset.mem_range.mpr (hc ▸ hh)
    · intro a ha b hb he
      exact row_column_injective t he
        (((mem_columnSlice t u j k a).mp ha).2.trans
          ((mem_columnSlice t u j k b).mp hb).2.symm)

private theorem sum_columnSlice (t : Tableau p) (u : Tableau q) (k : ℕ) :
    ∑ j ∈ (Finset.univ.image (labelColumn t)), (columnSlice t u j k).card =
      (initialLabels u k).card := by
  classical
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro a _
  exact Finset.mem_image_of_mem _ (Finset.mem_univ a)

/-- Counting the first k rows one column at a time. -/
theorem dominates_of_no_row_column_collision (t : Tableau p) (u : Tableau q)
    (h : ¬ RowColumnCollision t u) : dominates p q := by
  intro k
  rw [← initialLabels_card u k, ← initialLabels_card t k,
    ← sum_columnSlice t u k, ← sum_columnSlice t t k]
  exact Finset.sum_le_sum (fun j _ => columnSlice_card_le t u h j k)

theorem row_column_test (t : Tableau p) (u : Tableau q)
    (h : ¬ dominates p q) : RowColumnCollision t u := by
  by_contra hn
  exact h (dominates_of_no_row_column_collision t u hn)

/-- With equal shapes, equality of the sums forces equality in each column. -/
private theorem columnSlice_card_eq (t u : Tableau p) (h : ¬ RowColumnCollision t u)
    (j k : ℕ) (hj : j ∈ Finset.univ.image (labelColumn t)) :
    (columnSlice t u j k).card = (columnSlice t t j k).card := by
  classical
  have hs : ∑ j ∈ Finset.univ.image (labelColumn t), (columnSlice t u j k).card =
      ∑ j ∈ Finset.univ.image (labelColumn t), (columnSlice t t j k).card := by
    rw [sum_columnSlice, sum_columnSlice, initialLabels_card, initialLabels_card]
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => columnSlice_card_le t u h j k)).mp hs j hj

/-- A column of height H supplies all its labels to the first H rows. -/
private theorem mixed_cell (t u : Tableau p) (h : ¬ RowColumnCollision t u) (a : Fin n) :
    (labelRow u a, labelColumn t a) ∈ cells p := by
  classical
  let j := labelColumn t a
  let k := columnLength p j
  have ht : a ∈ columnSlice t t j k := by
    apply (mem_columnSlice t t j k a).mpr
    exact ⟨(cell_iff_column p _ _).mp (label_cell t a), rfl⟩
  have he : columnSlice t u j k = columnSlice t t j k := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨_, hc⟩ := (mem_columnSlice t u j k b).mp hb
      apply (mem_columnSlice t t j k b).mpr
      refine ⟨?_, hc⟩
      have hh := (cell_iff_column p _ _).mp (label_cell t b)
      simpa only [hc] using hh
    · exact (columnSlice_card_eq t u h j k
        (Finset.mem_image_of_mem _ (Finset.mem_univ a))).ge
  rw [← he] at ht
  exact (cell_iff_column p _ _).mpr ((mem_columnSlice t u j k a).mp ht).1

/-- The column subgroup acts freely on the tabloid of its tableau. -/
theorem column_tabloid_injective (t : Tableau p) :
    Function.Injective (fun c : columnSubgroup t => tabloid (c.val • t)) := by
  intro c d hcd
  have hr : labelRow (c.val • t) = labelRow (d.val • t) := Quotient.exact hcd
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro a
  apply row_column_injective t
  · exact congrFun hr a
  · have hc := c.property (c.val.symm a)
    have hd := d.property (d.val.symm a)
    simp only [Equiv.apply_symm_apply] at hc hd
    exact hc.symm.trans hd

/-- Assemble the unique column matching from the mixed row--column cells. -/
theorem row_column_unique (t u : Tableau p) (h : ¬ RowColumnCollision t u) :
    ∃! c : columnSubgroup t, tabloid u = tabloid (c.val • t) := by
  classical
  let f : Fin n → Fin n := fun a =>
    t ⟨(labelRow u a, labelColumn t a), mixed_cell t u h a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hh := congrArg (fun x : Fin n => (t.symm x).val) hab
    simp only [f, Equiv.symm_apply_apply] at hh
    have hr := congrArg Prod.fst hh
    have hc := congrArg Prod.snd hh
    exact noCollision_injective t u h hc hr
  let e : SymmetricGroup n := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hecol : e ∈ columnSubgroup t := by
    intro a
    change (t.symm (f a)).val.2 = (t.symm a).val.2
    simp only [f, Equiv.symm_apply_apply]
    rfl
  have herow : ∀ a, labelRow t (e a) = labelRow u a := by
    intro a
    change (t.symm (f a)).val.1 = labelRow u a
    simp only [f, Equiv.symm_apply_apply]
  let c : columnSubgroup t := (⟨e, hecol⟩ : columnSubgroup t)⁻¹
  have hc : tabloid u = tabloid (c.val • t) := by
    apply Quotient.sound
    change labelRow u = labelRow (c.val • t)
    funext a
    change labelRow u a = labelRow t (e a)
    exact (herow a).symm
  exact ⟨c, hc, fun d hd => column_tabloid_injective t (hd.symm.trans hc)⟩

end AdvancedFiniteGroupRepresentations
