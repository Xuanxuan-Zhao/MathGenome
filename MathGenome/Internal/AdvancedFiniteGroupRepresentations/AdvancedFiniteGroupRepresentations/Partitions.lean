import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Partitions
import Lean.Elab.Tactic.Omega

open scoped BigOperators
universe u

namespace AdvancedFiniteGroupRepresentations

abbrev SymmetricGroup := @Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup

abbrev GroupAlgebra := @Specs.AdvancedFiniteGroupRepresentations.GroupAlgebra

abbrev Partition := @Specs.AdvancedFiniteGroupRepresentations.Partition

abbrev diagram := @Specs.AdvancedFiniteGroupRepresentations.diagram

abbrev diagramEquiv := @Specs.AdvancedFiniteGroupRepresentations.diagramEquiv

abbrev parts := @Specs.AdvancedFiniteGroupRepresentations.parts

abbrev OrderedParts := @Specs.AdvancedFiniteGroupRepresentations.OrderedParts

abbrev cells := @Specs.AdvancedFiniteGroupRepresentations.cells

abbrev Cell := @Specs.AdvancedFiniteGroupRepresentations.Cell

abbrev rowLength := @Specs.AdvancedFiniteGroupRepresentations.rowLength

abbrev columnLength := @Specs.AdvancedFiniteGroupRepresentations.columnLength

abbrev length := @Specs.AdvancedFiniteGroupRepresentations.length

abbrev transpose := @Specs.AdvancedFiniteGroupRepresentations.transpose

abbrev dominates := @Specs.AdvancedFiniteGroupRepresentations.dominates

abbrev emptyPartition := @Specs.AdvancedFiniteGroupRepresentations.emptyPartition

abbrev cellOneBased := @Specs.AdvancedFiniteGroupRepresentations.cellOneBased

abbrev relabel := @Specs.AdvancedFiniteGroupRepresentations.relabel

abbrev relabelLabeling := @Specs.AdvancedFiniteGroupRepresentations.relabelLabeling

theorem parts_sorted : ∀ {n} (p : Partition n), (parts p).SortedGE := by
  intro n p
  exact (diagram p).rowLens_sorted

theorem parts_positive : ∀ {n} (p : Partition n) (x : ℕ), x ∈ parts p → 0 < x := by
  intro n p x hx
  exact (diagram p).pos_of_mem_rowLens x hx

theorem parts_sum : ∀ {n} (p : Partition n), (parts p).sum = n := by
  intro n p
  exact ((diagram p).sum_rowLens_eq_card).trans (YoungDiagram.card_ofPartition p)

theorem diagram_card : ∀ {n} (p : Partition n), (diagram p).card = n := by
  intro n p
  exact YoungDiagram.card_ofPartition p

theorem diagramEquiv_apply : ∀ {n} (p : Partition n), (diagramEquiv n p).val = diagram p := by
  intro n p
  rfl

theorem orderedParts_equivalence : ∀ n, ∃ e : Partition n ≃ OrderedParts n, ∀ p, (e p).val = parts p := by
  intro n
  let e : Partition n ≃ OrderedParts n :=
    { toFun := fun p => ⟨parts p, parts_sorted p, parts_positive p, parts_sum p⟩
      invFun := fun w => (YoungDiagram.ofRowLens w.val w.property.1).toPartition
        (by rw [← YoungDiagram.sum_rowLens_eq_card,
                YoungDiagram.rowLens_ofRowLens_eq_self w.property.2.1]; exact w.property.2.2)
      left_inv := by
        intro p
        change (YoungDiagram.ofRowLens (diagram p).rowLens _).toPartition _ = p
        simp only [YoungDiagram.ofRowLens_to_rowLens_eq_self]
        exact YoungDiagram.toPartition_ofPartition
      right_inv := by
        intro w
        apply Subtype.ext
        change (YoungDiagram.ofPartition ((YoungDiagram.ofRowLens w.val _).toPartition _)).rowLens = w.val
        rw [YoungDiagram.ofPartition_toPartition]
        exact YoungDiagram.rowLens_ofRowLens_eq_self w.property.2.1 }
  exact ⟨e, fun _ => rfl⟩

theorem parts_eq_sorted_multiset : ∀ {n} (p : Partition n), parts p = p.parts.sort (· ≥ ·) := by
  intro n p
  exact YoungDiagram.rowLens_ofPartition_eq_sort_parts p





theorem length_eq_columnLength_zero : ∀ {n} (p : Partition n), length p = columnLength p 0 := by
  intro n p
  exact YoungDiagram.length_rowLens

theorem rowLength_antitone : ∀ {n} (p : Partition n), Antitone (rowLength p) := by
  intro n p i j hij
  exact (diagram p).rowLen_anti i j hij

theorem rowLength_zero_of_length_le : ∀ {n} (p : Partition n) (i : ℕ), length p ≤ i → rowLength p i = 0 := by
  intro n p i hi
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hc : (i, 0) ∈ diagram p := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
  have hlt := YoungDiagram.mem_iff_lt_colLen.mp hc
  change i < columnLength p 0 at hlt
  rw [← length_eq_columnLength_zero] at hlt
  omega

theorem rowLength_eq_getD : ∀ {n} (p : Partition n) (i : ℕ), rowLength p i = (parts p)[i]?.getD 0 := by
  intro n p i
  by_cases hi : i < (parts p).length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some]
    exact YoungDiagram.get_rowLens.symm
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]
    exact rowLength_zero_of_length_le p i (Nat.le_of_not_gt hi)

theorem cell_iff : ∀ {n} (p : Partition n) (i j : ℕ), (i,j) ∈ cells p ↔ j < rowLength p i := by
  intro n p i j
  exact YoungDiagram.mem_iff_lt_rowLen

theorem cell_iff_column : ∀ {n} (p : Partition n) (i j : ℕ), (i,j) ∈ cells p ↔ i < columnLength p j := by
  intro n p i j
  exact YoungDiagram.mem_iff_lt_colLen

theorem cellOneBased_iff : ∀ {n} (p : Partition n) (i j : ℕ), cellOneBased p i j ↔ 0 < i ∧ 0 < j ∧ j ≤ rowLength p (i-1) := by
  intro n p i j
  change (0 < i ∧ 0 < j ∧ (i - 1, j - 1) ∈ cells p) ↔ _
  rw [cell_iff]
  omega

theorem transpose_diagram : ∀ {n} (p : Partition n), diagram (transpose p) = (diagram p).transpose := by
  intro n p
  exact YoungDiagram.ofPartition_toPartition (by simp)

theorem transpose_columnLength : ∀ {n} (p : Partition n) (i : ℕ), columnLength (transpose p) i = rowLength p i := by
  intro n p i
  change (diagram (transpose p)).colLen i = _
  rw [transpose_diagram]
  exact YoungDiagram.colLen_transpose _ _

theorem transpose_rowLength : ∀ {n} (p : Partition n) (j : ℕ), rowLength (transpose p) j = columnLength p j := by
  intro n p j
  change (diagram (transpose p)).rowLen j = _
  rw [transpose_diagram]
  exact YoungDiagram.rowLen_transpose _ _

theorem transpose_involutive : ∀ {n} (p : Partition n), transpose (transpose p) = p := by
  intro n p
  exact Nat.Partition.conjugate_conjugate p

theorem dominance_antisymm : ∀ {n} (p μ : Partition n), dominates p μ → dominates μ p → p = μ := by
  intro n p μ h₁ h₂
  have hs : ∀ k, (∑ i ∈ Finset.range k, rowLength p i) =
      ∑ i ∈ Finset.range k, rowLength μ i := fun k => Nat.le_antisymm (h₂ k) (h₁ k)
  have hr : ∀ i, rowLength p i = rowLength μ i := by
    intro i
    have ha := hs (i + 1)
    simp only [Finset.sum_range_succ, hs i] at ha
    exact Nat.add_left_cancel ha
  apply YoungDiagram.equivPartition.symm.injective
  apply Subtype.ext
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  change (i,j) ∈ cells p ↔ (i,j) ∈ cells μ
  rw [cell_iff, cell_iff, hr]

theorem dominance_refl : ∀ {n} (p : Partition n), dominates p p := by
  intro n p k
  exact le_refl _

theorem dominance_trans : ∀ {n} (p μ ν : Partition n), dominates p μ → dominates μ ν → dominates p ν := by
  intro n p μ ν h₁ h₂ k
  exact (h₂ k).trans (h₁ k)

theorem zero_partition_unique : ∀ p : Partition 0, p = emptyPartition := by
  intro p
  exact Subsingleton.elim _ _

theorem empty_parts : parts emptyPartition = [] := by
  change (YoungDiagram.ofPartition (default : Nat.Partition 0)).rowLens = []
  simp

theorem empty_cells : cells emptyPartition = ∅ := by
  apply Finset.card_eq_zero.mp
  exact diagram_card emptyPartition

theorem empty_length : length emptyPartition = 0 := by
  change (parts emptyPartition).length = 0
  rw [empty_parts]
  rfl

theorem empty_transpose : transpose emptyPartition = emptyPartition := by
  exact Subsingleton.elim _ _

theorem zero_labels_trivial : ∀ σ : SymmetricGroup 0, σ = 1 := by
  intro σ
  exact Subsingleton.elim _ _

theorem permutation_mul_apply : ∀ {n} (σ τ : SymmetricGroup n) (i : Fin n), (σ * τ) i = σ (τ i) := by
  intro n σ τ i
  rfl

theorem relabel_one : ∀ {n} {α : Type u} (t : α → Fin n), relabel (1 : SymmetricGroup n) t = t := by
  intro n α t
  rfl

theorem relabel_mul : ∀ {n} {α : Type u} (σ τ : SymmetricGroup n) (t : α → Fin n), relabel (σ * τ) t = relabel σ (relabel τ t) := by
  intro n α σ τ t
  rfl

theorem relabelLabeling_apply : ∀ {n} {α : Type u} (σ : SymmetricGroup n) (t : α ≃ Fin n) (a : α), relabelLabeling σ t a = σ (t a) := by
  intro n α σ t a
  rfl

end AdvancedFiniteGroupRepresentations
