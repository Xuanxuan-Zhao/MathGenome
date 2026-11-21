import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.FinitePartitionData
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.MarkedCellBudget
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Marking uses open cells. Choosing an interior node in each marked cell
is injective because open cells of a strictly increasing partition are disjoint. -/

noncomputable section

namespace D03Insertion

theorem interiorIndices_card (s : ℕ) : (interiorIndices s).card = s - 1 := by
  have h : interiorIndices s = Finset.Ioo (0 : Fin (s + 1)) (Fin.last s) := by
    ext k
    simp only [interiorIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioo, Fin.lt_def, Fin.val_zero, Fin.val_last]
  rw [h, Fin.card_Ioo]
  simp

theorem open_cells_unique {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq : StrictMono q) {x : ℝ} {i j : Fin n}
    (hil : left q i < x) (hir : x < right q i)
    (hjl : left q j < x) (hjr : x < right q j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have he : i.succ ≤ j.castSucc := by
      show i.val + 1 ≤ j.val
      exact hij
    have ho : right q i ≤ left q j := hq.monotone he
    exact False.elim (not_lt_of_ge ho (lt_trans hjl hir))
  · exact hij
  · have he : j.succ ≤ i.castSucc := by
      show j.val + 1 ≤ i.val
      exact hij
    have ho : right q j ≤ left q i := hq.monotone he
    exact False.elim (not_lt_of_ge ho (lt_trans hil hjr))

theorem marked_card_le {a b : ℝ} {s n : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ}
    (_hab : a < b) (_hp : ValidPartition a b p) (hq : ValidPartition a b q) :
    (marked p q).card ≤ s - 1 := by
  classical
  have witness (i : ↥(marked p q)) :
      ∃ k : ↥(interiorIndices s), left q i.val < p k.val ∧ p k.val < right q i.val := by
    obtain ⟨k, hk, hl, hr⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨k, hk⟩, hl, hr⟩
  let chooseNode : ↥(marked p q) → ↥(interiorIndices s) :=
    fun i => Classical.choose (witness i)
  have hchoose (i : ↥(marked p q)) :
      left q i.val < p (chooseNode i).val ∧ p (chooseNode i).val < right q i.val :=
    Classical.choose_spec (witness i)
  have hinj : Function.Injective chooseNode := by
    intro i j heq
    apply Subtype.ext
    have hi := hchoose i
    have hj := hchoose j
    rw [← heq] at hj
    exact open_cells_unique hq.2.1 hi.1 hi.2 hj.1 hj.2
  calc
    (marked p q).card ≤ (interiorIndices s).card :=
      Finset.card_le_card_of_injective hinj
    _ = s - 1 := interiorIndices_card s

theorem marked_length_budget {a b : ℝ} {s n : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ}
    (hab : a < b) (hp : ValidPartition a b p) (hq : ValidPartition a b q) :
    0 ≤ ∑ i ∈ marked p q, width q i ∧
    (∑ i ∈ marked p q, width q i) ≤ ((s - 1 : ℕ) : ℝ) * mesh q := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (width_pos hq i).le)
  · calc
      (∑ i ∈ marked p q, width q i) ≤ ∑ _i ∈ marked p q, mesh q :=
        Finset.sum_le_sum (fun i _ => width_le_mesh q i)
      _ = ((marked p q).card : ℝ) * mesh q := by simp
      _ ≤ ((s - 1 : ℕ) : ℝ) * mesh q :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (marked_card_le hab hp hq))
          (mesh_nonneg q)

theorem marked_eq_empty_of_one {a b : ℝ} {n : ℕ}
    {p : Fin (1 + 1) → ℝ} {q : Fin (n + 1) → ℝ}
    (hab : a < b) (hp : ValidPartition a b p) (hq : ValidPartition a b q) :
    marked p q = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := marked_card_le hab hp hq
  simpa using h

theorem marked_length_eq_zero_of_one {a b : ℝ} {n : ℕ}
    {p : Fin (1 + 1) → ℝ} {q : Fin (n + 1) → ℝ}
    (hab : a < b) (hp : ValidPartition a b p) (hq : ValidPartition a b q) :
    (∑ i ∈ marked p q, width q i) = 0 := by
  rw [marked_eq_empty_of_one hab hp hq, Finset.sum_empty]

end D03Insertion
