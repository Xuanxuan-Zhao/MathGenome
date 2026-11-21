import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.FinitePartitionData

/-! Independent propositions for the marked-cell counting and length budget.
No refinement, tags, function bound, or counting certificate is assumed. -/

noncomputable section

namespace D03Insertion.Specification

/-- There are exactly s - 1 indices strictly between the endpoint indices. -/
def interiorIndices_cardType : Prop :=
  ∀ s : ℕ, (interiorIndices s).card = s - 1

/-- An arbitrary real point belongs to at most one open cell of a strictly
increasing partition. In particular this applies to every interior P node. -/
def open_cells_uniqueType : Prop :=
  ∀ {n : ℕ} {q : Fin (n + 1) → ℝ}, StrictMono q →
    ∀ {x : ℝ} {i j : Fin n},
      left q i < x → x < right q i →
      left q j < x → x < right q j → i = j

/-- The number of marked cells is at most the number of interior P nodes. -/
def marked_card_leType : Prop :=
  ∀ {a b : ℝ} {s n : ℕ} {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ},
    a < b → ValidPartition a b p → ValidPartition a b q →
      (marked p q).card ≤ s - 1

/-- The complete nonnegative real length budget, with natural subtraction
performed before the cast to the reals. -/
def marked_length_budgetType : Prop :=
  ∀ {a b : ℝ} {s n : ℕ} {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ},
    a < b → ValidPartition a b p → ValidPartition a b q →
      0 ≤ ∑ i ∈ marked p q, width q i ∧
      (∑ i ∈ marked p q, width q i) ≤ ((s - 1 : ℕ) : ℝ) * mesh q

/-- With one P cell there are no marked Q cells. -/
def marked_eq_empty_of_oneType : Prop :=
  ∀ {a b : ℝ} {n : ℕ} {p : Fin (1 + 1) → ℝ} {q : Fin (n + 1) → ℝ},
    a < b → ValidPartition a b p → ValidPartition a b q → marked p q = ∅

/-- The marked length is exactly zero in the one-cell P case. -/
def marked_length_eq_zero_of_oneType : Prop :=
  ∀ {a b : ℝ} {n : ℕ} {p : Fin (1 + 1) → ℝ} {q : Fin (n + 1) → ℝ},
    a < b → ValidPartition a b p → ValidPartition a b q →
      (∑ i ∈ marked p q, width q i) = 0

end D03Insertion.Specification
