import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.FinitePartitionData

/-! Independent statements of the geometry of an arbitrary sorted node union. -/
namespace D03Insertion.Specification

/-- Every refined cell has exactly one containing old cell. -/
def refined_cell_parentType : Prop :=
  ∀ {a b : ℝ} (_hab : a < b) {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ},
    ValidPartition a b p → ValidPartition a b q → ValidPartition a b r →
    nodes r = nodes p ∪ nodes q →
    ∀ j : Fin t, ∃! i : Fin n,
      left q i ≤ left r j ∧ right r j ≤ right q i

/-- A parent assignment, its uniqueness, unchanged cells, and the exact
characterization of singleton fibers. The last clause also gives both endpoints
and unmarkedness from the singleton-fiber hypothesis alone. -/
def refined_cell_geometryType : Prop :=
  ∀ {a b : ℝ} (_hab : a < b) {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ},
    ValidPartition a b p → ValidPartition a b q → ValidPartition a b r →
    nodes r = nodes p ∪ nodes q →
    ∃ c : Fin t → Fin n,
      (∀ j, left q (c j) ≤ left r j ∧ right r j ≤ right q (c j)) ∧
      (∀ j i, left q i ≤ left r j ∧ right r j ≤ right q i → c j = i) ∧
      (∀ i, i ∉ marked p q →
        ∃! j, left r j = left q i ∧ right r j = right q i) ∧
      (∀ i j, (∀ k, c k = i ↔ k = j) ↔
        ((left r j = left q i ∧ right r j = right q i) ∧ i ∉ marked p q))

end D03Insertion.Specification
