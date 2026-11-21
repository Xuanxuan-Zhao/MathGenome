import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.CellGeometry

/-! Independent obligations for exact cell-length conservation and regrouping. -/
namespace D03Insertion.Specification

/-- Every containing-parent assignment conserves the length of each old cell. -/
def refined_cell_length_sumType : Prop :=
  ∀ {a b : ℝ} (_hab : a < b) {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ},
    ValidPartition a b p → ValidPartition a b q → ValidPartition a b r →
    nodes r = nodes p ∪ nodes q →
    ∀ (c : Fin t → Fin n),
      (∀ j, left q (c j) ≤ left r j ∧ right r j ≤ right q (c j)) →
      ∀ i : Fin n,
        ∑ j ∈ Finset.univ.filter (fun j => c j = i), width r j = width q i

/-- A finite sum can be regrouped over all fibers of any parent map.
The general additive-monoid statement includes both real and complex summands. -/
def parent_fiber_sumType : Prop :=
  ∀ {K : Type} [AddCommMonoid K] {n t : ℕ}
    (c : Fin t → Fin n) (H : Fin t → K),
    ∑ j : Fin t, H j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => c j = i), H j

end D03Insertion.Specification
