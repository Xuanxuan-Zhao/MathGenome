import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations

/-! Independent statement of the first paragraph of paper.tex, W68.
The ground is finite, but the ambient type is unrestricted. The element
being added may be a loop, and the independent set need not be a basis. -/

namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

/-- There is a unique circuit in `I + e`, and deleting `f ∈ I` makes
`I + e` independent exactly when `f` belongs to that circuit. -/
def fundamentalCircuit : Prop :=
  ∀ {α : Type u}, ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α) (e : α),
    M.Indep I → e ∈ M.closure I \ I →
      ∃ C : Set α, M.IsCircuit C ∧ C ⊆ insert e I ∧
        (∀ D : Set α, M.IsCircuit D → D ⊆ insert e I → D = C) ∧
        ∀ f ∈ I, M.Indep (insert e (I \ {f})) ↔ f ∈ C

end FiniteCombinatorics.Matroid.Expected
