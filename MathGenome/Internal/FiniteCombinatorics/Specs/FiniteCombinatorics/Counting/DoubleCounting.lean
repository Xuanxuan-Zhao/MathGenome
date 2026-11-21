import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
The independent statement of paper.tex, Proposition p204:W03.
Finite sets are represented by `Finset`s in arbitrary ambient types.
The relation is a finite set of ordered pairs, contained in the specified
Cartesian product. No nonemptiness assumption is imposed.
-/

universe u v

namespace Specs.FiniteCombinatorics.Counting

/-- The cardinality of an incidence relation equals both sums of fiber cardinalities.
The two equalities together give the chain of equalities in the source. -/
def incidenceCount : Prop := by
  classical
  exact ∀ {α : Type u} {β : Type v}
    (A : Finset α) (B : Finset β) (R : Finset (α × β)),
    R ⊆ A.product B →
      R.card = ∑ a ∈ A, (B.filter (fun b => (a, b) ∈ R)).card ∧
      R.card = ∑ b ∈ B, (A.filter (fun a => (a, b) ∈ R)).card

end Specs.FiniteCombinatorics.Counting
