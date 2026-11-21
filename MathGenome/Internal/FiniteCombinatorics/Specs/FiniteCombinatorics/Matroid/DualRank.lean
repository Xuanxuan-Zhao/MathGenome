import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Duality

/-! The integer dual rank formula in paper.tex, W67.
Only the ground set must be finite; the ambient type is arbitrary.
All complements are relative to that ground, and subtraction is in ℤ. -/

namespace FiniteCombinatorics.Matroid.Expected

open Set
open scoped _root_.Matroid
universe u

/-- The formula applies to every subset, including the empty and full ground sets. -/
def dualRank : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E →
      rank M✶ A = (A.ncard : ℤ) + rank M (relativeCompl M.E A) - rank M M.E

end FiniteCombinatorics.Matroid.Expected
