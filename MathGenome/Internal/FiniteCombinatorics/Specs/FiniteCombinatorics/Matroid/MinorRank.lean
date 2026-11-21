import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.DualRank
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations

/-! Independent statements for the rank and basis assertions of W69.
Only the ground is finite. Every rank is the shared integer rank, and the
retained ground is the relative complement in the original ground. -/

namespace FiniteCombinatorics.Matroid.Expected

open Set
open scoped _root_.Matroid
universe u

def deletionRank : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C A : Set α),
    C ⊆ M.E → A ⊆ relativeCompl M.E C →
      rank (M ＼ C) A = rank M A

def contractionRank : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C A : Set α),
    C ⊆ M.E → A ⊆ relativeCompl M.E C →
      rank (M ／ C) A = rank M (A ∪ C) - rank M C

/-- The criterion holds for every basis of C, including when C is dependent. -/
def contractionIndependentBasis : Prop :=
  ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite] (C I J : Set α),
    C ⊆ M.E → M.IsBasis I C → J ⊆ relativeCompl M.E C →
      ((M ／ C).Indep J ↔ M.Indep (I ∪ J))

end FiniteCombinatorics.Matroid.Expected
