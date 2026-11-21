import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation

namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

/-- Cardinal augmentation follows from the four closure axioms on the finite ground. -/
def closureAugmentation : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite →
    ∀ (c : Set α → Set α), ClosurePresentation E c →
    ∀ I J, ClosureIndependent E c I → ClosureIndependent E c J →
      I.ncard < J.ncard → ∃ e ∈ J \ I, ClosureIndependent E c (insert e I)

/-- The independent sets and canonical closure both recover the original data.
There is no assumption on c(∅), nor any nonemptiness assumption on E. -/
def closureRealization : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite →
    ∀ (c : Set α → Set α), ClosurePresentation E c →
    ∃ M : _root_.Matroid α, M.E = E ∧ M.Finite ∧
      (∀ I, M.Indep I ↔ ClosureIndependent E c I) ∧
      (∀ A, A ⊆ E → M.closure A = c A)

end FiniteCombinatorics.Matroid.Expected
