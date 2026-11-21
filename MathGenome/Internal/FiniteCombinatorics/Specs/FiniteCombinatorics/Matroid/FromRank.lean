import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation

/-! W64(3): arbitrary integer rank data on a finite ground. Values outside
`2^E` are unconstrained and are not asserted to be recovered. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def rankPresentationBounds : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ r : Set α → ℤ,
    RankPresentation E r → ∀ A, A ⊆ E → 0 ≤ r A ∧ r A ≤ (A.ncard : ℤ)

def existsMatroidFromRank : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ r : Set α → ℤ,
    RankPresentation E r → ∃ M : _root_.Matroid α,
      M.E = E ∧ ∃ hM : M.Finite,
        (∀ I, M.Indep I ↔ RankIndependent E r I) ∧
        (∀ A, A ⊆ E → @rank α M hM A = r A)

end FiniteCombinatorics.Matroid.Expected
