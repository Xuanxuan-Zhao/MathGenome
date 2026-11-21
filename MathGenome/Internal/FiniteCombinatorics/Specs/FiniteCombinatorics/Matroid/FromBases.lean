import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation

/-! W64(2): finite basis exchange, with no cardinality or maximality hypotheses.
The predicates here come from the independent shared foundation Specs. -/
namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u

def basisPresentationAugmentation : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite →
    ∀ (B : Set (Set α)), BasisPresentation E B →
      ∀ (I J : Set α), BasisIndependent E B I → BasisIndependent E B J →
        I.ncard < J.ncard → ∃ e ∈ J \ I, BasisIndependent E B (insert e I)

def basisPresentationEquicardinal : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite →
    ∀ (B : Set (Set α)), BasisPresentation E B →
      ∀ D ∈ B, ∀ F ∈ B, D.ncard = F.ncard

def existsMatroidOfBases : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite →
    ∀ (B : Set (Set α)), BasisPresentation E B →
      ∃ M : _root_.Matroid α,
        M.E = E ∧ M.Finite ∧
        (∀ I, M.Indep I ↔ BasisIndependent E B I) ∧
        (∀ D, M.IsBase D ↔ D ∈ B)

end FiniteCombinatorics.Matroid.Expected
