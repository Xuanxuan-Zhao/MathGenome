import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.SplitToriConjugacy

open GeometricBorelConjugacy (ConjugatesSubgroups)
open GeometricRadicals (IsMaximalTorus IsSplitReductive IsSplitTorus baseChangedSubgroup)

/-- Any two split geometrically maximal tori of a split connected reductive
group over a field are conjugate as closed subgroup schemes by a rational point. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSplitReductive G →
    ∀ T T' : ClosedSubgroup G.val, IsSplitTorus T.group → IsSplitTorus T'.group →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T'.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T' h)) →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g T T'

end LinearAlgebraicGroups.Specs.SplitToriConjugacy
