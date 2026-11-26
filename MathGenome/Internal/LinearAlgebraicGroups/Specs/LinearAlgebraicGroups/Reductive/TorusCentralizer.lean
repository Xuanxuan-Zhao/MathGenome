import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SubtorusCentralizer

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.TorusCentralizer

open GeometricRadicals (IsMaximalTorus IsReductive IsTorus baseChangedSubgroup)
open SubtorusCentralizer (IsCentralizer)

/-- A geometrically maximal torus of a connected reductive group is its own
scheme-theoretic centralizer. -/
def MaximalTorusCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsTorus T.group →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) →
      IsCentralizer T T

end LinearAlgebraicGroups.Specs.TorusCentralizer
