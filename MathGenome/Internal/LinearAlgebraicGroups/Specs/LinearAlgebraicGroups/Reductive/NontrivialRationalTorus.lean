import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.NontrivialRationalTorus

open GeometricRadicals (GeometricGroup IsTorus IsTrivialSubgroup)

/-- Over an infinite field, a smooth connected affine algebraic group with a
nontrivial geometric torus has a nontrivial torus over the ground field. -/
def ExistsNontrivialTorus : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    (∃ T : ClosedSubgroup (GeometricGroup G).val, IsTorus T.group ∧ ¬ IsTrivialSubgroup T) →
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧ ¬ IsTrivialSubgroup T

end LinearAlgebraicGroups.Specs.NontrivialRationalTorus
