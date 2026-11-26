import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

universe u

namespace LinearAlgebraicGroups.Specs.SemisimplyDifferentiated

/-- In characteristic zero the identity-tangent Lie algebra of a connected
semisimple affine algebraic group is finite dimensional and has zero solvable
radical. The radical predicate is the one used by Weyl complete reducibility. -/
def LieSemisimple : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    GeometricRadicals.IsSemisimple G →
    ∀ s : IdentityLieStructure G.val,
      letI := s.lieRing
      letI := s.lieAlgebra
      FiniteDimensional k (Lie k G.val) ∧
        _root_.Specs.LieAlgebrasAndRepresentations.SolvableRadical.IsSemisimple_value
          k (Lie k G.val)

end LinearAlgebraicGroups.Specs.SemisimplyDifferentiated
