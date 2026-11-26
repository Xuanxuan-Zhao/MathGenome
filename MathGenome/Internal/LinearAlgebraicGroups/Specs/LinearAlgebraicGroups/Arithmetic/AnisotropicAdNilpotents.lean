import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.Algebra.Lie.OfAssociative

universe u

namespace LinearAlgebraicGroups.Specs.AnisotropicAdNilpotents

/-- Anisotropy over the ground field means every closed split torus is trivial. -/
def IsAnisotropic {k : Type u} [Field k] (G : GroupScheme k) : Prop :=
  ∀ T : ClosedSubgroup G, GeometricRadicals.IsSplitTorus T.group →
    GeometricRadicals.IsTrivialSubgroup T

/-- The Lie algebra of a connected semisimple anisotropic group over a
characteristic-zero field has no nonzero element with nilpotent adjoint action. -/
def AdNilpotentEqZero : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    GeometricRadicals.IsSemisimple G → IsAnisotropic G.val →
    ∀ s : IdentityLieStructure G.val,
      letI := s.lieRing
      letI := s.lieAlgebra
      ∀ e : Lie k G.val, IsNilpotent (LieAlgebra.ad k (Lie k G.val) e) → e = 0

end LinearAlgebraicGroups.Specs.AnisotropicAdNilpotents
