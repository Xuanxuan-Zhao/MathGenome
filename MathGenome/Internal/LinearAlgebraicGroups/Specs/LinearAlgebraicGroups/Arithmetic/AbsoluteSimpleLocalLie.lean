import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.Algebra.Lie.Semisimple.Defs

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs

open GeometricRadicals

/-- Absolute almost simplicity is the absence of intermediate smooth connected
normal subgroups in the nontrivial geometrically semisimple group. -/
def IsAbsolutelyAlmostSimple {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  IsSemisimple G ∧
    ¬ Nonempty ((GeometricGroup G).val ≅ Grp.trivial (SchemeOver (AlgebraicClosure k))) ∧
    ∀ N : ClosedSubgroup (GeometricGroup G).val, IsSmoothConnectedNormal N →
      IsTrivialSubgroup N ∨ IsIso N.inclusion

/-- The scheme Lie algebra of an absolutely almost simple group in characteristic
zero is simple over the ground field. This applies to both split and nonsplit
forms over the characteristic-zero local fields. -/
def AbsoluteSimpleLocalLie : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsAbsolutelyAlmostSimple G → ∀ s : IdentityLieStructure G.val,
      letI := s.lieRing
      letI := s.lieAlgebra
      LieAlgebra.IsSimple k (Lie k G.val)

end LinearAlgebraicGroups.Specs
