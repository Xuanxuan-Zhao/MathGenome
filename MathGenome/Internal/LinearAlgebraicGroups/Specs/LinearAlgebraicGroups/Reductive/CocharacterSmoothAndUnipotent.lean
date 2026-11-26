import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics
open CharacterDescent (Cocharacter)

/-- All three closed subgroups representing the limit and centralizer functors
are smooth over the base field. -/
def LimitSubgroupsSmooth : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar),
    Smooth D.parabolic.group.X.hom ∧
      Smooth D.contracting.group.X.hom ∧
      Smooth D.centralizer.group.X.hom

/-- The subgroup of elements contracting to the identity is unipotent in
the invariant-vector sense of B06. -/
def ContractingSubgroupUnipotent : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    (cochar : Cocharacter G.val) (D : LimitDecomposition cochar),
    Unipotent.IsUnipotent
      (affineAlgebraicSubgroup D.contracting G.property.1 G.property.2.1 G.property.2.2)

end LinearAlgebraicGroups.Specs.CocharacterDynamics
