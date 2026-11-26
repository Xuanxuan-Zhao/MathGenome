import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RelativeRank

/-- A connected semisimple group and its quotient by the full scheme centre have the same
relative rank. The rank uses closed split subgroup schemes over the original field. -/
def SemisimpleAdjointRank : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), GeometricRadicals.IsSemisimple G →
    AdjointCocharacters.IsAdjointQuotient Z q → relativeRank G = relativeRank Q

end LinearAlgebraicGroups.Specs.RelativeRank
