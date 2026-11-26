import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

namespace LinearAlgebraicGroups.Specs.ComplexToralInvolutions

open CategoryTheory
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open AdjointRepresentation (GroupPoints)
open IntegralModels (MatrixRealization)
open Pinning (SplitBorelPair)

/-- Every square-one complex point is conjugate to a point of the specified
maximal torus of the split Borel pair. -/
def ToralInvolutions : Prop :=
  ∀ (P : SplitBorelPair ℂ) (i : MatrixRealization P.G) (x : PointsIn i ℂ),
    x * x = 1 →
    ∃ (g : PointsIn i ℂ) (t : GroupPoints P.T.group (CommAlgCat.of ℂ ℂ)),
      g * x * g⁻¹ = ((((groupPointsFunctor ℂ).map P.T.inclusion).app (CommAlgCat.of ℂ ℂ)) t :
        PointsIn i ℂ)

end LinearAlgebraicGroups.Specs.ComplexToralInvolutions
