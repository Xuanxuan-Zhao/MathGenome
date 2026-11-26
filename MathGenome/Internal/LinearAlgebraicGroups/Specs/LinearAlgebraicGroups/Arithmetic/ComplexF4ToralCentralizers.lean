import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.Analysis.Complex.Basic

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.ComplexF4ToralCentralizers

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open AbsoluteDynkinTypes (HasDynkinType)
open GeometricRadicals (IsSemisimple)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum SplitBorelPair)
open LinearAlgebraicGroups.RootData (integralCartan)

/-- The centralizer of any square-one point of the specified torus is
connected in the matrix topology on complex points. -/
def ToralCentralizerConnected : Prop :=
  ∀ (P : SplitBorelPair ℂ) (D : AttachedDatum P),
    IsSemisimple P.G →
    (letI := D.comm; HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4) →
    ∀ (i : MatrixRealization P.G)
      (t : ((groupPointsFunctor ℂ).obj P.T.group).obj (CommAlgCat.of ℂ ℂ)),
      t ^ 2 = 1 →
      let tG : PointsIn i ℂ :=
        (((groupPointsFunctor ℂ).map P.T.inclusion).app (CommAlgCat.of ℂ ℂ)).hom t
      ConnectedSpace {g : PointsIn i ℂ // Commute g tG}

end LinearAlgebraicGroups.Specs.ComplexF4ToralCentralizers
