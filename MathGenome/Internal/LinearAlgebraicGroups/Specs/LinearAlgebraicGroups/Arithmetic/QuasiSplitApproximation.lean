import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration

universe u v

namespace LinearAlgebraicGroups.Specs.QuasiSplitApproximation

open Arithmetic Arithmetic.AdelicGroups Arithmetic.ApproximationOfLocalWords
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSemisimple)
open IntegralModels (MatrixRealization)
open QuasiSplitPinnedPairModel (BorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The two marked radicals, with their actual inclusions in the ambient group. -/
noncomputable def oppositeRadicals {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (M : BorelPair G) : ULift.{u} Bool → ClosedSubgroup G.val :=
  fun j => M.subgroup (if j.down then .positiveRadical else .negativeRadical)

/-- At every completion, the two radicals of the specified opposite rational
Borels generate the full group of completion points. -/
def GenerationAtCompletions : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (M : BorelPair G) (w : D.Place),
      generatedBySubgroups (oppositeRadicals M) D i w = ⊤

/-- Strong approximation for quasi-split semisimple simply connected groups
outside any finite nonempty set of places. -/
def StrongApproximationForQuasiSplitGroups : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    IsSemisimple G → GeometricallySimplyConnected G → IsQuasiSplit G →
      ∀ (S : Finset D.Place), S.Nonempty → StrongApproximation D i S

end LinearAlgebraicGroups.Specs.QuasiSplitApproximation
