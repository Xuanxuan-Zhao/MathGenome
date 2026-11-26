import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RealAlbertGroups

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage)
open LinearAlgebraicGroups.RootData (integralCartan)
open AbsoluteDynkinTypes (HasDynkinType)
open Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints)
open CharacterDescent (Cocharacter)
open GeometricRadicals (GeometricGroup IsSemisimple)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum SplitBorelPair)

/-- A connected semisimple group whose actual absolute Cartan matrix has
type `F₄`. The Borel pair and the attached datum are taken on the base change
of the given group to an algebraic closure. -/
def HasAbsoluteTypeF4 {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  IsSemisimple G ∧
    ∃ (P : SplitBorelPair (AlgebraicClosure k)) (_ : P.G = GeometricGroup G)
      (D : AttachedDatum P),
      letI := D.comm
      HasDynkinType (integralCartan D.datum.rootDatum D.base) .F4

/-- The real points of every real form of type `F₄` are connected in their
usual topology. This includes the compact form. -/
def RealPointsConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    HasAbsoluteTypeF4 G → ConnectedSpace (PointsIn i ℝ)

/-- A noncompact real form has a nontrivial real cocharacter with a nonzero
contracting Lie direction. Its contracting radical and all its real conjugates
generate a dense subgroup. The rational parabolic radicals together also
generate a dense subgroup. -/
def NoncompactRealParabolicGeneration : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    HasAbsoluteTypeF4 G → ¬ CompactSpace (PointsIn i ℝ) →
    (∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      let U : Subgroup (PointsIn i ℝ) :=
        ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
          (CommAlgCat.of ℝ ℝ)).hom).range
      c.hom.hom ≠ 1 ∧ BorelProper.IsParabolic G D.parabolic ∧
      StandardParabolicLevi.IsContractingRadical D ∧
      (∃ v : Lie ℝ G.val, v ∈ lieImage D.contracting ∧ v ≠ 0) ∧
      Dense (Subgroup.normalClosure (U : Set (PointsIn i ℝ)) : Set (PointsIn i ℝ))) ∧
    Dense (Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :
      Set (PointsIn i ℝ))

end LinearAlgebraicGroups.Specs.RealAlbertGroups
