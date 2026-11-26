import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterWallGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalRealCompletionTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

noncomputable section

set_option autoImplicit false

open LieAlgebrasAndRepresentations (FiniteDynkinType)

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRealPoints

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn StrongApproximation)
open LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection (FinitePoints)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition lieImage)
open Arithmetic.OppositeRadicals (IsNoncentral)
open Arithmetic.ProjectiveRecurrence (parabolicRadicalPoints)
open CharacterDescent (Cocharacter)
open ExceptionalCompactInner (HasExceptionalType)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSplitReductive)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- The E₆ fold and the outer compact calculation on the actual marked torus.
The torus, Weyl labels, affine walls and compact root maps in the outer case
all use the same simple-coroot exponential. -/
def OuterCompactStatement : Prop :=
  ExceptionalFoldedWeyl.FoldedRootCalculation ∧
  ExceptionalFoldedWeyl.FoldedWeylCalculation ∧
  ExceptionalOuterWallGroups.OuterWallCalculation

/-- Connectedness in the usual topology for all simply connected real forms
of the three exceptional types, including the compact forms. -/
def RealPointsConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ConnectedSpace (PointsIn i ℝ)

/-- A noncompact real form has a noncentral cocharacter with a nonzero
contracting Lie direction, and the rational parabolic radicals generate densely. -/
def NoncompactRealParabolicGeneration : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ¬ CompactSpace (PointsIn i ℝ) →
    (∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
      let U : Subgroup (PointsIn i ℝ) :=
        ((((groupPointsFunctor ℝ).map D.contracting.inclusion).app
          (CommAlgCat.of ℝ ℝ)).hom).range
      IsNoncentral c ∧ BorelProper.IsParabolic G D.parabolic ∧
      StandardParabolicLevi.IsContractingRadical D ∧
      (∃ v : Lie ℝ G.val, v ∈ lieImage D.contracting ∧ v ≠ 0) ∧
      Dense (Subgroup.normalClosure (U : Set (PointsIn i ℝ)) : Set (PointsIn i ℝ))) ∧
    Dense (Subgroup.closure (G := PointsIn i ℝ) (parabolicRadicalPoints G) :
      Set (PointsIn i ℝ))

/-- The type of the group's attached datum after geometric scalar extension. -/
def HasAbsoluteExceptionalType {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  ∃ t : FiniteDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) ∧
    ExceptionalRealCompletionTransport.HasAbsoluteType G t

def ComplexCompletionsSplit : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasAbsoluteExceptionalType G →
    ∀ (w : NumberField.InfinitePlace K), w.IsComplex →
      IsSplitReductive (baseChangedAlgebraicGroup w.Completion G)

/-- Conditional number-field application, for both global isotropy cases.
All places outside S enter the adelic topology, including compact real places. -/
def StrongApproximationStatement : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (D : GlobalFieldData.{u, u} K),
    D = .number inferInstance →
    ∀ (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasAbsoluteExceptionalType G →
      (∀ w : D.FinitePlace, IsQuasiSplit (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)) →
      ∀ (S : Finset D.Place), S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
      StrongApproximation D i S

end LinearAlgebraicGroups.Specs.ExceptionalRealPoints
