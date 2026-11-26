import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration

open AlgebraicGeometry CategoryTheory

universe u v

namespace LinearAlgebraicGroups.Specs.SplitApproximation

open Arithmetic Arithmetic.AdelicGroups
open AdjointRepresentation (GroupPoints)
open CharacterPairing (absoluteRoots)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open IntegralModels (MatrixRealization)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (IsRootSubgroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Over every extension field, the points of the root subgroups defined over the
ground field generate the points of a split simply connected semisimple group. -/
def RootGenerationOverExtensions : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    GeometricallySimplyConnected G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (F : Type u) [Field F] [Algebra k F],
      Subgroup.closure
        {g : GroupPoints G.val (CommAlgCat.of k F) |
          ∃ α ∈ absoluteRoots T, ∃ U : ClosedSubgroup G.val, IsRootSubgroup T U α ∧
            ∃ p : GroupPoints U.group (CommAlgCat.of k F), p ≫ U.inclusion.hom.hom = g} = ⊤

/-- Strong approximation for split simply connected semisimple groups over number
fields and global function fields, outside any finite nonempty set of places. -/
def SplitStrongApproximation : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    GeometricallySimplyConnected G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → StrongApproximation D i S

/-- Every completion of a positive-dimensional split semisimple group is
noncompact. This includes split absolutely almost simple groups. -/
def SplitLocalNoncompactness : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    0 < topologicalKrullDim G.val.X.left →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place),
      ¬ CompactSpace (LocalPoints D i w)

/-- The product of the omitted local factors is noncompact for every nonempty
set of omitted places in the positive-dimensional split semisimple case. -/
def SplitOmittedProductNoncompactness : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    0 < topologicalKrullDim G.val.X.left →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → ¬ CompactSpace (∀ w : (↑S : Set D.Place), LocalPoints D i w.1)

end LinearAlgebraicGroups.Specs.SplitApproximation
