import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CocharacterLieWeights
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Relative.ReductiveLieCentralizers

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (adjointWeightVectors)
open GeometricBorelConjugacy (IsReducedIdentityComponent)
open GeometricRadicals (IsMaximalTorus IsReductive)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage)
open RootGroups (IsRootSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open SemisimpleLieCentralizer (GeometricallySemisimple)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k]

/-- The nontrivial adjoint weights occurring in the image of the Lie algebra of H.
When T is contained in H, these are the roots of H relative to T. -/
def subgroupRoots {G : GroupScheme k} (T H : ClosedSubgroup G) : Set (Character T.group) :=
  {α | α ≠ 1 ∧ ∃ v ∈ adjointWeightVectors T α, v ∈ lieImage H ∧ v ≠ 0}

/-- A smooth connected subgroup of maximal rank is reductive if its Lie roots
are symmetric and the corresponding ambient root groups are contained in it. -/
def ReductiveOfSymmetricRoots : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ H : ClosedSubgroup G.val, Smooth H.group.X.hom → GeometricallyConnected H.group.X.hom →
    ∀ T : ClosedSubgroup G.val, IsMaximalTorus T → IsSubgroupOf T H →
      (∀ α ∈ subgroupRoots T H, α⁻¹ ∈ subgroupRoots T H) →
      (∀ α ∈ subgroupRoots T H, ∀ U : ClosedSubgroup G.val,
        IsRootSubgroup T U α → IsSubgroupOf U H) →
      IsReductive (closedSubgroupAlgebraicGroup H)

/-- The subgroup represents the matrix commutation equation over every
commutative test algebra. -/
def IsMatrixCentralizer {G L : GroupScheme k} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    (f : G ⟶ L) (Y : Matrix ι ι k) (C : ClosedSubgroup G) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints G R),
    (∃ c : GroupPoints C.group R, ((groupPointsFunctor k).map C.inclusion).app R c = g) ↔
      Commute (l.hom.app R (((groupPointsFunctor k).map f).app R g)).val
        (Y.map (algebraMap k R))

/-- The smooth identity component of the scheme centralizer of a
matrix-semisimple Lie element in a connected reductive group is reductive. -/
def SemisimpleLieCentralizerComponentReductive : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (L : AffineGroupCategory k)
      (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
      (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    ∀ y : Lie k G.val,
      let Y := InfinitesimalCommutator.matrixDifferential f l y
      GeometricallySemisimple Y →
        ∃ C : ClosedSubgroup G.val, IsMatrixCentralizer l f Y C ∧ Smooth C.group.X.hom ∧
          ∃ H : ClosedSubgroup C.group, IsReducedIdentityComponent H ∧
            IsOpenImmersion H.inclusion.hom.hom.left ∧
            IsReductive (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) H)

end LinearAlgebraicGroups.Specs.Relative.ReductiveLieCentralizers
