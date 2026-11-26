import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import Mathlib.NumberTheory.LocalField.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMinimalParabolicDynamics

open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
  (RationalPoints pointTopology)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Relative.RelativeChambers (IsRegular)
open RelativeRayGeneration (unipotentGenerated)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

/-- Dense generation by parabolic radicals in a nontrivial local point group
gives a regular cocharacter defining a proper minimal rational parabolic. -/
def ExistsProperMinimalParabolic : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsReductive J →
    (∃ g : RationalPoints J.val.X, g ≠ 1) →
    (letI := pointTopology J.val.X
     Dense {g : RationalPoints J.val.X |
       ∃ x ∈ unipotentGenerated J,
         toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ x = g}) →
    ∃ (S : ClosedSubgroup J.val) (c : Cocharacter S.group)
      (D : LimitDecomposition (c ≫ S.inclusion)),
      IsMaximalSplitTorus S ∧ IsRegular S c ∧ IsMinimalParabolic J D.parabolic ∧
        ¬ IsIso D.parabolic.inclusion ∧
        ∃ (X : SchemeOver F) (x : X ⟶ J.val.X), ¬ Centralizes (c ≫ S.inclusion) x

/-- A normal subgroup contained in the rational points of the indicated minimal
parabolic centralizes its defining cocharacter scheme-theoretically. -/
def NormalSubgroupCentralizesCocharacter : Prop :=
  ∀ {F : Type u} [Field F] (J : AffineAlgebraicGroup F), IsReductive J →
    ∀ (S : ClosedSubgroup J.val) (c : Cocharacter S.group)
      (D : LimitDecomposition (c ≫ S.inclusion)),
      IsMaximalSplitTorus S → IsRegular S c → IsMinimalParabolic J D.parabolic →
      ¬ IsIso D.parabolic.inclusion →
      (∃ (X : SchemeOver F) (x : X ⟶ J.val.X), ¬ Centralizes (c ≫ S.inclusion) x) →
      ∀ (N : Subgroup (RationalPoints J.val.X)) [N.Normal],
        N ≤ SubgroupSections D.parabolic ((testSpec F).obj (op (CommAlgCat.of F F))) →
        ∀ x ∈ N, Centralizes (c ≫ S.inclusion) x

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMinimalParabolicDynamics
