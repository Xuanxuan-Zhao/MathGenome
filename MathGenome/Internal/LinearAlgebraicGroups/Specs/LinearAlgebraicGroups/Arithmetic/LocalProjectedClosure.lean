import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.QuotientGroup.Basic

open CategoryTheory Opposite
open MeasureTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalProjectedClosure

open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LocalQuotientMixing (MixingCases)
open BorelProper (IsParabolic)
open Relative.MaximalSplitTori (IsMinimalParabolic)
open SchemeDerivedGroup (IsSubgroupOf)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
  (RationalPoints pointTopology)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
  (RightInvariant)

/-- The rational points of a maximal proper standard parabolic are maximal
as an abstract subgroup. Its core is the center, and left translation on
the original parabolic cosets descends to a faithful primitive action. -/
def MaximalParabolicCosetAction : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple J → MixingCases J →
    ∀ (B P : ClosedSubgroup J.val),
      IsMinimalParabolic J B → IsParabolic J P → IsSubgroupOf B P →
      ¬ IsIso P.inclusion →
      (∀ Q : ClosedSubgroup J.val, IsParabolic J Q → IsSubgroupOf P Q →
        IsSubgroupOf Q P ∨ IsIso Q.inclusion) →
      let G := RationalPoints J.val.X
      let P_F : Subgroup G :=
        SubgroupSections P ((testSpec F).obj (op (CommAlgCat.of F F)))
      let Z := Subgroup.center G
      IsCoatom P_F ∧ P_F.normalCore = Z ∧
        ∃ action : MulAction (G ⧸ Z) (G ⧸ P_F),
          letI := action
          (∀ (g : G) (x : G ⧸ P_F), (QuotientGroup.mk g : G ⧸ Z) • x = g • x) ∧
          FaithfulSMul (G ⧸ Z) (G ⧸ P_F) ∧
          MulAction.IsPreprimitive (G ⧸ Z) (G ⧸ P_F)

/-- Every noncentral rational point normally generates the local group
in the topology of its original affine model. -/
def LocalNormalClosure : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple J → MixingCases J →
    letI := pointTopology J.val.X
    ∀ g : RationalPoints J.val.X, g ∉ Subgroup.center (RationalPoints J.val.X) →
      closure (Subgroup.normalClosure ({g} : Set (RationalPoints J.val.X)) :
        Set (RationalPoints J.val.X)) = Set.univ

/-- A closed nondiscrete subgroup whose space of right cosets carries a
finite nonzero right-invariant measure is the full local group. -/
def FiniteCovolumeSubgroup : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple J → MixingCases J →
    letI := pointTopology J.val.X
    ∀ (H : Subgroup (RationalPoints J.val.X)),
      IsClosed (H : Set (RationalPoints J.val.X)) → ¬ DiscreteTopology H →
      ∀ (ν : Measure (_root_.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport.RightCosets H)) [IsFiniteMeasure ν],
        ν ≠ 0 → RightInvariant ν → H = ⊤

end LinearAlgebraicGroups.Specs.Arithmetic.LocalProjectedClosure
