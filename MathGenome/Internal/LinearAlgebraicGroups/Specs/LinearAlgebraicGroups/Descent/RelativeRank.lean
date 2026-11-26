import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.NormOneTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RelativeRank

open AdjointCocharacters (IsAdjointQuotient)
open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsSemisimple
  IsSplitReductive IsSplitTorus)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

noncomputable section

variable {k : Type u} [Field k]

/-- The relative rank is the supremum of the dimensions of the closed split tori. -/
def relativeRank (G : AffineAlgebraicGroup k) : WithBot ℕ∞ :=
  ⨆ S : {S : ClosedSubgroup G.val // IsSplitTorus S.group},
    topologicalKrullDim S.val.group.X.left

/-- The geometric rank is the rank after extension to an algebraic closure. -/
def geometricRank (G : AffineAlgebraicGroup k) : WithBot ℕ∞ :=
  relativeRank (GeometricGroup G)

def RelativeRankType := ∀ {k : Type u} [Field k], AffineAlgebraicGroup k → WithBot ℕ∞

/-- Properness refers to the inclusion as a closed subgroup scheme. -/
def HasProperParabolic (G : AffineAlgebraicGroup k) : Prop :=
  ∃ P : ClosedSubgroup G.val, IsParabolic G P ∧ ¬ IsIso P.inclusion

/-- Centrality of a cocharacter is tested on all scheme families. -/
def IsCentralCocharacter {G : GroupScheme k} (c : Cocharacter G) : Prop :=
  ∀ (X : SchemeOver k) (x : X ⟶ G.X), Centralizes c x

/-- The rank is attained and is the dimension of every maximal split torus. -/
def MaximalSplitDimension : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    (∃ S : ClosedSubgroup G.val, IsMaximalSplitTorus S) ∧
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
      topologicalKrullDim S.group.X.left = relativeRank G

/-- Over the algebraic closure, the rank is the dimension of each maximal torus. -/
def MaximalGeometricDimension : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    (∃ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T) ∧
    ∀ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T →
      topologicalKrullDim T.group.X.left = geometricRank G

def RankComparison : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    relativeRank G ≤ geometricRank G ∧
    (IsSplitReductive G → relativeRank G = geometricRank G)

def ProperDynamicParabolic : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (c : Cocharacter G.val) (D : LimitDecomposition c),
      IsParabolic G D.parabolic ∧ (¬ IsIso D.parabolic.inclusion ↔ ¬ IsCentralCocharacter c)

def AdjointParabolicCriterion : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k} (Z : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val), IsReductive G → IsAdjointQuotient Z q →
      (HasProperParabolic G ↔ 0 < relativeRank Q)

def SemisimpleParabolicCriterion : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    (HasProperParabolic G ↔ 0 < relativeRank G)

/-- The actual scheme kernel of the quadratic norm has ranks zero and one. -/
def QuadraticNormOneRanks : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K]
    (W H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj W.val ≅ WeilRestriction.extendedUnits k K)
    (n : W.val ⟶ H.val) (T : NormOneTorus.KernelModel e n),
    letI := T.finiteType
    let S := StandardGroups.spectrum k T.coordinate
    relativeRank S = 0 ∧ geometricRank S = 1

end

end LinearAlgebraicGroups.Specs.RelativeRank
