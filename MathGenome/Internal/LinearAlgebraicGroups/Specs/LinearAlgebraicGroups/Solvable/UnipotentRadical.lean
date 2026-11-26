import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.RingTheory.KrullDimension.Basic

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.SolvableRadical

open GeometricRadicals (IsSmoothConnectedNormal IsTorus IsUnipotentRadical)
open SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Unipotent (IsUnipotent closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup
  IsFppfGroupQuotient)

/-- The smooth connected normal unipotent subgroup containing all closed unipotent
subgroup schemes, including the ones that are not smooth or connected. -/
def IsSolvableUnipotentRadical {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val) : Prop :=
  IsSmoothConnectedNormal U ∧ IsUnipotent (closedSubgroupAlgebraicGroup U) ∧
    ∀ V : ClosedSubgroup G.val, IsUnipotent (closedSubgroupAlgebraicGroup V) →
      IsSubgroupOf V U

def SolvableUnipotentRadicalExists : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsSolvable G.val →
    ∃ (U : ClosedSubgroup G.val) (T : AffineAlgebraicGroup k) (q : G.val ⟶ T.val),
      IsSolvableUnipotentRadical G U ∧ IsTorus T.val ∧ IsFppfGroupQuotient U q

def SolvableUnipotentRadicalUnique : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) {U V : ClosedSubgroup G.val},
    IsSolvableUnipotentRadical G U → IsSolvableUnipotentRadical G V →
    ∃! e : U.group ≅ V.group, e.hom ≫ V.inclusion = U.inclusion

def SolvableUnipotentRadicalBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G T : AffineAlgebraicGroup k) (U : ClosedSubgroup G.val) (q : G.val ⟶ T.val),
    IsSmoothConnectedNormal U → IsUnipotent (closedSubgroupAlgebraicGroup U) →
    IsTorus T.val → IsFppfGroupQuotient U q →
    ∃ (h : IsClosedImmersion ((groupBaseChange k K).map U.inclusion).hom.hom.left),
      let U' := GeometricRadicals.baseChangedSubgroup K U h
      IsSolvableUnipotentRadical (baseChangedAlgebraicGroup K G) U' ∧
      IsTorus (baseChangedAlgebraicGroup K T).val ∧
      IsFppfGroupQuotient (G := baseChangedAlgebraicGroup K G)
        (Q := baseChangedAlgebraicGroup K T) U' ((groupBaseChange k K).map q)

def MaximalUnipotentSubgroupIsLargest : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (U : ClosedSubgroup G.val), IsSmoothConnectedNormal U →
    IsUnipotent (closedSubgroupAlgebraicGroup U) →
    (∀ V : ClosedSubgroup G.val, IsSmoothConnectedNormal V →
      IsUnipotent (closedSubgroupAlgebraicGroup V) →
      ringKrullDim (coordinates V.group.X) ≤ ringKrullDim (coordinates U.group.X)) →
    IsUnipotentRadical G U

def LargestSmoothConnectedNormalUnipotentExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    ∃ U : ClosedSubgroup G.val, IsUnipotentRadical G U

end LinearAlgebraicGroups.Specs.SolvableRadical
