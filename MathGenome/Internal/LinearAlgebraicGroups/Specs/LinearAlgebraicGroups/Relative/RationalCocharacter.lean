import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.RationalCocharacter

open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsMaximalTorus)
open RankOneFlag (SameSubgroup)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

/-- A parabolic over the ground field is a limit parabolic, with reductive
centralizer and geometric unipotent radical. The multiplicative decomposition,
its section and its limit map are those of the cocharacter. -/
def RationalParabolic : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∃ (c : Cocharacter G.val) (L : LimitDecomposition c),
      SameSubgroup P L.parabolic ∧
        IsReductive (closedSubgroupAlgebraicGroup L.centralizer) ∧ IsContractingRadical L

/-- The cocharacter can be taken in any maximal torus of the parabolic
defined over the ground field. -/
def RationalParabolicThroughTorus : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∀ T : ClosedSubgroup P.group, IsMaximalTorus T →
      ∃ (c : Cocharacter T.group)
        (L : LimitDecomposition (c ≫ (subgroupOfSubgroup P T).inclusion)),
        SameSubgroup P L.parabolic ∧
          IsReductive (closedSubgroupAlgebraicGroup L.centralizer) ∧ IsContractingRadical L

end LinearAlgebraicGroups.Specs.RationalCocharacter
