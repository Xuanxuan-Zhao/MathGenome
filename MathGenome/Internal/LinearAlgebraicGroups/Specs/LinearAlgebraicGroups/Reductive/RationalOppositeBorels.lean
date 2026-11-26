import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag

open CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.RationalOppositeBorels

open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsMaximalTorus)
open RankOneFlag (IsGeometricallyMaximal)

/-- The common torus of two opposite rational Borels, with its two inclusions
exhibiting the scheme-theoretic intersection inside the ambient group. -/
def OppositeBorels {k : Type u} [Field k] {G : GroupScheme k}
    (B Bminus T : ClosedSubgroup G) : Prop :=
  IsKBorel B ∧ IsKBorel Bminus ∧ IsMaximalTorus T ∧ IsGeometricallyMaximal T ∧
    ∃ (i : T.group ⟶ B.group) (j : T.group ⟶ Bminus.group),
      i ≫ B.inclusion = T.inclusion ∧ j ≫ Bminus.inclusion = T.inclusion ∧
        IsPullback i.hom.hom j.hom.hom B.inclusion.hom.hom Bminus.inclusion.hom.hom

/-- A specified rational Borel of a connected reductive group in characteristic
zero admits an opposite rational Borel and a common maximal torus. -/
def RationalOppositeBorelsExist : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsReductive G → ∀ B : ClosedSubgroup G.val, IsKBorel B →
      ∃ Bminus T : ClosedSubgroup G.val, OppositeBorels B Bminus T

end LinearAlgebraicGroups.Specs.RationalOppositeBorels
