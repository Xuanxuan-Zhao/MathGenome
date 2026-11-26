import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitOppositeBorelUniqueness

open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open UnipotentRadicalIntersection (IsSchemeIntersection)

/-- An isomorphism of the ambient groups that identifies the positive Borels
and their tori identifies the opposite Borels by a unique isomorphism over
the ambient map. Both intersections are taken as subgroup schemes. -/
def OppositeUniqueness : Prop :=
  ∀ {k : Type u} [Field k] {G H : AffineAlgebraicGroup k},
    IsReductive G → IsReductive H →
    ∀ (T B C : ClosedSubgroup G.val) (T' B' C' : ClosedSubgroup H.val),
      IsSplitTorus T.group → IsSplitTorus T'.group →
      IsGeometricallyMaximal T → IsGeometricallyMaximal T' →
      IsKBorel B → IsKBorel C → IsKBorel B' → IsKBorel C' →
      IsSchemeIntersection {B, C} T → IsSchemeIntersection {B', C'} T' →
      ∀ (e : G.val ≅ H.val) (t : T.group ≅ T'.group) (b : B.group ≅ B'.group),
        T.inclusion ≫ e.hom = t.hom ≫ T'.inclusion →
        B.inclusion ≫ e.hom = b.hom ≫ B'.inclusion →
        ∃! c : C.group ≅ C'.group, C.inclusion ≫ e.hom = c.hom ≫ C'.inclusion

end LinearAlgebraicGroups.Specs.QuasiSplitOppositeBorelUniqueness
