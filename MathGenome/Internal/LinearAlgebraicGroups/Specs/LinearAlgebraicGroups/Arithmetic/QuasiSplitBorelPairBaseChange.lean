import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitBorelPairBaseChange

open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsTorus IsSplitTorus baseChangedSubgroup)
open RankOneFlag (IsGeometricallyMaximal)
open Unipotent (baseChangedAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)

/-- A specified opposite Borel pair and its common maximal torus after extension
to a field splitting the torus. The inclusions are the actual scalar extensions
of the three original inclusions. -/
def ExtendBorelPair : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (B C T : ClosedSubgroup G.val), IsKBorel B → IsKBorel C →
      IsTorus T.group → IsGeometricallyMaximal T → IsSchemeIntersection {B, C} T →
      IsSplitTorus ((groupBaseChange k K).obj T.group) →
      ∃ (hB : IsClosedImmersion ((groupBaseChange k K).map B.inclusion).hom.hom.left)
        (hC : IsClosedImmersion ((groupBaseChange k K).map C.inclusion).hom.hom.left)
        (hT : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left),
        let BK := baseChangedSubgroup K B hB
        let CK := baseChangedSubgroup K C hC
        let TK := baseChangedSubgroup K T hT
        IsReductive (baseChangedAlgebraicGroup K G) ∧
          IsKBorel BK ∧ IsKBorel CK ∧ IsGeometricallyMaximal TK ∧
          IsSchemeIntersection {BK, CK} TK

end LinearAlgebraicGroups.Specs.QuasiSplitBorelPairBaseChange
