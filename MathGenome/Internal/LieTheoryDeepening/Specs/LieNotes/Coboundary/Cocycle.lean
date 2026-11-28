import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Basic

/-! The adjoint representation identity and the coboundary cocycle assertion of LD04. -/

namespace Specs.LieNotes.Coboundary

universe u v

def ExteriorAdjointWedgeTwoLieType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ (x y : g) (r : ⋀[k]^2 g),
      exteriorAdjointValue 2 ⁅x, y⁆ r =
        exteriorAdjointValue 2 x (exteriorAdjointValue 2 y r) -
          exteriorAdjointValue 2 y (exteriorAdjointValue 2 x r)

def CoboundaryIsCocycleType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ r : ⋀[k]^2 g, isCobracketCocycleValue (coboundaryValue r)

end Specs.LieNotes.Coboundary
