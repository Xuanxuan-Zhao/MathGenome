import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.CAT0Spaces
import Mathlib.Topology.MetricSpace.ProperSpace

/-! The geometric-action assertion of Result E11 and its metric consequences. -/

namespace LinearAlgebraicGroups.Geometry.GeometricSemisimplicitySpec

open CAT0SpacesSpec

def properSpaceType :=
  ∀ {G X : Type*} [Group G] [MetricSpace X] [MulAction G X],
    isGeometricActionValue G X → cat0Value X → ProperSpace X

def completeSpaceType :=
  ∀ {G X : Type*} [Group G] [MetricSpace X] [MulAction G X],
    isGeometricActionValue G X → cat0Value X → CompleteSpace X

def isSemisimpleType :=
  ∀ {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]
    (h : isGeometricActionValue G X), cat0Value X → ∀ g : G,
      letI : IsIsometricSMul G X := h.1
      isSemisimpleValue (IsometryEquiv.constSMul g : X ≃ᵢ X)

end LinearAlgebraicGroups.Geometry.GeometricSemisimplicitySpec
