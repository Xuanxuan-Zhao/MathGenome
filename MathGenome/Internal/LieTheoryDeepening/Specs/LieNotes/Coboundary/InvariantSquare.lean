import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.DualJacobi
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Schouten

/-! The invariant Schouten-square criterion of Proposition LD05. -/

namespace Specs.LieNotes.Coboundary

universe u v

def SchoutenEqNegCobracketDifferentialType : Prop :=
  ∀ {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g],
    ∀ r s : ⋀[k]^2 g,
      schoutenValue r s = -cobracketDifferentialValue (coboundaryValue r) s

def CobracketDifferentialCoboundaryType : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g],
    ∀ (r : ⋀[k]^2 g) (x : g),
      cobracketDifferentialValue (coboundaryValue r) (coboundaryValue r x) =
        -((1 / 2 : k) • exteriorAdjointValue 3 x (schoutenValue r r))

def CoboundaryIsLieBialgebraIffInvariantSquareType : Prop :=
  ∀ {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    [Module.Finite k g], ∀ r : ⋀[k]^2 g,
      isLieBialgebraCobracketValue (coboundaryValue r) ↔
        ∀ x : g, exteriorAdjointValue 3 x (schoutenValue r r) = 0

end Specs.LieNotes.Coboundary
