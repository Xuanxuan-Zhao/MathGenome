import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.InvariantSquare
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model

/-! The two coboundary Lie bialgebras in Example LD06. -/

namespace Specs.LieNotes.Coboundary.SplitRankOne

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model H E F)

universe u

def BivectorType := ∀ (k : Type u) [Field k], ⋀[k]^2 (Model k)

def r₁Value (k : Type u) [Field k] : ⋀[k]^2 (Model k) :=
  wedge₂Value (F k) (E k)

def r₂Value (k : Type u) [Field k] : ⋀[k]^2 (Model k) :=
  wedge₂Value (H k) (E k)

def StandardCobracketType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let δ := coboundaryValue (r₁Value k)
    isLieBialgebraCobracketValue δ ∧
      δ (H k) = 0 ∧
      δ (E k) = wedge₂Value (H k) (E k) ∧
      δ (F k) = wedge₂Value (H k) (F k)

def TriangularCobracketType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let δ := coboundaryValue (r₂Value k)
    isLieBialgebraCobracketValue δ ∧
      schoutenValue (r₂Value k) (r₂Value k) = 0 ∧
      δ (H k) = (2 : k) • wedge₂Value (H k) (E k) ∧
      δ (E k) = 0 ∧
      δ (F k) = (-2 : k) • wedge₂Value (E k) (F k)

end Specs.LieNotes.Coboundary.SplitRankOne
