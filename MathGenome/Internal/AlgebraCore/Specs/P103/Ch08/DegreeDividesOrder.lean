import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The order divisibility assertion of Theorem 8.12 (paper.tex 1685–1689).
The shared irreducibility convention includes nonzeroness. For a finite group,
finite dimensionality follows from irreducibility, so it is not an extra hypothesis. -/

universe u v

namespace P103.Ch08.DegreeDividesOrderSpecs

def degree_divides_orderType : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ → Module.finrank ℂ V ∣ Nat.card G

end P103.Ch08.DegreeDividesOrderSpecs
