import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry

/-! Euler's formula in W62 (paper.tex, lines 2374–2411).
Counts refer to the original finite simple graph and to actual connected
components of its sphere complement. Integer subtraction is untruncated.
Finiteness is a conclusion, including for the empty drawing. -/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Plane.Euler
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

def finite_facesType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G), Finite (Face D)

def euler_formulaType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G),
    (Nat.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (Nat.card (Face D) : ℤ) =
      1 + (Nat.card G.ConnectedComponent : ℤ)

/-- The exceptional empty realization has a connected complement with one face. -/
def empty_eulerType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] {G : SimpleGraph V} (D : Drawing G),
    ConnectedSpace (SphereComplement D) ∧ Nat.card (Face D) = 1 ∧
      Nat.card V = 0 ∧ Nat.card G.edgeSet = 0 ∧ Nat.card G.ConnectedComponent = 0

end Specs.FiniteCombinatorics.Graph.Plane.Euler
