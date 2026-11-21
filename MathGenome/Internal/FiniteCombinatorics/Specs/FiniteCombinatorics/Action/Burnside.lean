import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.OrbitStabilizer
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.EquivFin

/-! Independent specification of paper.tex, p204:W30 (Burnside's formula).
The quotient is by the canonical orbit relation of the given left action.
No faithfulness or nonemptiness hypothesis is imposed. -/

namespace Specs.FiniteCombinatorics.Action.Burnside

universe u v

/-- The natural counting identity, choosing an enumeration only to write the
finite sum. Fixed points are specified directly by their defining equation. -/
noncomputable def burnsideType : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] [Finite X],
    letI := Fintype.ofFinite G
    Nat.card G * Nat.card (Quotient (MulAction.orbitRel G X)) =
      ∑ g : G, Nat.card {x : X // g • x = x}

end Specs.FiniteCombinatorics.Action.Burnside
