import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.Burnside
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.OrbitStabilizer

/-! Burnside's fixed-point formula, paper.tex, p204:W30. -/

namespace FiniteCombinatorics.Action

universe u v

/-- For every finite left action, the group order times the number of orbits
is the sum of the fixed-point counts. This includes the empty action set and
does not require a faithful action. -/
theorem burnside (G : Type u) (X : Type v) [Group G] [MulAction G X]
    [Finite G] [Finite X] :
    letI := Fintype.ofFinite G
    Nat.card G * Nat.card (Quotient (MulAction.orbitRel G X)) =
      ∑ g : G, Nat.card (fixedBy G X g) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel G X))
  simpa only [Nat.card_eq_fintype_card, fixedBy, Nat.mul_comm] using
    (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X).symm

end FiniteCombinatorics.Action
