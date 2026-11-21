import MathGenome.Internal.D07.Ch05.OrbitStabilizerCounting
import MathGenome.Internal.Specs.D07.Ch05.Burnside
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Burnside's orbit-counting theorem

`K07.05.burnside`, paper.tex:911–924. Mathlib's fixed-point counting
theorem counts the same orbit quotient and the subtype `g • x = x`.
Its finite-type instances are obtained here from exactly the source's
finiteness assumptions, including when the acted-on type is empty.
-/

namespace D07.Ch05.Burnside

universe u v

theorem counting_identity (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite G] [Finite X] :
    letI := Fintype.ofFinite G
    Nat.card G * Nat.card (MulAction.orbitRel.Quotient G X) =
      ∑ g : G, Nat.card {x : X // g • x = x} := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  calc
    Nat.card G * Nat.card (MulAction.orbitRel.Quotient G X) =
        ∑ g : G, Fintype.card (MulAction.fixedBy X g) := by
      simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using
        (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X).symm
    _ = ∑ g : G, Nat.card {x : X // g • x = x} := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.card_eq_nat_card

theorem group_order_positive (G : Type u) [Group G] [Finite G] :
    0 < Nat.card G := Nat.card_pos

theorem group_order_divides_fixed_point_sum (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite G] [Finite X] :
    letI := Fintype.ofFinite G
    Nat.card G ∣ ∑ g : G, Nat.card {x : X // g • x = x} := by
  let := Fintype.ofFinite G
  exact ⟨Nat.card (MulAction.orbitRel.Quotient G X), counting_identity G X |>.symm⟩

theorem orbit_count_eq_div (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite G] [Finite X] :
    letI := Fintype.ofFinite G
    Nat.card (MulAction.orbitRel.Quotient G X) =
      (∑ g : G, Nat.card {x : X // g • x = x}) / Nat.card G := by
  let := Fintype.ofFinite G
  rw [← counting_identity G X, Nat.mul_div_cancel_left _ (group_order_positive G)]

end D07.Ch05.Burnside
