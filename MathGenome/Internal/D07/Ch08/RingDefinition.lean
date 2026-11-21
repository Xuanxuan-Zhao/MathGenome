import MathGenome.Internal.Specs.D07.Ch08.RingDefinition

/-!
# Associative unital rings

K07.08.ring_definition (paper.tex:1160–1177). We use Mathlib's `Ring`,
`CommRing` and `NonUnitalRing`. The characterization theorems below verify
that these structures express exactly the source's axioms on the supplied
additive group and operations. Zero absorption is derived from distributivity
and additive cancellation when constructing these structures. In particular,
there is no hypothesis `Nontrivial R` or commutativity of multiplication.
-/

universe u

namespace D07.Ch08.RingDefinition

open Specs.D07.Ch08.RingDefinition

private theorem mul_zero_from_distributivity {R : Type u}
    [AddCommGroup R] [Mul R] (h : NonUnitalRingLaws R) (a : R) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  calc
    a * 0 + a * 0 = a * (0 + 0) := (h.left_distrib a 0 0).symm
    _ = a * 0 + 0 := by rw [add_zero, add_zero]

private theorem zero_mul_from_distributivity {R : Type u}
    [AddCommGroup R] [Mul R] (h : NonUnitalRingLaws R) (a : R) : 0 * a = 0 := by
  apply add_left_cancel (a := 0 * a)
  calc
    0 * a + 0 * a = (0 + 0) * a := (h.right_distrib 0 0 a).symm
    _ = 0 * a + 0 := by rw [add_zero, add_zero]

/-- The abelian-group, associativity, identity and distributivity axioms
are exactly the data required for the usual canonical ring structure. -/
theorem unitalRingCharacterization : UnitalRingCharacterization.{u} := by
  intro R g m o
  constructor
  · intro h
    refine ⟨{ g, m, o with
      mul_assoc := h.mul_assoc
      one_mul := h.one_mul
      mul_one := h.mul_one
      left_distrib := h.left_distrib
      right_distrib := h.right_distrib
      mul_zero := mul_zero_from_distributivity h.toNonUnitalRingLaws
      zero_mul := zero_mul_from_distributivity h.toNonUnitalRingLaws }, rfl, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl, rfl⟩
    let : Ring R := s
    exact {
      mul_assoc := _root_.mul_assoc
      one_mul := _root_.one_mul
      mul_one := _root_.mul_one
      left_distrib := _root_.left_distrib
      right_distrib := _root_.right_distrib }

/-- Dropping the identity axiom gives exactly an associative nonunital ring. -/
theorem nonUnitalRingCharacterization : NonUnitalRingCharacterization.{u} := by
  intro R g m
  constructor
  · intro h
    refine ⟨{ g, m with
      mul_assoc := h.mul_assoc
      left_distrib := h.left_distrib
      right_distrib := h.right_distrib
      mul_zero := mul_zero_from_distributivity h
      zero_mul := zero_mul_from_distributivity h }, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl⟩
    let : NonUnitalRing R := s
    exact {
      mul_assoc := _root_.mul_assoc
      left_distrib := _root_.left_distrib
      right_distrib := _root_.right_distrib }

/-- A commutative ring is a ring with commuting multiplication. -/
theorem commutativeRingCharacterization : CommutativeRingCharacterization.{u} := by
  intro R s
  constructor
  · intro h
    exact ⟨{ s with mul_comm := h }, rfl⟩
  · rintro ⟨c, rfl⟩
    let : CommRing R := c
    exact _root_.mul_comm

/-- Distributivity and additive cancellation imply right zero absorption. -/
theorem mulZero : MulZero.{u} := by
  intro R _ a
  exact MulZeroClass.mul_zero a

/-- Distributivity and additive cancellation imply left zero absorption. -/
theorem zeroMul : ZeroMul.{u} := by
  intro R _ a
  exact MulZeroClass.zero_mul a

/-- Multiplication preserves additive inverses in its second argument. -/
theorem mulNeg : MulNeg.{u} := by
  intro R _ a b
  exact _root_.mul_neg a b

/-- Multiplication preserves additive inverses in its first argument. -/
theorem negMul : NegMul.{u} := by
  intro R _ a b
  exact _root_.neg_mul a b

/-- Two negative factors have the same product as their positive counterparts. -/
theorem negMulNeg : NegMulNeg.{u} := by
  intro R _ a b
  exact _root_.neg_mul_neg a b

end D07.Ch08.RingDefinition
