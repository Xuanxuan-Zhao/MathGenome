import Mathlib.Algebra.Ring.Defs

/-!
Independent specification for K07.08.ring_definition, paper.tex:1160–1177.
The canonical structures are `Ring`, `CommRing` and `NonUnitalRing`.
No commutativity or nontriviality is required of a ring. The two predicates
below list exactly the multiplicative axioms in the source, on a fixed
abelian additive group; in particular they do not assume zero absorption.
The characterization statements require the resulting Mathlib structure
to retain the given additive group, multiplication and (when present) one.
The separate entries on domains, fields, ideals and homomorphisms use their
respective canonical objects; they add no hypotheses to this entry.
-/

universe u

namespace Specs.D07.Ch08.RingDefinition

structure NonUnitalRingLaws (R : Type u) [AddCommGroup R] [Mul R] : Prop where
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

structure UnitalRingLaws (R : Type u) [AddCommGroup R] [Mul R] [One R]
    : Prop extends NonUnitalRingLaws R where
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a

/-- The definition is equivalent to the canonical unital ring structure,
with all supplied operations retained. -/
def UnitalRingCharacterization : Prop :=
  ∀ (R : Type u) (g : AddCommGroup R) (m : Mul R) (o : One R),
    @UnitalRingLaws R g m o ↔
      ∃ s : Ring R, s.toAddCommGroup = g ∧ s.toMul = m ∧ s.toOne = o

/-- The explicitly nonunital convention has no identity assumption. -/
def NonUnitalRingCharacterization : Prop :=
  ∀ (R : Type u) (g : AddCommGroup R) (m : Mul R),
    @NonUnitalRingLaws R g m ↔
      ∃ s : NonUnitalRing R, s.toAddCommGroup = g ∧ s.toMul = m

/-- Commutativity is precisely the additional axiom for a commutative ring. -/
def CommutativeRingCharacterization : Prop :=
  ∀ (R : Type u) (s : Ring R),
    (∀ a b : R, a * b = b * a) ↔ ∃ c : CommRing R, c.toRing = s

-- These laws apply without a unit; hence they also apply to every unital ring.
def MulZero : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (a : R), a * 0 = 0

def ZeroMul : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (a : R), 0 * a = 0

def MulNeg : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (a b : R), a * (-b) = -(a * b)

def NegMul : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (a b : R), (-a) * b = -(a * b)

def NegMulNeg : Prop :=
  ∀ (R : Type u) [NonUnitalRing R] (a b : R), (-a) * (-b) = a * b

end Specs.D07.Ch08.RingDefinition
