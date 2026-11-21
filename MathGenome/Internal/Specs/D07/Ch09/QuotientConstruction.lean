import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
Independent specifications for K07.09.quotient_construction,
paper.tex:1516–1533. Rings are associative and unital; neither
commutativity nor nontriviality nor properness of the ideal is assumed.

The quotient is Mathlib's canonical ideal quotient. Its underlying type
and additive group are the additive-subgroup quotient. The explicit
set-valued cosets and equality bridge below identify its elements with
the source's additive cosets. For an arbitrary additive subgroup, the
last statement characterizes precisely when the product rule descends;
it assumes neither a ring structure on the quotient nor absorption.
-/

universe u

namespace Specs.D07.Ch09.QuotientConstruction

open Specs.D07.Ch08.IdealDefinition

/-- The actual additive coset `a + H = {a + h | h ∈ H}`. -/
def additiveCoset {R : Type u} [Ring R] (H : AddSubgroup R) (a : R) : Set R :=
  (fun h => a + h) '' (H : Set R)

def AdditiveCosetEqIffSubMem : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R) (a b : R),
    additiveCoset H a = additiveCoset H b ↔ a - b ∈ H

/-- Equality in the canonical ring quotient is equality of additive cosets. -/
def QuotientEqIffCosetEq : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided] (a b : R),
    Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔
      additiveCoset I.toAddSubgroup a = additiveCoset I.toAddSubgroup b

/-- The ring structure uses exactly the additive quotient, with its original
abelian additive group, and the canonical quotient multiplication and one. -/
def RingConstruction : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    ∃ s : Ring (R ⧸ I),
      s.toAddCommGroup =
        (inferInstance : AddCommGroup (R ⧸ I.toAddSubgroup)) ∧
      s.toMul = (inferInstance : Mul (R ⧸ I)) ∧
      s.toOne = (inferInstance : One (R ⧸ I))

/-- All operation rules on representatives, including zero and negatives. -/
def QuotientOperations : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    (∀ a b : R, Ideal.Quotient.mk I a + Ideal.Quotient.mk I b =
      Ideal.Quotient.mk I (a + b)) ∧
    (∀ a b : R, Ideal.Quotient.mk I a * Ideal.Quotient.mk I b =
      Ideal.Quotient.mk I (a * b)) ∧
    Ideal.Quotient.mk I 1 = 1 ∧ Ideal.Quotient.mk I 0 = 0 ∧
    (∀ a : R, -(Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (-a))

/-- The source's associativity, distributivity and identity axioms hold
for the canonical quotient operations. -/
def QuotientRingLaws : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    Specs.D07.Ch08.RingDefinition.UnitalRingLaws (R ⧸ I)

/-- Addition is independent of both representatives for every additive subgroup. -/
def AdditionIndependent : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R) (a a' b b' : R),
    additiveCoset H a = additiveCoset H a' →
    additiveCoset H b = additiveCoset H b' →
    additiveCoset H (a + b) = additiveCoset H (a' + b')

/-- Independence of representatives in `[a][b] = [ab]` is equivalent
to both ambient absorption conditions on the given additive subgroup. -/
def MultiplicationIndependentIffTwoSided : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R),
    (∀ a a' b b' : R,
      additiveCoset H a = additiveCoset H a' →
      additiveCoset H b = additiveCoset H b' →
      additiveCoset H (a * b) = additiveCoset H (a' * b')) ↔
    IsTwoSidedIdeal H

end Specs.D07.Ch09.QuotientConstruction
