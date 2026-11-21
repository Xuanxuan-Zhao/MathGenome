import MathGenome.Internal.Specs.D07.Ch08.Subring
import MathGenome.Internal.Specs.D07.Ch09.FirstIsomorphism
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
Independent specifications for K07.09.second_isomorphism, paper.tex:1583–1597.
The ambient ring need not be commutative or nontrivial. Ideals are two-sided.
The sum is defined as the inverse image of the image of A under R → R/I;
`SumCarrier` identifies it with the literal set of sums in the source.
Intersections and restrictions are inverse images along the actual inclusions.
For a nonunital subring, congruence quotients retain the inherited nonunital
ring operations; `NonUnitalQuotientRelation` identifies their additive cosets.
-/

universe u

namespace Specs.D07.Ch09.SecondIsomorphism

variable {R : Type u} [Ring R]

/-- The saturation of A under reduction modulo I. -/
def sumSubring (A : Subring R) (I : Ideal R) [I.IsTwoSided] : Subring R :=
  (A.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I)

/-- The ideal A ∩ I, considered in A (and similarly for A + I). -/
def intersectionIdeal (A : Subring R) (I : Ideal R) : Ideal A :=
  I.comap A.subtype

instance (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    (intersectionIdeal A I).IsTwoSided :=
  inferInstanceAs (I.comap A.subtype).IsTwoSided

/-- Inclusion A → A + I, with the ambient element unchanged. -/
def sumInclusion (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    A →+* sumSubring A I where
  toFun a := ⟨a, ⟨a, a.property, rfl⟩⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The source's map a ↦ [a], with I restricted to A + I. -/
def restriction (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    A →+* (sumSubring A I ⧸ intersectionIdeal (sumSubring A I) I) :=
  (Ideal.Quotient.mk _).comp (sumInclusion A I)

def SumCarrier : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided] (x : R),
    x ∈ sumSubring A I ↔ ∃ a ∈ A, ∃ i ∈ I, x = a + i

/-- In particular every element of I really lies in the right-hand ambient ring. -/
def SumInclusions : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided],
    (∀ a ∈ A, a ∈ sumSubring A I) ∧ (∀ i ∈ I, i ∈ sumSubring A I)

def IntersectionIdealProperties : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided],
    (intersectionIdeal A I).IsTwoSided ∧
      (∀ a : A, a ∈ intersectionIdeal A I ↔ (a : R) ∈ I)

def RestrictionSurjective : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided],
    Function.Surjective (restriction A I)

def RestrictionKernel : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided],
    RingHom.ker (restriction A I) = intersectionIdeal A I

def SecondIsomorphism : Prop :=
  ∀ (R : Type u) [Ring R] (A : Subring R) (I : Ideal R) [I.IsTwoSided],
    ∃ e : (A ⧸ intersectionIdeal A I) ≃+*
        (sumSubring A I ⧸ intersectionIdeal (sumSubring A I) I),
      ∀ a : A, e (Ideal.Quotient.mk _ a) = restriction A I a

/-- The same saturation without imposing membership of the ambient identity. -/
def sumNonUnitalSubring (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided] :
    NonUnitalSubring R :=
  (A.map (Ideal.Quotient.mk I).toNonUnitalRingHom).comap
    (Ideal.Quotient.mk I).toNonUnitalRingHom

/-- The additive subgroup A ∩ I; absorption in A is a theorem below. -/
def nonUnitalIntersection (A : NonUnitalSubring R) (I : Ideal R) : AddSubgroup A :=
  I.toAddSubgroup.comap (NonUnitalSubringClass.subtype A).toAddMonoidHom

/-- Equality modulo the intersection, with multiplication inherited from A. -/
def nonUnitalCongruence (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided] :
    RingCon A :=
  (Ideal.Quotient.ringCon I).comap (NonUnitalSubringClass.subtype A)

def nonUnitalSumInclusion (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided] :
    A →ₙ+* sumNonUnitalSubring A I where
  toFun a := ⟨a, ⟨a, a.property, rfl⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def nonUnitalRestriction (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided] :
    A →ₙ+* (nonUnitalCongruence (sumNonUnitalSubring A I) I).Quotient where
  toFun a := RingCon.toQuotient (nonUnitalSumInclusion A I a)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def NonUnitalSumCarrier : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided]
    (x : R), x ∈ sumNonUnitalSubring A I ↔ ∃ a ∈ A, ∃ i ∈ I, x = a + i

def NonUnitalSumInclusions : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided],
    (∀ a ∈ A, a ∈ sumNonUnitalSubring A I) ∧
      (∀ i ∈ I, i ∈ sumNonUnitalSubring A I)

def NonUnitalIntersectionProperties : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided],
    (∀ a : A, a ∈ nonUnitalIntersection A I ↔ (a : R) ∈ I) ∧
    (∀ (a b : A), b ∈ nonUnitalIntersection A I →
      a * b ∈ nonUnitalIntersection A I ∧ b * a ∈ nonUnitalIntersection A I)

def NonUnitalQuotientRelation : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided]
    (a b : A),
    (RingCon.toQuotient a : (nonUnitalCongruence A I).Quotient) =
      RingCon.toQuotient b ↔ a - b ∈ nonUnitalIntersection A I

def NonUnitalRestrictionSurjective : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided],
    Function.Surjective (nonUnitalRestriction A I)

def NonUnitalRestrictionKernel : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided]
    (a : A), nonUnitalRestriction A I a = 0 ↔ a ∈ nonUnitalIntersection A I

def NonUnitalSecondIsomorphism : Prop :=
  ∀ (R : Type u) [Ring R] (A : NonUnitalSubring R) (I : Ideal R) [I.IsTwoSided],
    ∃ e : (nonUnitalCongruence A I).Quotient ≃+*
        (nonUnitalCongruence (sumNonUnitalSubring A I) I).Quotient,
      ∀ a : A, e (RingCon.toQuotient a) = nonUnitalRestriction A I a

end Specs.D07.Ch09.SecondIsomorphism
