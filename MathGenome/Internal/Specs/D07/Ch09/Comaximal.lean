import MathGenome.Internal.Specs.D07.Ch08.IdealSumIntersection
import MathGenome.Internal.Specs.D07.Ch09.MaximalIdeal
import Mathlib.Algebra.Polynomial.Basic

/-!
Independent specifications for K07.09.comaximal, paper.tex:1710–1717.
The chapter assumes commutativity from line 1631. The ideal join is the
sum identified in K07.08.ideal_sum_intersection. No nontriviality is
required for comaximality or the Bezout equivalence.

The gcd assertions use its divisibility universal property, avoiding a
choice of normalized gcd in a general domain. The example 2, X in ℤ[X]
makes precise the stated strictness of the Bezout condition (also
explained later at paper.tex:1938–1944).
-/

universe u

namespace Specs.D07.Ch09.Comaximal

/-- Type of the comaximality predicate in the commutative chapter. -/
def ComaximalPredicateType : Type (u + 1) :=
  {R : Type u} → [CommRing R] → Ideal R → Ideal R → Prop

/-- The source definition: the sum of the ideals is the whole ring. -/
def comaximalPredicateValue : ComaximalPredicateType.{u} :=
  fun {_} _ I J => I ⊔ J = ⊤

/-- Comaximality is equivalent to an additive witness for one. -/
def WitnessCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    comaximalPredicateValue I J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1

/-- Two distinct maximal ideals are comaximal. Maximality includes properness. -/
def DistinctMaximalIdeals : Prop :=
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    MaximalIdeal.maximalPredicateValue I →
    MaximalIdeal.maximalPredicateValue J → I ≠ J →
      comaximalPredicateValue I J

/-- For principal ideals, the witnesses are exactly a Bezout identity. -/
def PrincipalBezout : Prop :=
  ∀ (R : Type u) [CommRing R] (a b : R),
    comaximalPredicateValue (Ideal.span {a}) (Ideal.span {b}) ↔
      ∃ r s : R, r * a + s * b = 1

/-- A Bezout identity implies that one is a greatest common divisor,
expressed by its universal divisibility property. -/
def BezoutImpliesGcdOne : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    (∃ r s : R, r * a + s * b = 1) →
      ∀ d : R, (d ∣ a ∧ d ∣ b) ↔ d ∣ 1

/-- In the domain ℤ[X], one is a gcd of 2 and X but there is no
Bezout identity, and their principal ideals are not comaximal. -/
def GcdOneNotSufficient : Prop :=
  (∀ d : Polynomial ℤ,
    (d ∣ (2 : Polynomial ℤ) ∧ d ∣ Polynomial.X) ↔ d ∣ 1) ∧
  (¬ ∃ f g : Polynomial ℤ, f * 2 + g * Polynomial.X = 1) ∧
  ¬ comaximalPredicateValue
    (Ideal.span {(2 : Polynomial ℤ)}) (Ideal.span {Polynomial.X})

end Specs.D07.Ch09.Comaximal
