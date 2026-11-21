import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.CharP.Defs

/-!
Independent specification of K07.11.multiplicity_derivative,
paper.tex:2441–2467 (chapters/M07.11.tex:296–322).

The objects are formal polynomials. `rootMultiplicity` is the same canonical
number as in the upstream root-bound specification; its interpretation as a
largest exponent is asserted only for nonzero polynomials. Formal derivative
laws allow arbitrary unital rings, including noncommutative and zero rings.
The linear-factor differentiation formula uses commutative coefficients.
Multiplicity statements use the field hypothesis of this source entry, with
no characteristic-zero assumption. Integer factors act by repeated addition.
-/

universe u

namespace Specs.D07.Ch11.MultiplicityDerivative

open Polynomial

/-- Degree bounds every possible exponent, so there is no unbounded sequence
of linear-factor powers dividing a nonzero polynomial. -/
def PowerDivisorBound : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 →
    ∀ (a : F) (k : ℕ), (X - C a) ^ k ∣ f → k ≤ f.natDegree

/-- The library multiplicity is precisely the maximum, including when a is
not a root. In particular its own power divides and the next power does not. -/
def MultiplicityMaximum : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → ∀ a : F,
    (∀ k : ℕ, (X - C a) ^ k ∣ f ↔ k ≤ f.rootMultiplicity a) ∧
    (X - C a) ^ f.rootMultiplicity a ∣ f ∧
    ¬ (X - C a) ^ (f.rootMultiplicity a + 1) ∣ f

def MultiplicityFactorization : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → ∀ a : F,
    ∃ g : Polynomial F,
      f = (X - C a) ^ f.rootMultiplicity a * g ∧ g.eval a ≠ 0

def NonrootMultiplicity : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → ∀ a : F,
    f.eval a ≠ 0 ↔ f.rootMultiplicity a = 0

/-- A coefficientwise specification fixes the formal derivative uniquely. -/
def DerivativeCoefficients : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R) (n : ℕ),
    f.derivative.coeff n = (n + 1) • f.coeff (n + 1)

/-- The index-zero summand vanishes. The remaining finite sum is exactly
the source formula with the integer i acting by repeated addition. -/
def DerivativeExpansion : Prop :=
  ∀ (R : Type u) [Ring R] (f : Polynomial R),
    f.derivative = ∑ i ∈ f.support, C (i • f.coeff i) * X ^ (i - 1)

def DerivativeAdditive : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    (f + g).derivative = f.derivative + g.derivative

/-- Formal differentiation of each coefficient monomial, also at i=0. -/
def DerivativeMonomial : Prop :=
  ∀ (R : Type u) [Ring R] (a : R) (i : ℕ),
    (C a * X ^ i).derivative = C (i • a) * X ^ (i - 1)

/-- No commutativity of the coefficients is needed for this ordered law. -/
def DerivativeProduct : Prop :=
  ∀ (R : Type u) [Ring R] (f g : Polynomial R),
    (f * g).derivative = f.derivative * g + f * g.derivative

/-- This applies in particular to the maximal multiplicity factorization. -/
def DerivativeLinearFactorization : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : Polynomial R) (a : R) (m : ℕ),
    1 ≤ m → f = (X - C a) ^ m * g →
      f.derivative = C (m : R) * (X - C a) ^ (m - 1) * g +
        (X - C a) ^ m * g.derivative

def SimpleRootDerivative : Prop :=
  ∀ (F : Type u) [Field F] (f g : Polynomial F) (a : F),
    f = (X - C a) * g → g.eval a ≠ 0 →
      f.derivative.eval a = g.eval a ∧ f.derivative.eval a ≠ 0

def HigherMultiplicityDerivative : Prop :=
  ∀ (F : Type u) [Field F] (f g : Polynomial F) (a : F) (m : ℕ),
    2 ≤ m → f = (X - C a) ^ m * g → f.derivative.eval a = 0

/-- The equivalence includes nonroots and is valid in every characteristic. -/
def RepeatedRootCriterion : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → ∀ a : F,
    1 < f.rootMultiplicity a ↔ f.eval a = 0 ∧ f.derivative.eval a = 0

def MultiplicityAtLeastTwo : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 → ∀ a : F,
    2 ≤ f.rootMultiplicity a ↔ f.eval a = 0 ∧ f.derivative.eval a = 0

/-- The derivative can vanish for a nonconstant formal polynomial. The
degree and inequality with every constant make nonconstancy explicit. -/
def PositiveCharacteristicExample : Prop :=
  ∀ (F : Type u) [Field F] (p : ℕ), p.Prime → ∀ [CharP F p],
    (X ^ p : Polynomial F).derivative = C (p : F) * X ^ (p - 1) ∧
    (X ^ p : Polynomial F).derivative = 0 ∧
    (X ^ p : Polynomial F).natDegree = p ∧
    ∀ c : F, (X ^ p : Polynomial F) ≠ C c

/-- Zero has all linear-factor powers as divisors and has no maximum. -/
def ZeroHasNoMaximum : Prop :=
  ∀ (F : Type u) [Field F] (a : F),
    (∀ k : ℕ, (X - C a) ^ k ∣ (0 : Polynomial F)) ∧
    ¬ ∃ m : ℕ, ∀ k : ℕ,
      (X - C a) ^ k ∣ (0 : Polynomial F) ↔ k ≤ m

end Specs.D07.Ch11.MultiplicityDerivative
