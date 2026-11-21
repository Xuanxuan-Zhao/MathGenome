import MathGenome.Internal.Specs.D07.Ch10.GcdLcm
import MathGenome.Internal.Specs.D07.Ch10.PidDefinition
import MathGenome.Internal.Specs.D07.Ch11.DegreeArithmetic
import Mathlib.Algebra.Polynomial.Coeff

/-!
Independent propositions for K07.10.bezout (paper.tex:1931–1946).
The gcd predicate is the shared divisibility predicate, without normalization.
General rings are commutative nontrivial domains. Principal-pair statements do
not require a PID. PID assertions include all inputs and every choice of gcd.
The counterexample uses the formal polynomial ring over the integers.
-/

universe u

namespace Specs.D07.Ch10.Bezout

open Polynomial
open Specs.D07.Ch10.GcdLcm

def PairMembership : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d : R),
    d ∈ Ideal.span ({a, b} : Set R) ↔ ∃ x y : R, d = x * a + y * b

def CommonDivisorInclusion : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b c : R),
    c ∣ a → c ∣ b → Ideal.span ({a, b} : Set R) ≤ Ideal.span {c}

def PrincipalPairGcd : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d : R),
    Ideal.span ({a, b} : Set R) = Ideal.span {d} → IsGcd R a b d

def PrincipalPairBezout : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d : R),
    Ideal.span ({a, b} : Set R) = Ideal.span {d} →
      ∃ x y : R, d = x * a + y * b

def PIDGcdBezout : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (a b : R),
    ∃ d : R, Ideal.span ({a, b} : Set R) = Ideal.span {d} ∧
      IsGcd R a b d ∧ ∃ x y : R, d = x * a + y * b

/-- No choice of associate representative is imposed on the given gcd. -/
def PIDEveryGcdBezout : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (a b d : R),
    IsGcd R a b d → Ideal.span ({a, b} : Set R) = Ideal.span {d} ∧
      ∃ x y : R, d = x * a + y * b

def AllZeroCase : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    Ideal.span ({0, 0} : Set R) = Ideal.span {(0 : R)} ∧
      IsGcd R 0 0 0 ∧ (∃ x y : R, (0 : R) = x * 0 + y * 0)

def DivisorTwoConstant : Prop :=
  ∀ p : Polynomial ℤ, p ∣ C (2 : ℤ) → ∃ n : ℤ, p = C n

def CommonDivisorTwoXUnit : Prop :=
  ∀ p : Polynomial ℤ, p ∣ C (2 : ℤ) → p ∣ X → IsUnit p

def TwoXGcdOne : Prop :=
  IsGcd (Polynomial ℤ) (C (2 : ℤ)) X 1

/-- All possible combinations have even constant coefficient. -/
def EvenConstantCoefficient : Prop :=
  ∀ f g : Polynomial ℤ, (2 : ℤ) ∣ (C 2 * f + X * g).coeff 0

def TwoXNoBezout : Prop :=
  ¬ ∃ f g : Polynomial ℤ, C 2 * f + X * g = 1

end Specs.D07.Ch10.Bezout
