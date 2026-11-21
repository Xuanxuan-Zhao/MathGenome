import MathGenome.Internal.Specs.D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
import MathGenome.Internal.Specs.D07.Ch10.DedekindHasseSufficient
import Mathlib.Data.Int.GCD

/-! Independent obligations for paper.tex:2091–2121. The fraction is taken in
ℂ using the original embedding of R; no new model of the quadratic ring is used.
All denominator cases, including the two parity cases at four, are retained. -/
noncomputable section
namespace D07.Ch10.PidNotEuclideanDedekindHasseVerification
open PidNotEuclideanQuadraticIntegerNorm

def quadraticFraction (A B c : ℤ) : ℂ :=
  ((A : ℂ) + (B : ℂ) * sqrtMinus19) / (c : ℂ)

def Primitive (A B c : ℤ) : Prop := Int.gcd (Int.gcd A B : ℤ) c = 1

def HasSmallRemainder (z : ℂ) : Prop :=
  ∃ s t : R, 0 < Complex.normSq (z * (s : ℂ) - (t : ℂ)) ∧
    Complex.normSq (z * (s : ℂ) - (t : ℂ)) < 1

namespace Specs

def ReducedRepresentation : Prop :=
  ∀ a b : R, b ≠ 0 → ¬ b ∣ a → ∃ A B c : ℤ,
    1 < c ∧ Primitive A B c ∧ (a : ℂ) / (b : ℂ) = quadraticFraction A B c

def LargeDenominator : Prop :=
  ∀ A B c : ℤ, 5 ≤ c → Primitive A B c → HasSmallRemainder (quadraticFraction A B c)

def DenominatorTwo : Prop :=
  ∀ A B : ℤ, Primitive A B 2 → quadraticFraction A B 2 ∉ integerRing →
    HasSmallRemainder (quadraticFraction A B 2)

def DenominatorThree : Prop :=
  ∀ A B : ℤ, Primitive A B 3 → HasSmallRemainder (quadraticFraction A B 3)

def DenominatorFourOpposite : Prop :=
  ∀ A B : ℤ, A % 2 ≠ B % 2 → HasSmallRemainder (quadraticFraction A B 4)

def DenominatorFourOdd : Prop :=
  ∀ A B : ℤ, A % 2 = 1 → B % 2 = 1 → HasSmallRemainder (quadraticFraction A B 4)

def FractionApproximation : Prop :=
  ∀ a b : R, b ≠ 0 → ¬ b ∣ a → HasSmallRemainder ((a : ℂ) / (b : ℂ))

def DedekindHasseVerification : Prop :=
  ∀ a b : R, a ≠ 0 → b ≠ 0 → ¬ b ∣ a →
    ∃ s t : R, 0 < norm (s * a - t * b) ∧ norm (s * a - t * b) < norm b

def PrincipalIdealDomain : Prop := _root_.Specs.D07.Ch10.PidDefinition.pidPredicateValue R

end Specs
end D07.Ch10.PidNotEuclideanDedekindHasseVerification
