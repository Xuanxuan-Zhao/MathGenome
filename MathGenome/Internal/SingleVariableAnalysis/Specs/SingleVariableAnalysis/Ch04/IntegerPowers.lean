import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specification of the integer-power part of
K03.04.elementary_rules, paper.tex:733–757.

Positive powers use natural exponents and apply at every real base, including
zero. The zero power is specified separately as a constant with derivative
zero, without a negative power in its derivative value. Negative powers use
integer exponents and require a nonzero base; no positivity of that base is
required. The increment derivative is the upstream real-variable predicate.
-/

namespace Specs.SingleVariableAnalysis.Ch04.IntegerPowers

def incrementDerivativePositivePower : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < n →
    Derivative.hasRealIncrementDerivativeValue
      (fun x : ℝ => x ^ n) ((n : ℝ) * a ^ (n - 1)) a

def incrementDerivativeZeroPower : Prop :=
  ∀ a : ℝ, Derivative.hasRealIncrementDerivativeValue
    (fun x : ℝ => x ^ (0 : ℕ)) 0 a

def incrementDerivativeNegativePower : Prop :=
  ∀ (n : ℤ) (a : ℝ), n < 0 → a ≠ 0 →
    Derivative.hasRealIncrementDerivativeValue
      (fun x : ℝ => x ^ n) ((n : ℝ) * a ^ (n - 1)) a

def derivPositivePower : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < n →
    deriv (fun x : ℝ => x ^ n) a = (n : ℝ) * a ^ (n - 1)

def derivZeroPower : Prop :=
  ∀ a : ℝ, deriv (fun x : ℝ => x ^ (0 : ℕ)) a = 0

def derivNegativePower : Prop :=
  ∀ (n : ℤ) (a : ℝ), n < 0 → a ≠ 0 →
    deriv (fun x : ℝ => x ^ n) a = (n : ℝ) * a ^ (n - 1)

end Specs.SingleVariableAnalysis.Ch04.IntegerPowers
