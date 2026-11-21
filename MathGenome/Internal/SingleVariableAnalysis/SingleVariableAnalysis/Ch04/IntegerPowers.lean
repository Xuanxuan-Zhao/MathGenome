import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.IntegerPowers
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Integer power derivatives

The integer-power part of K03.04.elementary_rules (paper.tex:733–757).
We transport Mathlib's `hasDerivAt_pow` and `hasDerivAt_zpow` through the
proved equivalence with real-increment differentiation. These library proofs
use the power and reciprocal rules; they do not require constructing real
exponentiation by logarithms. In the negative case the base may have either
sign, and its nonzero hypothesis discharges the library rule's domain condition.

The constant zero power is handled by the constant rule, including at zero.
The derivative-existence statements precede the equalities for `deriv`, so
none of the conclusions relies on the default value of a total derivative.
-/

namespace SingleVariableAnalysis

theorem incrementDerivative_positive_power (n : ℕ) (a : ℝ) (_hn : 0 < n) :
    HasRealIncrementDerivative (fun x : ℝ => x ^ n)
      ((n : ℝ) * a ^ (n - 1)) a := by
  exact (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr (hasDerivAt_pow n a)

theorem incrementDerivative_zero_power (a : ℝ) :
    HasRealIncrementDerivative (fun x : ℝ => x ^ (0 : ℕ)) 0 a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  simpa only [pow_zero] using (hasDerivAt_const a (1 : ℝ))

theorem incrementDerivative_negative_power (n : ℤ) (a : ℝ) (_hn : n < 0)
    (ha : a ≠ 0) :
    HasRealIncrementDerivative (fun x : ℝ => x ^ n)
      ((n : ℝ) * a ^ (n - 1)) a := by
  exact (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
    (hasDerivAt_zpow n a (Or.inl ha))

theorem deriv_positive_power (n : ℕ) (a : ℝ) (hn : 0 < n) :
    deriv (fun x : ℝ => x ^ n) a = (n : ℝ) * a ^ (n - 1) :=
  ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_positive_power n a hn)).deriv

theorem deriv_zero_power (a : ℝ) :
    deriv (fun x : ℝ => x ^ (0 : ℕ)) a = 0 :=
  ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_zero_power a)).deriv

theorem deriv_negative_power (n : ℤ) (a : ℝ) (hn : n < 0) (ha : a ≠ 0) :
    deriv (fun x : ℝ => x ^ n) a = (n : ℝ) * a ^ (n - 1) :=
  ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_negative_power n a hn ha)).deriv

end SingleVariableAnalysis
