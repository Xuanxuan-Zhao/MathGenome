import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.NumberTheory.Real.Irrational

/-! Independent statements for paper.tex, §5.1, rational roots and its first corollary.
The polynomial's actual degree and leading coefficient are used throughout.
Integer gcd is nonnegative, and rational denominators are positive.
-/
namespace P203Specs.Ch05.RationalRoots

/-- The nonzero reduced-root clause, with the source's degree assumptions. -/
def NonzeroRoot : Prop :=
  ∀ (P : Polynomial ℤ), 1 ≤ P.natDegree → P.leadingCoeff ≠ 0 →
    ∀ (p q : ℤ), 0 < q → Int.gcd p q = 1 →
      (p : ℚ) / q ≠ 0 → Polynomial.aeval ((p : ℚ) / q) P = 0 →
      p ∣ P.coeff 0 ∧ q ∣ P.leadingCoeff

/-- At zero, the constant coefficient vanishes and the reduced denominator is one. -/
def ZeroRoot : Prop :=
  ∀ (P : Polynomial ℤ) (p q : ℤ), 0 < q → Int.gcd p q = 1 →
    (p : ℚ) / q = 0 → Polynomial.aeval (0 : ℚ) P = 0 →
    P.coeff 0 = 0 ∧ p = 0 ∧ q = 1

/-- Every rational root of a monic integer polynomial is an integer. -/
def MonicRoot : Prop :=
  ∀ (P : Polynomial ℤ), P.Monic → ∀ (r : ℚ),
    Polynomial.aeval r P = 0 → ∃ z : ℤ, r = (z : ℚ)

/-- Nonnegative kth roots of natural numbers that are not kth powers are irrational. -/
def IrrationalNthRoot : Prop :=
  ∀ (k m : ℕ), 2 ≤ k → (¬ ∃ n : ℕ, n ^ k = m) →
    ∀ (r : ℝ), 0 ≤ r → r ^ k = (m : ℝ) → Irrational r

/-- In particular, square roots of nonsquare natural numbers are irrational. -/
def IrrationalSqrt : Prop :=
  ∀ (m : ℕ), (¬ ∃ n : ℕ, n ^ 2 = m) → Irrational (Real.sqrt (m : ℝ))

end P203Specs.Ch05.RationalRoots
