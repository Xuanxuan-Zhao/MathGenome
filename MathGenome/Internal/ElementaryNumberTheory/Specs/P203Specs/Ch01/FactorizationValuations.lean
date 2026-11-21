import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Order.Ring.Int

/-!
Independent specification of `paper.tex`, Theorem 1.3 and its surrounding
conventions and consequences (lines 145–196). Positive integer primes are
represented by `p : ℕ` with `p.Prime`; their integer value is `(p : ℤ)`.
The valuation is Mathlib's extended multiplicity, not a new arithmetic model.
-/
namespace P203Specs.Ch01

/-- The single canonical valuation, including the value infinity at zero.
For nonzero integers the bridge below identifies this with the exponent in
`|n|`'s prime factorization. -/
noncomputable def primeValuation (p : ℕ) (n : ℤ) : ℕ∞ :=
  emultiplicity (p : ℤ) n

def UniquePrimeFactorization : Prop :=
  (∀ n : ℕ, 0 < n → ∃ l : List ℕ,
    l.prod = n ∧ (∀ p ∈ l, p.Prime) ∧
    ∀ k : List ℕ, k.prod = n → (∀ p ∈ k, p.Prime) → k.Perm l) ∧
  Nat.primeFactorsList 1 = []

def IntegerPrimeFactorization : Prop :=
  ∀ n : ℤ, n ≠ 0 →
    (n.sign = 1 ∨ n.sign = -1) ∧
    ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧
      l.prod = n.natAbs ∧ n = n.sign * (l.prod : ℤ) ∧
      ∀ k : List ℕ, k.prod = n.natAbs → (∀ p ∈ k, p.Prime) → k.Perm l

def IntegerUnits : Prop := ∀ n : ℤ, IsUnit n ↔ n = 1 ∨ n = -1

/-- The finite exponent is exactly the count in the prime factorization. -/
def ValuationFactorizationBridge : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℤ, n ≠ 0 →
    primeValuation p n = (n.natAbs.factorization p : ℕ∞) ∧
    primeValuation p n ≠ ⊤

def ValuationZeroAndUnits : Prop :=
  ∀ p : ℕ, p.Prime →
    primeValuation p 0 = ⊤ ∧ primeValuation p 1 = 0 ∧ primeValuation p (-1) = 0

/-- Includes zero factors, using infinity plus any value equals infinity. -/
def ValuationProduct : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a b : ℤ,
    primeValuation p (a * b) = primeValuation p a + primeValuation p b

/-- All signed and zero integers, including `0 ∣ b ↔ b = 0`. -/
def ValuationDivisibility : Prop :=
  (∀ a b : ℤ, a ∣ b ↔
    ∀ p : ℕ, p.Prime → primeValuation p a ≤ primeValuation p b) ∧
  (∀ b : ℤ, (0 : ℤ) ∣ b ↔ b = 0)

/-- The nonnegative integer gcd and lcm, including two zero inputs. -/
def ValuationGcdLcm : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a b : ℤ,
    primeValuation p (Int.gcd a b : ℤ) = min (primeValuation p a) (primeValuation p b) ∧
    primeValuation p (Int.lcm a b : ℤ) = max (primeValuation p a) (primeValuation p b)

/-- The prime-power criterion is also valid at zero. -/
def ValuationPrimePowers : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℤ, ∀ j : ℕ,
    (p : ℤ) ^ j ∣ n ↔ (j : ℕ∞) ≤ primeValuation p n

/-- Finite arithmetic, expressed using the natural number represented by the
finite canonical valuation. This recovers precisely the nonzero formulation. -/
def FiniteValuationArithmetic : Prop :=
  ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
    (∀ p : ℕ, p.Prime →
      (primeValuation p (a * b)).toNat =
        (primeValuation p a).toNat + (primeValuation p b).toNat) ∧
    (a ∣ b ↔ ∀ p : ℕ, p.Prime →
      (primeValuation p a).toNat ≤ (primeValuation p b).toNat) ∧
    (∀ p : ℕ, p.Prime →
      (primeValuation p (Int.gcd a b : ℤ)).toNat =
        min (primeValuation p a).toNat (primeValuation p b).toNat ∧
      (primeValuation p (Int.lcm a b : ℤ)).toNat =
        max (primeValuation p a).toNat (primeValuation p b).toNat) ∧
    (∀ p : ℕ, p.Prime → ∀ j : ℕ,
      ((p : ℤ) ^ j ∣ a ↔ j ≤ (primeValuation p a).toNat))

def UnequalValuationSum : Prop :=
  ∀ p : ℕ, p.Prime → ∀ U V : ℤ, ∀ j : ℕ,
    primeValuation p U = (j : ℕ∞) → (p : ℤ) ^ (j + 1) ∣ V →
    primeValuation p (U + V) = (j : ℕ∞)

end P203Specs.Ch01
