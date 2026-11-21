import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs

/-!
# Theorem 1.2: independent specification

Source: `paper.tex`, lines 77–144, including the nonnegative gcd/lcm
convention and the unnumbered coprime cancellation statement.
All arithmetic is Mathlib's ordinary integer arithmetic.
-/
namespace P203Specs.Ch01

/-- A finite Euclidean division run. Each step records its quotient and
remainder, with a positive divisor and the standard remainder bounds.
The final pair is `(d, 0)` with `d ≥ 0`. -/
inductive EuclideanRun : ℤ → ℤ → ℤ → Prop
  | stop (u : ℤ) (hu : 0 ≤ u) : EuclideanRun u 0 u
  | step {u v r d : ℤ} (q : ℤ) (hv : 0 < v)
      (division : u = q * v + r) (hr : 0 ≤ r) (hlt : r < v)
      (tail : EuclideanRun v r d) : EuclideanRun u v d

/-- Termination at the ordinary nonnegative gcd, and correctness of every
finite run from the prescribed absolute-value initial pair. -/
def EuclideanAlgorithm : Prop :=
  ∀ a b : ℤ,
    EuclideanRun |a| |b| (Int.gcd a b : ℤ) ∧
    ∀ d : ℤ, EuclideanRun |a| |b| d → d = (Int.gcd a b : ℤ)

/-- The gcd generates exactly all integer linear combinations. This includes
its nonnegativity, divisibility, Bézout witnesses and greatest-divisor property. -/
def GcdBezout : Prop :=
  ∀ a b : ℤ,
    0 ≤ (Int.gcd a b : ℤ) ∧
    (Int.gcd a b : ℤ) ∣ a ∧ (Int.gcd a b : ℤ) ∣ b ∧
    (∀ c : ℤ, c ∣ a → c ∣ b → c ∣ (Int.gcd a b : ℤ)) ∧
    (∃ x y : ℤ, (Int.gcd a b : ℤ) = a * x + b * y) ∧
    {n : ℤ | ∃ x y : ℤ, n = a * x + b * y} =
      {n : ℤ | ∃ k : ℤ, n = (Int.gcd a b : ℤ) * k}

/-- The zero-input boundary convention is stated explicitly. -/
def ZeroGcd : Prop := (Int.gcd 0 0 : ℤ) = 0

/-- Positive prime integers satisfy Euclid's lemma. `Nat.Prime p.natAbs`
uses the ordinary divisor/factorization definition of a prime number;
Euclid's product-divisibility property is the conclusion, not a hypothesis. -/
def PrimeDividesProduct : Prop :=
  ∀ p : ℤ, 0 < p → Nat.Prime p.natAbs →
    ∀ a b : ℤ, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- Coprime cancellation, including arbitrary signed and zero integers. -/
def CoprimeCancellation : Prop :=
  ∀ x y z : ℤ, Int.gcd x y = 1 → x ∣ y * z → x ∣ z

/-- The nonnegative lcm, its zero/nonzero formula and its complete universal
property for common multiples (including negative and zero multiples). -/
def LcmProperties : Prop :=
  ∀ a b : ℤ,
    0 ≤ (Int.lcm a b : ℤ) ∧
    (a * b = 0 → (Int.lcm a b : ℤ) = 0) ∧
    (a * b ≠ 0 → (Int.lcm a b : ℤ) = |a * b| / (Int.gcd a b : ℤ)) ∧
    ∀ M : ℤ, (a ∣ M ∧ b ∣ M) ↔ (Int.lcm a b : ℤ) ∣ M

end P203Specs.Ch01
