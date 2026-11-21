import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions
import Mathlib.NumberTheory.Chebyshev

/-! Independent objects and statements for paper.tex:1208–1234.
Primes are positive natural primes. Natural floor truncation makes all four
functions defined on every real input. The inner interval in `psi` contains
exactly the positive exponents with `p ^ k ≤ x`, as required by `PrimePowerIndex`.
In particular, a prime contributes once for EACH allowed exponent.
-/
namespace P203Specs.PrimeProduct

/-- Positive primes at most the real cutoff. -/
noncomputable def primes (x : ℝ) : Finset ℕ := Nat.primesLE ⌊x⌋₊

/-- The source prime product, with empty product equal to one. -/
noncomputable def P (x : ℝ) : ℝ := ∏ p ∈ primes x, (p : ℝ)

noncomputable def theta (x : ℝ) : ℝ := ∑ p ∈ primes x, Real.log (p : ℝ)

/-- A sum indexed by prime AND exponent, retaining prime-power multiplicities.
`Nat.log p n` is the largest exponent whose power is at most `n` for `p ≥ 2`,
with the harmless zero convention when the cutoff is zero. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ p ∈ primes x, ∑ _k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log (p : ℝ)

noncomputable def piCount (x : ℝ) : ℕ := (primes x).card

/-- The finite prime index has exactly the source's meaning on all real inputs. -/
def PrimeIndex : Prop :=
  ∀ (x : ℝ) (p : ℕ), p ∈ primes x ↔ p.Prime ∧ (p : ℝ) ≤ x

/-- Exact identification of the double index, including each positive exponent. -/
def PrimePowerIndex : Prop :=
  ∀ (x : ℝ) (p k : ℕ),
    (p ∈ primes x ∧ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊)) ↔
      p.Prime ∧ 1 ≤ k ∧ ((p ^ k : ℕ) : ℝ) ≤ x

/-- Identification with the library's conventions and the summatory function
of the SAME canonical von Mangoldt function fixed in Proposition 3.3. -/
def Identifications : Prop :=
  ∀ x : ℝ,
    P x = (primorial ⌊x⌋₊ : ℝ) ∧
    theta x = Chebyshev.theta x ∧
    psi x = Chebyshev.psi x ∧
    psi x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ClassicalFunctions.vonMangoldt n ∧
    piCount x = Nat.primeCounting ⌊x⌋₊

/-- Lemma 3.9. The right-hand exponent is REAL, not a natural power. -/
def PrimeProductBound : Prop := ∀ x : ℝ, 1 ≤ x → P x ≤ (4 : ℝ) ^ x

/-- Empty sums and product below the first positive prime, including negatives. -/
def BelowTwo : Prop :=
  ∀ x : ℝ, x < 2 → P x = 1 ∧ theta x = 0 ∧ psi x = 0 ∧ piCount x = 0

end P203Specs.PrimeProduct
