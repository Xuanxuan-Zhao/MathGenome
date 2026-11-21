import MathGenome.Internal.Specs.D07.Foundations.IntegerArithmetic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Independent statements for the prime representation part of
`paper.tex:5680–5711`. Primality of a positive integer uses the arithmetic
foundation's predicate. Square witnesses are signed integers. The intermediate
statements retain Wilson's inverse pairing and the Gaussian norm argument;
none assumes a classification of Gaussian primes. -/

namespace Specs.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion

def SelfInverseResidues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ x : ZMod p, x ≠ 0 →
    (x⁻¹ = x ↔ x = 1 ∨ x = -1)

def InversePairingProduct : Prop :=
  ∀ (p : ℕ) (hp : p.Prime),
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∏ u : (ZMod p)ˣ, u) = -1

def Wilson : Prop :=
  ∀ p : ℕ, p.Prime → (Nat.factorial (p - 1) : ZMod p) = -1

def FactorialPairing : Prop :=
  ∀ p : ℕ, Odd p →
    (Nat.factorial (p - 1) : ZMod p) =
      (-1) ^ ((p - 1) / 2) * (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2

/-- A specified square root, and an integer representative of a square root. -/
def WilsonSquareRoot : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2 = -1 ∧
      ∃ x : ℤ, (p : ℤ) ∣ x ^ 2 + 1

/-- The product `(x+i)(x-i)` witnesses failure of Gaussian primality. -/
def GaussianNonprime : Prop :=
  ∀ p : ℕ, p.Prime → ∀ x : ℤ, (p : ℤ) ∣ x ^ 2 + 1 →
    (p : GaussianInt) ∣ (⟨x, 1⟩ : GaussianInt) * ⟨x, -1⟩ ∧
    ¬ (p : GaussianInt) ∣ (⟨x, 1⟩ : GaussianInt) ∧
    ¬ (p : GaussianInt) ∣ (⟨x, -1⟩ : GaussianInt) ∧
    ¬ Prime (p : GaussianInt) ∧ ¬ Irreducible (p : GaussianInt)

/-- A proper Gaussian factorization has both norms equal to the rational prime. -/
def GaussianFactorNorms : Prop :=
  ∀ p : ℕ, p.Prime → ¬ Irreducible (p : GaussianInt) →
    ∃ u v : GaussianInt, (p : GaussianInt) = u * v ∧
      ¬ IsUnit u ∧ ¬ IsUnit v ∧ u.norm = (p : ℤ) ∧ v.norm = (p : ℤ)

def PrimeTwoSquareCriterionNat : Prop :=
  ∀ p : ℕ, p.Prime →
    ((∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2) ↔ p = 2 ∨ p % 4 = 1)

def PrimeTwoSquareCriterion : Prop :=
  ∀ p : ℤ, D07.Foundations.IntegerArithmetic.PositivePrime p →
    ((∃ a b : ℤ, p = a ^ 2 + b ^ 2) ↔ p = 2 ∨ p % 4 = 1)

end Specs.D07.Ch19.GaussianPrimesTwoSquaresPrimeTwoSquareCriterion
