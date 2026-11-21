import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs

/-! Independent statements for paper.tex:348–409 (Theorem 2.1 and the
preceding finite-group order paragraph). Positive moduli and positive prime
integers are represented by naturals, with explicit positivity hypotheses.
All congruences use ordinary integer divisibility. -/
namespace P203Specs.Ch02

universe u
open scoped BigOperators

/-- The source's multiplicative group of residue units, including modulus one. -/
abbrev ResidueUnits (m : ℕ) := (ZMod m)ˣ

/-- Euler's function is defined as the cardinality of the unit group. Its
agreement with Mathlib's counting definition is a conclusion below. -/
noncomputable def totient (m : ℕ) : ℕ := Nat.card (ResidueUnits m)

def TotientCardinality : Prop :=
  ∀ m : ℕ, 0 < m →
    totient m = m.totient ∧
    totient m = Nat.card {a : ℤ // 0 ≤ a ∧ a < (m : ℤ) ∧ Int.gcd a m = 1}

def ResidueUnitCriterion : Prop :=
  ∀ (m : ℕ) (a : ℤ), IsUnit (a : ZMod m) ↔ Int.gcd a m = 1

def TotientOne : Prop := totient 1 = 1

def TotientPrimePower : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k →
    totient (p ^ k) = p ^ (k - 1) * (p - 1)

def TotientProduct : Prop :=
  ∀ m : ℕ, 0 < m →
    (totient m : ℚ) = (m : ℚ) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℚ))

def TotientMultiplicative : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.gcd m n = 1 →
    totient (m * n) = totient m * totient n

/-- The order is the least positive exponent, detects every integer exponent,
and divides the size of the group. No commutativity assumption is made. -/
def FiniteGroupOrder : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (g : G),
    0 < orderOf g ∧ g ^ orderOf g = 1 ∧
    (∀ d : ℕ, 0 < d → g ^ d = 1 → orderOf g ≤ d) ∧
    (∀ j : ℤ, g ^ j = 1 ↔ (orderOf g : ℤ) ∣ j) ∧
    orderOf g ∣ Nat.card G

def EulerCongruence : Prop :=
  ∀ m : ℕ, 0 < m → ∀ a : ℤ, Int.gcd a m = 1 →
    (m : ℤ) ∣ a ^ totient m - 1

def FermatUnitCongruence : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : ℤ, ¬ (p : ℤ) ∣ a →
    (p : ℤ) ∣ a ^ (p - 1) - 1

def FermatAllResidues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : ℤ, (p : ℤ) ∣ a ^ p - a

def WilsonCriterion : Prop :=
  ∀ m : ℕ, 1 < m → (m.Prime ↔ (m : ℤ) ∣ (Nat.factorial (m - 1) : ℤ) + 1)

end P203Specs.Ch02
