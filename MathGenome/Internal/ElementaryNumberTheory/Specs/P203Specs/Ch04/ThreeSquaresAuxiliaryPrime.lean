import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.JacobiRules
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Squarefree

/-! The auxiliary-prime construction in paper.tex:1893–1942, with the integer
congruence conventions at 58–65 and 80–86. The witnesses retain the reduced
class modulo 8m, the two signs in the five-case calculation, and both integer
roots needed by the subsequent lattice. Symbols reuse the upstream definitions.
-/
namespace P203Specs.Ch04

/-- The five squarefree residue possibilities outside the three-square obstruction. -/
def ThreeSquaresResidue (n : ℕ) : Prop :=
  n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6

/-- The five rows in paper.tex:1909–1918, retaining the residue information
used by both supplement calculations. -/
def AuxiliaryCase (n k m ell c : ℕ) : Prop :=
  (n % 8 = 1 ∧ k = 0 ∧ m % 4 = 1 ∧ ell = 0 ∧ c = 1) ∨
  (n % 8 = 2 ∧ k = 1 ∧ m % 4 = 1 ∧ ell = 0 ∧ c = 1) ∨
  (n % 8 = 3 ∧ k = 0 ∧ m % 8 = 3 ∧ ell = 1 ∧ c = 1) ∨
  (n % 8 = 5 ∧ k = 0 ∧ m % 4 = 1 ∧ ell = 0 ∧ c = 1) ∨
  (n % 8 = 6 ∧ k = 1 ∧ m % 4 = 3 ∧ ell = 0 ∧ c = 5)

/-- Complete auxiliary data, including the CRT class from which the prime comes. -/
structure AuxiliaryPrimeData (n k m ell q : ℕ) (a u v : ℤ) : Prop where
  k_le : k ≤ 1
  odd_m : Odd m
  decomposition : n = 2 ^ k * m
  ell_eq : ell = if n % 8 = 3 then 1 else 0
  prime : q.Prime
  gt : n < q
  residue : q % 8 = if n % 8 = 6 then 5 else 1
  reduced_class : Int.gcd a ((8 * m : ℕ) : ℤ) = 1
  prime_class : (q : ℤ) ≡ a [ZMOD ((8 * m : ℕ) : ℤ)]
  class_eight : a ≡ (if n % 8 = 6 then 5 else 1) [ZMOD 8]
  class_odd : -(2 : ℤ) ^ ell * a ≡ 1 [ZMOD (m : ℤ)]
  local_squares : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m →
    ¬(p : ℤ) ∣ -((2 : ℤ) ^ ell * q) ∧
      ∃ x : ℤ, x ^ 2 ≡ -((2 : ℤ) ^ ell * q) [ZMOD (p : ℤ)]
  mod_four : q % 4 = 1
  sign_q : Ch02.legendreSymbol (-((2 : ℤ) ^ k)) q =
    (-1 : ℤ) ^ (k * ((m - 1) / 2))
  sign_m : Ch02.jacobiSymbol (-((2 : ℤ) ^ ell)) m =
    (-1 : ℤ) ^ (k * ((m - 1) / 2))
  reciprocity : Ch02.legendreSymbol (-(n : ℤ)) q = 1
  coprime : Int.gcd ((2 : ℤ) ^ ell * q) n = 1
  root_u : u ^ 2 ≡ -(n : ℤ) [ZMOD ((4 : ℤ) ^ ell * q)]
  root_v : (2 : ℤ) ^ ell * q * v ^ 2 ≡ -1 [ZMOD (n : ℤ)]

/-- No roots or prime are assumed: all the data are constructed from n. -/
def ThreeSquaresAuxiliaryPrime : Prop :=
  ∀ n : ℕ, Squarefree n → 1 < n → ThreeSquaresResidue n →
    ∃ (k m ell q : ℕ) (a u v : ℤ), AuxiliaryPrimeData n k m ell q a u v

/-- The source's second congruence expressed with the actual inverse in ℤ/nℤ. -/
def AuxiliaryInverseCongruence : Prop :=
  ∀ (n : ℕ) (b v : ℤ), Int.gcd b n = 1 →
    (b * v ^ 2 ≡ -1 [ZMOD (n : ℤ)] ↔
      (v : ZMod n) ^ 2 = -(b : ZMod n)⁻¹)

end P203Specs.Ch04
