import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.LegendreGauss
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Basic

/-! Independent specification of paper.tex:726–791 (Theorem 2.9 and its
computation and example), using the positive-modulus conventions at 58–65, 80–86.
Natural odd denominators are positive. Numerators are arbitrary integers.
The canonical Mathlib symbol is connected below to the source's prime-power
product using the previously specified numerator-first Legendre symbol. -/
namespace P203Specs.Ch02

def jacobiSymbol : ℤ → ℕ → ℤ := jacobiSym

def JacobiSymbolType : Type := ℤ → ℕ → ℤ

def JacobiFactorization : Prop :=
  ∀ (a : ℤ) (m : ℕ), Odd m →
    jacobiSymbol a m = ∏ p ∈ m.primeFactors,
      legendreSymbol a p ^ m.factorization p

def JacobiOne : Prop := ∀ a : ℤ, jacobiSymbol a 1 = 1

def JacobiPrime : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a : ℤ,
    jacobiSymbol a p = legendreSymbol a p

def JacobiReduction : Prop :=
  ∀ (a : ℤ) (m : ℕ), Odd m →
    0 ≤ a % (m : ℤ) ∧ a % (m : ℤ) < (m : ℤ) ∧
      jacobiSymbol a m = jacobiSymbol (a % (m : ℤ)) m

def JacobiResidueClass : Prop :=
  ∀ (a b : ℤ) (m : ℕ), Odd m → a ≡ b [ZMOD (m : ℤ)] →
    jacobiSymbol a m = jacobiSymbol b m

def JacobiMultiplicativity : Prop :=
  (∀ (a b : ℤ) (m : ℕ), Odd m →
    jacobiSymbol (a * b) m = jacobiSymbol a m * jacobiSymbol b m) ∧
  (∀ (a : ℤ) (m n : ℕ), Odd m → Odd n →
    jacobiSymbol a (m * n) = jacobiSymbol a m * jacobiSymbol a n)

def JacobiZero : Prop :=
  ∀ (a : ℤ) (m : ℕ), Odd m → (jacobiSymbol a m = 0 ↔ 1 < Int.gcd a m)

def JacobiSupplementNegOne : Prop :=
  ∀ m : ℕ, Odd m → jacobiSymbol (-1) m = (-1 : ℤ) ^ ((m - 1) / 2)

def JacobiSupplementTwo : Prop :=
  ∀ m : ℕ, Odd m → jacobiSymbol 2 m = (-1 : ℤ) ^ ((m ^ 2 - 1) / 8)

def JacobiReciprocity : Prop :=
  ∀ a m : ℕ, Odd a → Odd m →
    jacobiSymbol (a : ℤ) m =
      (-1 : ℤ) ^ (((a - 1) / 2) * ((m - 1) / 2)) * jacobiSymbol (m : ℤ) a

/-- A finite execution of the source's algorithm. Each constructor is an
arithmetic computation rule, independent of the symbol being computed.
`power` is the odd-part-one branch; `step` extracts `2^v*c`, applies the
second supplement and reciprocity, and recurses with strictly smaller odd
positive denominator `c`. An inductive derivation is a finite execution. -/
inductive JacobiEvaluation : ℤ → ℕ → ℤ → Prop
  | one (a : ℤ) : JacobiEvaluation a 1 1
  | zero {a : ℤ} {m : ℕ} (hm : Odd m) (hm1 : 1 < m)
      (hr : a % (m : ℤ) = 0) : JacobiEvaluation a m 0
  | power {a : ℤ} {m v : ℕ} (hm : Odd m) (hm1 : 1 < m)
      (hr : a % (m : ℤ) = (2 : ℤ) ^ v) :
      JacobiEvaluation a m (((-1 : ℤ) ^ ((m ^ 2 - 1) / 8)) ^ v)
  | step {a : ℤ} {m v c : ℕ} {z : ℤ} (hm : Odd m) (hm1 : 1 < m)
      (hc : Odd c) (hc1 : 1 < c) (hcm : c < m)
      (hr : a % (m : ℤ) = (2 : ℤ) ^ v * (c : ℤ))
      (next : JacobiEvaluation (m : ℤ) c z) :
      JacobiEvaluation a m
        ((((-1 : ℤ) ^ ((m ^ 2 - 1) / 8)) ^ v) *
          (-1 : ℤ) ^ (((c - 1) / 2) * ((m - 1) / 2)) * z)

/-- Termination on the entire source domain, including arbitrary negative
numerators, denominator one and noncoprime inputs. -/
def JacobiTermination : Prop :=
  ∀ (a : ℤ) (m : ℕ), Odd m → ∃ z : ℤ, JacobiEvaluation a m z

/-- Every finite computation returns the prime-factor-defined symbol. -/
def JacobiComputationCorrect : Prop :=
  ∀ (a : ℤ) (m : ℕ) (z : ℤ), JacobiEvaluation a m z → jacobiSymbol a m = z

/-- Thus all runs on a valid input agree. -/
def JacobiComputationUnique : Prop :=
  ∀ (a : ℤ) (m : ℕ), Odd m → ∃! z : ℤ, JacobiEvaluation a m z

def JacobiCompositeExample : Prop :=
  jacobiSymbol 2 15 = 1 ∧ ¬ ∃ x : ℤ, x ^ 2 ≡ 2 [ZMOD 15]

end P203Specs.Ch02
