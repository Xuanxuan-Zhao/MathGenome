import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.GaussianPrimes
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Multiplicativity
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! The ordered, signed representation count of paper.tex, Theorem 4.4
(nt:D04), lines 1512–1549. Existence criteria are allocated to D04.
All divisor sums below use positive natural divisors. The input n : ℕ
covers exactly the source's nonnegative integers, including zero. -/
namespace P203Specs.Ch04.TwoSquaresCount

/-- The canonical mod-four character; its explicit source values are specified below. -/
def chi4 (d : ℕ) : ℤ := ZMod.χ₄ d

/-- Coordinates are ordered integers, with no quotient by signs or interchange. -/
def representations (n : ℕ) : Set (ℤ × ℤ) :=
  {ab | ab.1 ^ 2 + ab.2 ^ 2 = (n : ℤ)}

noncomputable def r2 (n : ℕ) : ℕ := Nat.card (representations n)

/-- One representative for each orbit under the four units, for positive norm.
The positive real axis is included and the positive imaginary axis excluded. -/
def quarterRepresentations (n : ℕ) :=
  {z : GaussianInt // z.norm = (n : ℤ) ∧ 0 < z.re ∧ 0 ≤ z.im}

noncomputable def quarterCount (n : ℕ) : ℕ := Nat.card (quarterRepresentations n)

/-- Local count for a rational prime. Values at nonprimes are irrelevant. -/
def localFactor (p e : ℕ) : ℕ :=
  if p = 2 then 1 else if p % 4 = 1 then e + 1 else if Even e then 1 else 0

def CharacterValues : Prop :=
  ∀ d : ℕ, chi4 d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1

def CharacterMultiplicative : Prop :=
  chi4 1 = 1 ∧ ∀ a b : ℕ, chi4 (a * b) = chi4 a * chi4 b

def RepresentationFiniteness : Prop := ∀ n : ℕ, (representations n).Finite

def ZeroRepresentations : Prop := representations 0 = {(0, 0)} ∧ r2 0 = 1

def GaussianCountBridge : Prop :=
  ∀ n : ℕ, r2 n = Nat.card {z : GaussianInt // z.norm = (n : ℤ)}

def FourUnitCount : Prop := ∀ n : ℕ, 0 < n → r2 n = 4 * quarterCount n

def QuarterMultiplicative : Prop :=
  quarterCount 1 = 1 ∧
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n →
    quarterCount (m * n) = quarterCount m * quarterCount n

def QuarterPrimePowers : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, quarterCount (p ^ e) = localFactor p e

def GaussianFactorCount : Prop :=
  ∀ n : ℕ, 0 < n →
    r2 n = 4 * ∏ p ∈ n.primeFactors, localFactor p (n.factorization p)

def DivisorSumFactors : Prop :=
  ∀ n : ℕ, 0 < n →
    (∑ d ∈ n.divisors, chi4 d) =
      ∏ p ∈ n.primeFactors, (localFactor p (n.factorization p) : ℤ)

def CountFormula : Prop :=
  ∀ n : ℕ, 0 < n → (r2 n : ℤ) = 4 * ∑ d ∈ n.divisors, chi4 d

end P203Specs.Ch04.TwoSquaresCount
