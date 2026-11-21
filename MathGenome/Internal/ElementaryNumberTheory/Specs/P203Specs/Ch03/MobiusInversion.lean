import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions

/-! Independent statements for paper.tex:1000–1027, Theorem 3.4.
The arbitrary functions have precisely the source domain ℕ_{>0}. In the
finite sums, zero extension only supplies notation for evaluating them at
natural divisors; every such divisor and complementary divisor is positive.
All casts of μ are the canonical unital integer coefficient maps.
The arithmetic-function identity `1` is the delta of C01. -/
namespace P203Specs.MobiusInversion

universe u
open P203Specs.ClassicalFunctions

/-- Both directions, for every commutative unital ring and arbitrary
positive-input functions, including the equation at n = 1. -/
def Inversion : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : PositiveFunction R),
    (∀ n : ℕ+, g n = ∑ d ∈ (n : ℕ).divisors, zeroExtend f d) ↔
    (∀ n : ℕ+, f n = ∑ d ∈ (n : ℕ).divisors,
      (mu d : R) * zeroExtend g ((n : ℕ) / d))

def MobiusInverse : Prop :=
  mu * (one : ArithmeticFunction ℤ) = (1 : ArithmeticFunction ℤ)

def TotientSum : Prop :=
  ∀ n : ℕ+, (∑ d ∈ (n : ℕ).divisors, (phi d : ℤ)) = (n : ℕ)

def TotientConvolution : Prop :=
  (phi : ArithmeticFunction ℤ) = mu * (idK 1 : ArithmeticFunction ℤ)

def MangoldtConvolution : Prop :=
  vonMangoldt = (mu : ArithmeticFunction ℝ) * log

end P203Specs.MobiusInversion
