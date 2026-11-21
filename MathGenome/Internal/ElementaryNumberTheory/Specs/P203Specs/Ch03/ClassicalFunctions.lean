import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Convolution
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TotientClassicalCongruences
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! Independent statements for paper.tex:959–998, Proposition 3.3 (nt:C03).
All functions use the canonical arithmetic-function model of C01. Values at
zero are the model's zero extension; the source's domain is the positive
integers. Natural-valued functions are cast coefficientwise into the indicated
ring, never interpreted as convolution powers. -/
namespace P203Specs.ClassicalFunctions

abbrev one : ArithmeticFunction ℕ := ArithmeticFunction.zeta
abbrev idK (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.pow k
noncomputable abbrev log : ArithmeticFunction ℝ := ArithmeticFunction.log
abbrev mu : ArithmeticFunction ℤ := ArithmeticFunction.moebius
def phi : ArithmeticFunction ℕ := ⟨Nat.totient, rfl⟩
def tau : ArithmeticFunction ℕ := ⟨fun n => n.divisors.card, by simp⟩
abbrev sigma (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.sigma k
noncomputable abbrev vonMangoldt : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt

/-- The elementary functions, divisor sums, and both descriptions of totient
agree with the source on every positive input, including one. -/
def FunctionValues : Prop :=
  ∀ n : ℕ+,
    one n = 1 ∧
    (∀ k : ℕ, idK k n = (n : ℕ) ^ k) ∧
    log n = Real.log (n : ℝ) ∧
    phi n = Ch02.totient n ∧
    phi n = ((Finset.Icc 1 (n : ℕ)).filter (fun a => Nat.Coprime a n)).card ∧
    tau n = (n : ℕ).divisors.card ∧
    (∀ k : ℕ, sigma k n = ∑ d ∈ (n : ℕ).divisors, d ^ k)

/-- The exponent counts distinct primes. The second clause explicitly
identifies the zero case with the existence of a prime square divisor. -/
def MobiusDefinition : Prop :=
  (∀ n : ℕ+, mu n =
    if Squarefree (n : ℕ) then (-1 : ℤ) ^ (n : ℕ).primeFactors.card else 0) ∧
  (∀ n : ℕ+, mu n = 0 ↔ ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ (n : ℕ))

def DivisorConvolutions : Prop :=
  tau = one * one ∧ ∀ k : ℕ, sigma k = one * idK k

/-- Explicit natural-to-integer coefficient maps for the convolution ring. -/
def IntegerConvolutions : Prop :=
  (tau : ArithmeticFunction ℤ) = (one : ArithmeticFunction ℤ) * one ∧
  ∀ k : ℕ, (sigma k : ArithmeticFunction ℤ) =
    (one : ArithmeticFunction ℤ) * (idK k : ArithmeticFunction ℤ)

/-- The same identities in C01's literal positive-divisor convolution. -/
def PositiveConvolutions : Prop :=
  restrictPositive (tau : ArithmeticFunction ℤ) =
    positiveConvolution (restrictPositive (one : ArithmeticFunction ℤ))
      (restrictPositive (one : ArithmeticFunction ℤ)) ∧
  ∀ k : ℕ, restrictPositive (sigma k : ArithmeticFunction ℤ) =
    positiveConvolution (restrictPositive (one : ArithmeticFunction ℤ))
      (restrictPositive (idK k : ArithmeticFunction ℤ))

def Multiplicativity : Prop :=
  mu.IsMultiplicative ∧ phi.IsMultiplicative ∧ tau.IsMultiplicative ∧
    ∀ k : ℕ, (sigma k).IsMultiplicative

def PrimePowerValues : Prop :=
  ∀ p : ℕ, p.Prime → ∀ j : ℕ, 1 ≤ j →
    mu (p ^ j) = (if j = 1 then -1 else 0) ∧
    phi (p ^ j) = p ^ j - p ^ (j - 1) ∧
    tau (p ^ j) = j + 1 ∧
    ∀ k : ℕ, sigma k (p ^ j) = ∑ i ∈ Finset.range (j + 1), p ^ (i * k)

def SigmaZero : Prop := sigma 0 = tau

def ValuesAtOne : Prop :=
  mu 1 = 1 ∧ phi 1 = 1 ∧ tau 1 = 1 ∧ (∀ k : ℕ, sigma k 1 = 1) ∧
    vonMangoldt 1 = 0

/-- Every positive prime power has the prescribed value, and all other
positive inputs have value zero. This includes n=1. -/
def VonMangoldtDefinition : Prop :=
  (∀ p : ℕ, p.Prime → ∀ j : ℕ, 1 ≤ j →
    vonMangoldt (p ^ j) = Real.log (p : ℝ)) ∧
  (∀ n : ℕ+, (¬ ∃ p j : ℕ, p.Prime ∧ 1 ≤ j ∧ p ^ j = (n : ℕ)) →
    vonMangoldt n = 0)

def VonMangoldtConvolution : Prop :=
  (one : ArithmeticFunction ℝ) * vonMangoldt = log

def PositiveVonMangoldtConvolution : Prop :=
  positiveConvolution (restrictPositive (one : ArithmeticFunction ℝ))
    (restrictPositive vonMangoldt) = restrictPositive log

end P203Specs.ClassicalFunctions
