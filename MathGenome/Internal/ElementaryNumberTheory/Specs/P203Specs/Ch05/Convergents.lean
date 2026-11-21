import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ContinuedFractionAlgorithm
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational

/-! Integer continuants and the conclusions assigned from paper.tex §nt:E03,
lines 2138–2159 and 2170–2197. The two exact error bounds and convergence
are allocated separately. Natural algorithm indices are cast to integers
in the signed numerator/denominator functions, so `n - 1` at zero is -1.
-/
namespace P203Specs

/-- Index `k` holds `(p_{k-1},q_{k-1})`. After the algorithm stops this
auxiliary pair is held constant, exactly as in Mathlib; no new digit is assigned. -/
noncomputable def integerContinuants (x : ℝ) : ℕ → GenContFract.Pair ℤ
  | 0 => ⟨1, 0⟩
  | 1 => ⟨⌊x⌋, 1⟩
  | n + 2 =>
    match partialQuotient x (n + 1) with
    | none => integerContinuants x (n + 1)
    | some a =>
      ⟨a * (integerContinuants x (n + 1)).a + (integerContinuants x n).a,
       a * (integerContinuants x (n + 1)).b + (integerContinuants x n).b⟩

/-- Signed indexing incorporates `p₋₂=0` and `p₋₁=1` explicitly.
Only indices at least -2 are used in the stated conclusions. -/
noncomputable def convergentNumerator (x : ℝ) (n : ℤ) : ℤ :=
  if n = -2 then 0 else (integerContinuants x (n + 1).toNat).a

/-- Signed indexing incorporates `q₋₂=1` and `q₋₁=0` explicitly. -/
noncomputable def convergentDenominator (x : ℝ) (n : ℤ) : ℤ :=
  if n = -2 then 1 else (integerContinuants x (n + 1).toNat).b

def IntegerContinuantsType := ℝ → ℕ → GenContFract.Pair ℤ
def ConvergentNumeratorType := ℝ → ℤ → ℤ
def ConvergentDenominatorType := ℝ → ℤ → ℤ

def ConvergentInitial : Prop :=
  ∀ x : ℝ, convergentNumerator x (-2) = 0 ∧ convergentNumerator x (-1) = 1 ∧
    convergentDenominator x (-2) = 1 ∧ convergentDenominator x (-1) = 0

def ConvergentRecurrences : Prop :=
  ∀ (x : ℝ) (n : ℕ) (a : ℤ), partialQuotient x n = some a →
    convergentNumerator x n = a * convergentNumerator x ((n : ℤ) - 1) +
      convergentNumerator x ((n : ℤ) - 2) ∧
    convergentDenominator x n = a * convergentDenominator x ((n : ℤ) - 1) +
      convergentDenominator x ((n : ℤ) - 2)

/-- The full defined finite prefix exists and evaluates to the indicated ratio.
This includes the one-digit prefix and the final index of rational expansions. -/
def ConvergentFiniteEvaluation : Prop :=
  ∀ (x : ℝ) (n : ℕ), partialQuotient x n ≠ none →
    ∃ (a : ℤ) (t : List ℤ), t.length = n ∧
      (∀ j ≤ n, partialQuotient x j = (a :: t)[j]?) ∧
      (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ) =
        finiteContinuedFraction a t

def ConvergentDeterminant : Prop :=
  ∀ (x : ℝ) (n : ℕ), partialQuotient x n ≠ none →
    convergentNumerator x n * convergentDenominator x ((n : ℤ) - 1) -
      convergentNumerator x ((n : ℤ) - 1) * convergentDenominator x n = (-1) ^ (n + 1)

def ConvergentReduced : Prop :=
  ∀ (x : ℝ) (n : ℕ), partialQuotient x n ≠ none →
    0 < convergentDenominator x n ∧
      Int.gcd (convergentNumerator x n) (convergentDenominator x n) = 1

def ConvergentDenominatorGrowth : Prop :=
  (∀ x : ℝ, convergentDenominator x 0 = 1) ∧
  (∀ (x : ℝ) (a : ℤ), partialQuotient x 1 = some a →
    convergentDenominator x 1 = a) ∧
  (∀ (x : ℝ) (n : ℕ), 1 ≤ n → partialQuotient x (n + 1) ≠ none →
    convergentDenominator x n < convergentDenominator x (n + 1))

/-- Casts identify the integer recurrences with Mathlib's numerators and
denominators, as well as both standard notions of convergent, at the same index. -/
def ConvergentMathlibBridge : Prop :=
  ∀ (x : ℝ) (n : ℕ),
    (convergentNumerator x n : ℝ) = (simpleContinuedFraction x).nums n ∧
    (convergentDenominator x n : ℝ) = (simpleContinuedFraction x).dens n ∧
    (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ) =
      (simpleContinuedFraction x).convs n ∧
    (convergentNumerator x n : ℝ) / (convergentDenominator x n : ℝ) =
      (Real.convergent x n : ℝ)

/-- Both source tail identities, with existence of the next complete quotient
and positivity (and hence nonvanishing) of the common denominator. -/
def ConvergentExactTail : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ n : ℕ,
    ∃ α : ℝ, completeQuotient x (n + 1) = some α ∧
      0 < (convergentDenominator x n : ℝ) * α +
        (convergentDenominator x ((n : ℤ) - 1) : ℝ) ∧
      (convergentDenominator x n : ℝ) * α +
        (convergentDenominator x ((n : ℤ) - 1) : ℝ) ≠ 0 ∧
      x = ((convergentNumerator x n : ℝ) * α +
        (convergentNumerator x ((n : ℤ) - 1) : ℝ)) /
        ((convergentDenominator x n : ℝ) * α +
        (convergentDenominator x ((n : ℤ) - 1) : ℝ)) ∧
      (convergentDenominator x n : ℝ) * x - (convergentNumerator x n : ℝ) =
        (-1) ^ n / ((convergentDenominator x n : ℝ) * α +
        (convergentDenominator x ((n : ℤ) - 1) : ℝ))

end P203Specs
