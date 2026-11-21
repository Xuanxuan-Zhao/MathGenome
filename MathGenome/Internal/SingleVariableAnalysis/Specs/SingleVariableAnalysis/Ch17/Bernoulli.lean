import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcSecond
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! K03.17.bernoulli, paper.tex:4404–4417.
Real polynomials, their real-variable derivatives, and the proper Darboux
integral on [0,1]. The canonical rational polynomials are transported to ℝ;
the normalization and its uniqueness are proof obligations below.
The subsequent reflection, endpoint, difference and power-sum identities
are allocated to d03_17_bernoulli_identities.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.Bernoulli
open Polynomial
open Ch08.Integral

abbrev bernoulliPolynomialType := ℕ → Polynomial ℝ
def bernoulliPolynomialValue : bernoulliPolynomialType :=
  fun n => (Polynomial.bernoulli n).map (algebraMap ℚ ℝ)

abbrev bernoulliNumberType := ℕ → ℝ
def bernoulliNumberValue : bernoulliNumberType :=
  fun n => (bernoulliPolynomialValue n).eval 0

/-- A step of the defining recursion, including existence of the proper integral. -/
def normalizedStep (p q : Polynomial ℝ) (n : ℕ) : Prop :=
  derivative p = C ((n : ℝ) + 1) * q ∧
    ∃ h : realIntegrableValue p.eval 0 1, realIntegralValue p.eval h = 0

/-- The formal derivative condition is exactly the ordinary real derivative condition. -/
def normalizedStepIffHasDerivAt : Prop := ∀ (p q : Polynomial ℝ) (n : ℕ),
  normalizedStep p q n ↔
    (∀ x : ℝ, HasDerivAt p.eval (((n : ℝ) + 1) * q.eval x) x) ∧
      ∃ h : realIntegrableValue p.eval 0 1, realIntegralValue p.eval h = 0

abbrev bernoulliRecursionType := (ℕ → Polynomial ℝ) → Prop
def bernoulliRecursionValue : bernoulliRecursionType := fun B =>
  B 0 = 1 ∧ ∀ n, normalizedStep (B (n + 1)) (B n) n

def bernoulliZero : Prop := bernoulliPolynomialValue 0 = 1

def bernoulliDerivative : Prop := ∀ n,
  derivative (bernoulliPolynomialValue (n + 1)) =
    C ((n : ℝ) + 1) * bernoulliPolynomialValue n

def bernoulliHasDerivAt : Prop := ∀ (n : ℕ) (x : ℝ),
  HasDerivAt (bernoulliPolynomialValue (n + 1)).eval
    (((n : ℝ) + 1) * (bernoulliPolynomialValue n).eval x) x

def bernoulliZeroAverage : Prop := ∀ n,
  ∃ h : realIntegrableValue (bernoulliPolynomialValue (n + 1)).eval 0 1,
    realIntegralValue (bernoulliPolynomialValue (n + 1)).eval h = 0

def bernoulliStepUnique : Prop := ∀ n,
  ∃! p : Polynomial ℝ, normalizedStep p (bernoulliPolynomialValue n) n

def bernoulliNormalization : Prop := bernoulliRecursionValue bernoulliPolynomialValue

def bernoulliUniqueSequence : Prop :=
  ∃! B : ℕ → Polynomial ℝ, bernoulliRecursionValue B

def bernoulliNumberCanonical : Prop := ∀ n,
  bernoulliNumberValue n = algebraMap ℚ ℝ (_root_.bernoulli n)

def bernoulliOne : Prop := bernoulliPolynomialValue 1 = X - C (1 / 2)
def bernoulliTwo : Prop :=
  bernoulliPolynomialValue 2 = X ^ 2 - X + C (1 / 6)
def bernoulliFour : Prop :=
  bernoulliPolynomialValue 4 = X ^ 4 - C 2 * X ^ 3 + X ^ 2 - C (1 / 30)
def bernoulliNumbers : Prop :=
  bernoulliNumberValue 0 = 1 ∧ bernoulliNumberValue 1 = -1 / 2 ∧
    bernoulliNumberValue 2 = 1 / 6 ∧ bernoulliNumberValue 4 = -1 / 30

end Specs.SingleVariableAnalysis.Ch17.Bernoulli
