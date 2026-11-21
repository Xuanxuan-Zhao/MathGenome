import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.FlatDecay
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Independent specification of K03.06.smooth_flat, paper.tex:2871–2886.
The function is the canonical zero extension already constructed in FlatDecay.
The polynomials below retain the source's full recurrence, including P₀ = 1.
Derivatives are iterated real-variable derivatives, at every natural order. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch06.SmoothFlat

open Polynomial

def derivativePolynomialType := ℕ → Polynomial ℝ

def derivativePolynomialValue : derivativePolynomialType
  | 0 => 1
  | j + 1 => -X ^ 2 * (derivativePolynomialValue j).derivative +
      C 2 * X ^ 3 * derivativePolynomialValue j

def polynomialZero : Prop := derivativePolynomialValue 0 = 1

def polynomialSucc : Prop := ∀ j : ℕ,
  derivativePolynomialValue (j + 1) = -X ^ 2 * (derivativePolynomialValue j).derivative +
    C 2 * X ^ 3 * derivativePolynomialValue j

def smooth : Prop :=
  Ch04.Higher.smoothOnValue FlatDecay.flatExponentialValue Set.univ

def derivativesAtZero : Prop := ∀ j : ℕ,
  Ch04.Higher.realIteratedDerivativeValue j FlatDecay.flatExponentialValue 0 = 0

def positiveOffZero : Prop := ∀ x : ℝ, x ≠ 0 → 0 < FlatDecay.flatExponentialValue x

def derivativeRepresentation : Prop := ∀ (j : ℕ) (x : ℝ), x ≠ 0 →
  Ch04.Higher.realIteratedDerivativeValue j FlatDecay.flatExponentialValue x =
    (derivativePolynomialValue j).eval (1 / x) *
      Ch07.ExpConstruction.realSeriesExpValue (-1 / x ^ 2)

end Specs.SingleVariableAnalysis.Ch06.SmoothFlat
