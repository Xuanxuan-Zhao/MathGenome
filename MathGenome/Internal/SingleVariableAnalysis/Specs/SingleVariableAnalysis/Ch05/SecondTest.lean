import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.DerivativeSignTest
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specifications for paper.tex:876–887, K03.05.second_test.
The positive radius expresses differentiability on a full neighborhood of the
interior point. Differentiability of `deriv f` is required only at that point;
continuity or existence of the second derivative elsewhere is not assumed.
Strict extrema use the same punctured-neighborhood inequalities as the first
derivative sign test. The examples explicitly include both derivative values.
-/

namespace Specs.SingleVariableAnalysis.Ch05.SecondTest

def secondDerivativeStrictMinimum : Prop :=
  ∀ (f : ℝ → ℝ) (a r : ℝ), 0 < r →
    (∀ x : ℝ, |x - a| < r → DifferentiableAt ℝ f x) →
    DifferentiableAt ℝ (deriv f) a → deriv f a = 0 →
    0 < deriv (deriv f) a →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f a < f x

def secondDerivativeStrictMaximum : Prop :=
  ∀ (f : ℝ → ℝ) (a r : ℝ), 0 < r →
    (∀ x : ℝ, |x - a| < r → DifferentiableAt ℝ f x) →
    DifferentiableAt ℝ (deriv f) a → deriv f a = 0 →
    deriv (deriv f) a < 0 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f x < f a

def quarticZeroSecondDerivativeMinimum : Prop :=
  HasDerivAt (fun x : ℝ => x ^ 4) 0 0 ∧
    HasDerivAt (deriv (fun x : ℝ => x ^ 4)) 0 0 ∧
    deriv (fun x : ℝ => x ^ 4) 0 = 0 ∧
    deriv (deriv (fun x : ℝ => x ^ 4)) 0 = 0 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x| → |x| < δ →
      (0 : ℝ) ^ 4 < x ^ 4

def negativeQuarticZeroSecondDerivativeMaximum : Prop :=
  HasDerivAt (fun x : ℝ => -(x ^ 4)) 0 0 ∧
    HasDerivAt (deriv (fun x : ℝ => -(x ^ 4))) 0 0 ∧
    deriv (fun x : ℝ => -(x ^ 4)) 0 = 0 ∧
    deriv (deriv (fun x : ℝ => -(x ^ 4))) 0 = 0 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x| → |x| < δ →
      -(x ^ 4) < -((0 : ℝ) ^ 4)

def cubicZeroSecondDerivativeNoExtremum : Prop :=
  HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧
    HasDerivAt (deriv (fun x : ℝ => x ^ 3)) 0 0 ∧
    deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧
    deriv (deriv (fun x : ℝ => x ^ 3)) 0 = 0 ∧
    ¬ IsLocalMax (fun x : ℝ => x ^ 3) 0 ∧
    ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0

end Specs.SingleVariableAnalysis.Ch05.SecondTest
