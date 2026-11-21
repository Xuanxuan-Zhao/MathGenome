import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specifications for K03.05.mean_inequality, paper.tex:835–844.
The variable and all increments are real. Only interior differentiability is
required; continuity includes both endpoints. The norm on ℂ is its modulus.
Ambient functions represent functions on the interval, with no restrictions
outside it. The relative formulations use the upstream interval predicates.
Neither the hypotheses nor the conclusions exclude a zero endpoint increment.
-/

namespace Specs.SingleVariableAnalysis.Ch05.MeanInequality

open Set

def realMeanInequality : Prop :=
  ∀ (f : ℝ → ℝ) (x y M : ℝ), x < y → 0 ≤ M →
    ContinuousOn f (Icc x y) →
    (∀ t ∈ Ioo x y, DifferentiableAt ℝ f t) →
    (∀ t ∈ Ioo x y, |deriv f t| ≤ M) →
    |f y - f x| ≤ M * (y - x)

def complexMeanInequality : Prop :=
  ∀ (f : ℝ → ℂ) (x y M : ℝ), x < y → 0 ≤ M →
    ContinuousOn f (Icc x y) →
    (∀ t ∈ Ioo x y, DifferentiableAt ℝ f t) →
    (∀ t ∈ Ioo x y, ‖deriv f t‖ ≤ M) →
    ‖f y - f x‖ ≤ M * (y - x)

def realMeanInequalityWithin : Prop :=
  ∀ (f f' : ℝ → ℝ) (x y M : ℝ), x < y → 0 ≤ M →
    Ch03.Continuity.relativeContinuousValue f (Icc x y) →
    (∀ t ∈ Ioo x y,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f (f' t) (Icc x y) t) →
    (∀ t ∈ Ioo x y, |f' t| ≤ M) →
    |f y - f x| ≤ M * (y - x)

def complexMeanInequalityWithin : Prop :=
  ∀ (f f' : ℝ → ℂ) (x y M : ℝ), x < y → 0 ≤ M →
    Ch03.Continuity.relativeContinuousValue f (Icc x y) →
    (∀ t ∈ Ioo x y,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f (f' t) (Icc x y) t) →
    (∀ t ∈ Ioo x y, ‖f' t‖ ≤ M) →
    ‖f y - f x‖ ≤ M * (y - x)

end Specs.SingleVariableAnalysis.Ch05.MeanInequality
