import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specifications for K03.05.rolle, paper.tex:807–814.
An ambient real function represents a function on [a,b]; no condition is
placed on its values outside that interval. Continuity includes both endpoints,
and all differentiability assumptions concern only the open interval.
The derivative-value conclusion ensures an actual finite derivative exists.
The relative version uses the previously specified real increment limits.
No nonconstancy hypothesis is imposed; the last statement records the proof's
observation that every interior point works for a function constant on [a,b].
-/

namespace Specs.SingleVariableAnalysis.Ch05.Rolle

open Set

def rolleHasDerivAt : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) → f a = f b →
      ∃ c ∈ Ioo a b, HasDerivAt f 0 c

def rolleDeriv : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) → f a = f b →
      ∃ c ∈ Ioo a b, deriv f c = 0

def rolleWithin : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) →
    (∀ x ∈ Ioo a b, ∃ L : ℝ,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f L (Icc a b) x) →
    f a = f b → ∃ c ∈ Ioo a b,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f 0 (Icc a b) c

def rolleConstant : Prop :=
  ∀ (f : ℝ → ℝ) (a b k : ℝ), (∀ x ∈ Icc a b, f x = k) →
    ∀ c ∈ Ioo a b, HasDerivAt f 0 c

end Specs.SingleVariableAnalysis.Ch05.Rolle
