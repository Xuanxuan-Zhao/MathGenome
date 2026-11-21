import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specifications for K03.05.lagrange, paper.tex:815–823.
The function is real-valued, continuous on the entire closed interval, and
differentiable only in its interior. Values outside the interval are arbitrary.
The slope formulation records an actual derivative, while the second statement
is the manuscript's exact mean value equality. The last formulation uses the
previously specified relative continuity and real-increment derivatives.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Lagrange

open Set

def lagrangeHasDerivAt : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
      ∃ c ∈ Ioo a b, HasDerivAt f ((f b - f a) / (b - a)) c

def lagrangeDeriv : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
      ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a)

def lagrangeWithin : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    Ch03.Continuity.relativeContinuousValue f (Icc a b) →
    (∀ x ∈ Ioo a b, ∃ L : ℝ,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f L (Icc a b) x) →
    ∃ c ∈ Ioo a b, ∃ L : ℝ,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f L (Icc a b) c ∧
      f b - f a = L * (b - a)

end Specs.SingleVariableAnalysis.Ch05.Lagrange
