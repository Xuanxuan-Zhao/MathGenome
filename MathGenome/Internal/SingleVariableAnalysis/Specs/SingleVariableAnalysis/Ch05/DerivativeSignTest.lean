import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Lagrange
import Mathlib.Topology.Order.LocalExtr

/-!
Independent specifications for K03.05.derivative_sign_test, paper.tex:868–876.
An ambient real function represents the function near its interior point `a`.
The positive radius supplies a full neighborhood; no derivative at `a` is
assumed. Continuity at all other points of this neighborhood follows from
the stated punctured differentiability. Strict extrema are expressed by
strict inequalities at every sufficiently close point distinct from `a`.
-/

namespace Specs.SingleVariableAnalysis.Ch05.DerivativeSignTest

open Set

def firstDerivativeStrictMaximum : Prop :=
  ∀ (f : ℝ → ℝ) (a r : ℝ), 0 < r → ContinuousAt f a →
    (∀ x : ℝ, 0 < |x - a| → |x - a| < r → DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo (a - r) a, 0 < deriv f x) →
    (∀ x ∈ Ioo a (a + r), deriv f x < 0) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f x < f a

def firstDerivativeStrictMinimum : Prop :=
  ∀ (f : ℝ → ℝ) (a r : ℝ), 0 < r → ContinuousAt f a →
    (∀ x : ℝ, 0 < |x - a| → |x - a| < r → DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo (a - r) a, deriv f x < 0) →
    (∀ x ∈ Ioo a (a + r), 0 < deriv f x) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f a < f x

/-- A stationary point need not even be a non-strict local extremum. -/
def cubicStationaryNoExtremum : Prop :=
  HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧
    deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧
    ¬ IsLocalMax (fun x : ℝ => x ^ 3) 0 ∧
    ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0

end Specs.SingleVariableAnalysis.Ch05.DerivativeSignTest
