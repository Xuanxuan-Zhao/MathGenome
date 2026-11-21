import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specifications for K03.05.convex_derivative, paper.tex:931–941.
An open interval is an open order-connected real set; boundedness and finite
endpoints are not required. Ambient functions represent functions on that set.
Differentiability is assumed only at its points, so `deriv` here is always an
actual finite real derivative. Twice differentiable means differentiability
of both `f` and its first derivative, with no continuity assumption on `f''`.
The convexity predicate is precisely the upstream one-parameter definition.
-/

namespace Specs.SingleVariableAnalysis.Ch05.ConvexDerivative

open Set

def convexDerivativeSecantBounds : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected → ∀ (f : ℝ → ℝ),
    (∀ x ∈ I, DifferentiableAt ℝ f x) →
    Convexity.convexFunctionOnValue I f →
    ∀ x ∈ I, ∀ y ∈ I, x < y →
      deriv f x ≤ (f y - f x) / (y - x) ∧
        (f y - f x) / (y - x) ≤ deriv f y

def convexIffMonotoneDerivative : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected → ∀ (f : ℝ → ℝ),
    (∀ x ∈ I, DifferentiableAt ℝ f x) →
    (Convexity.convexFunctionOnValue I f ↔ MonotoneOn (deriv f) I)

def convexIffTangentSupport : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected → ∀ (f : ℝ → ℝ),
    (∀ x ∈ I, DifferentiableAt ℝ f x) →
    (Convexity.convexFunctionOnValue I f ↔
      ∀ x ∈ I, ∀ y ∈ I, f x + deriv f x * (y - x) ≤ f y)

def convexIffSecondDerivativeNonnegative : Prop :=
  ∀ (I : Set ℝ), IsOpen I → I.OrdConnected → ∀ (f : ℝ → ℝ),
    (∀ x ∈ I, DifferentiableAt ℝ f x) →
    (∀ x ∈ I, DifferentiableAt ℝ (deriv f) x) →
    (Convexity.convexFunctionOnValue I f ↔ ∀ x ∈ I, 0 ≤ deriv (deriv f) x)

end Specs.SingleVariableAnalysis.Ch05.ConvexDerivative
