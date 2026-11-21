import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
import Mathlib.Analysis.Calculus.Taylor

/-!
Independent specifications for K03.06.lagrange, paper.tex:2781–2792.
The compact derivative family is the upstream C^n interface: its continuous
values at the endpoints are the available one-sided derivatives. The finite
sum below is exactly T_n with those coefficients, rather than derivatives of
an arbitrary extension outside the segment. The additional differentiability
hypothesis concerns only the nth derivative at interior points; continuity of
the (n+1)st derivative is not assumed. Unordered intervals retain x<a and the
signed power; n is any natural number, including zero. All functions are real.
-/
namespace Specs.SingleVariableAnalysis.Ch06.Lagrange
open Set
open scoped BigOperators

def endpointTaylor_eq_within : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) (D : ℕ → ℝ → ℝ), a ≠ x →
    Ch04.Higher.closedDerivativeFamilyValue n f (min a x) (max a x) D →
    taylorWithinEval f n (uIcc a x) a x =
      ∑ k ∈ Finset.range (n+1), D k a / (k.factorial : ℝ) * (x-a)^k

def lagrangeRemainderWithin : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ), a ≠ x →
    Ch04.Higher.ckOnClosedValue n f (min a x) (max a x) →
    (∀ t ∈ uIoo a x, DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue n f) t) →
    ∃ ξ ∈ uIoo a x, f x - taylorWithinEval f n (uIcc a x) a x =
      Ch04.Higher.realIteratedDerivativeValue (n+1) f ξ * (x-a)^(n+1) /
        ((n+1).factorial : ℝ)

def lagrangeRemainder : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) (D : ℕ → ℝ → ℝ), a ≠ x →
    Ch04.Higher.closedDerivativeFamilyValue n f (min a x) (max a x) D →
    (∀ t ∈ uIoo a x, DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue n f) t) →
    ∃ ξ ∈ uIoo a x,
      f x - (∑ k ∈ Finset.range (n+1), D k a / (k.factorial : ℝ) * (x-a)^k) =
        Ch04.Higher.realIteratedDerivativeValue (n+1) f ξ * (x-a)^(n+1) /
          ((n+1).factorial : ℝ)

/-- Compatibility with the already defined TaylorRemainder whenever its ambient
jet agrees with the endpoint jet. This is a bridge, not the general theorem's
regularity hypothesis. -/
def lagrangeRemainderAmbient : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ), a ≠ x →
    Ch04.Higher.ckOnClosedValue n f (min a x) (max a x) →
    (∀ t ∈ uIoo a x, DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue n f) t) →
    (∀ k ≤ n, iteratedDerivWithin k f (uIcc a x) a =
      Ch04.Higher.realIteratedDerivativeValue k f a) →
    ∃ ξ ∈ uIoo a x, Ch06.TaylorPolynomial.taylorRemainderValue f n a x =
      Ch04.Higher.realIteratedDerivativeValue (n+1) f ξ * (x-a)^(n+1) /
        ((n+1).factorial : ℝ)

def lagrangeRemainderZero : Prop :=
  ∀ (f : ℝ → ℝ) (a x : ℝ), a ≠ x → ContinuousOn f (uIcc a x) →
    (∀ t ∈ uIoo a x, DifferentiableAt ℝ f t) →
    ∃ ξ ∈ uIoo a x, f x - f a = deriv f ξ * (x-a)

end Specs.SingleVariableAnalysis.Ch06.Lagrange
