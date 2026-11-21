import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.RCLike.Basic

/-!
Independent specification of K03.06.uniform_bound (paper.tex:2817–2830).
The supplied continuous derivative family is the upstream compact C^n
interface, including continuous one-sided endpoint values. Only the next
interior derivative must exist, and it need not be continuous. The same real
M is used for all a,x in the interval; n is arbitrary, including zero.
RCLike includes the canonical real and complex scalars, with real derivatives.
No positivity assumption on M or strict interval hypothesis is added.
-/
namespace Specs.SingleVariableAnalysis.Ch06.UniformBound
open Set
open scoped BigOperators
universe u

def uniformTaylorBound : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (u v M : ℝ)
    (D : ℕ → ℝ → K),
    Ch04.Higher.closedDerivativeFamilyValue n f u v D →
    (∀ t ∈ Ioo u v,
      DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue n f) t) →
    (∀ t ∈ Ioo u v,
      ‖Ch04.Higher.realIteratedDerivativeValue (n+1) f t‖ ≤ M) →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
      ‖f x - ∑ k ∈ Finset.range (n+1),
        D k a / (k.factorial : K) * (algebraMap ℝ K (x-a))^k‖ ≤
        M / ((n+1).factorial : ℝ) * |x-a|^(n+1)

/-- The same source bound using the canonical within Taylor polynomial.
On nondegenerate intervals its coefficients are exactly the continuous
one-sided endpoint values. On a singleton, evaluation at the center is f a. -/
def uniformTaylorBoundWithin : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (u v M : ℝ),
    Ch04.Higher.ckOnClosedValue n f u v →
    (∀ t ∈ Ioo u v,
      DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue n f) t) →
    (∀ t ∈ Ioo u v,
      ‖Ch04.Higher.realIteratedDerivativeValue (n+1) f t‖ ≤ M) →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
      ‖f x - taylorWithinEval f n (Icc u v) a x‖ ≤
        M / ((n+1).factorial : ℝ) * |x-a|^(n+1)

end Specs.SingleVariableAnalysis.Ch06.UniformBound
