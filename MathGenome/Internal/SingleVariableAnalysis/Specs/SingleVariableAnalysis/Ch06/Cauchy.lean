import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial

/-!
Independent specification of K03.06.cauchy, paper.tex:2792–2804, with the
hypotheses of K03.06.lagrange (2778–2790).

The closed derivative family is the upstream representation of C^n on a
compact interval. Its values at a are the continuous, available one-sided
Taylor coefficients. Thus the finite sum in `cauchy_remainder` is exactly
T_n(f,a)(x), even when f's arbitrary ambient extension is not differentiable
at a. Only differentiability of the nth derivative on the open segment is
required at the next order; its derivative need not be continuous.

The second statement specializes to ambient derivatives when these exist
through order n at the endpoints, and uses the already fixed TaylorRemainder.
Both statements quantify over every natural n, including zero, and use min/max
to include both orientations with the signed factor x-a.
-/
namespace Specs.SingleVariableAnalysis.Ch06.Cauchy
open Set
open Specs.SingleVariableAnalysis.Ch04

noncomputable def cauchy_remainder : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) (D : ℕ → ℝ → ℝ), a ≠ x →
    Higher.closedDerivativeFamilyValue n f (min a x) (max a x) D →
    (∀ t ∈ Ioo (min a x) (max a x),
      DifferentiableAt ℝ (Higher.realIteratedDerivativeValue n f) t) →
    ∃ ξ ∈ Ioo (min a x) (max a x),
      f x - ∑ k ∈ Finset.range (n + 1), (D k a / (k.factorial : ℝ)) * (x-a)^k =
        Higher.realIteratedDerivativeValue (n + 1) f ξ * (x-ξ)^n * (x-a) /
          (n.factorial : ℝ)

noncomputable def cauchy_remainder_taylor : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a x : ℝ), a ≠ x →
    Higher.ckOnValue n f (Icc (min a x) (max a x)) →
    (∀ t ∈ Ioo (min a x) (max a x),
      DifferentiableAt ℝ (Higher.realIteratedDerivativeValue n f) t) →
    ∃ ξ ∈ Ioo (min a x) (max a x),
      TaylorPolynomial.taylorRemainderValue f n a x =
        Higher.realIteratedDerivativeValue (n + 1) f ξ * (x-ξ)^n * (x-a) /
          (n.factorial : ℝ)

end Specs.SingleVariableAnalysis.Ch06.Cauchy
