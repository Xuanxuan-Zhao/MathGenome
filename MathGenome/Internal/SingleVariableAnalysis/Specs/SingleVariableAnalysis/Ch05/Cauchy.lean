import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specifications for K03.05.cauchy, paper.tex:824–839.
An ambient function represents a real function on [a,b], with arbitrary
values outside that interval. Continuity includes both endpoints, while
differentiability is required only in the open interval. No continuity
of either derivative, or nonvanishing derivative of f, is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Cauchy

open Set

def cauchyMeanValue : Prop :=
  ∀ (f g : ℝ → ℝ) (a b : ℝ), a < b →
    ContinuousOn f (Icc a b) → ContinuousOn g (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) →
    ∃ c ∈ Ioo a b,
      (f b - f a) * deriv g c = (g b - g a) * deriv f c

def cauchyEndpointNe : Prop :=
  ∀ (g : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn g (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) →
    (∀ x ∈ Ioo a b, deriv g x ≠ 0) → g b ≠ g a

/-- The same interior point witnesses the cross-product and ratio identities;
both denominator conditions are part of the conclusion. -/
def cauchyMeanValueRatio : Prop :=
  ∀ (f g : ℝ → ℝ) (a b : ℝ), a < b →
    ContinuousOn f (Icc a b) → ContinuousOn g (Icc a b) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) →
    (∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) →
    (∀ x ∈ Ioo a b, deriv g x ≠ 0) →
    g b ≠ g a ∧ ∃ c ∈ Ioo a b, deriv g c ≠ 0 ∧
      (f b - f a) * deriv g c = (g b - g a) * deriv f c ∧
      (f b - f a) / (g b - g a) = deriv f c / deriv g c

end Specs.SingleVariableAnalysis.Ch05.Cauchy
