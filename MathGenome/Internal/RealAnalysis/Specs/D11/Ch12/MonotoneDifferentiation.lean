import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for paper.tex:4089–4120.

The derivative is that of the original point values. No continuity, chosen
Stieltjes representative, or absolute continuity is assumed. The ambient
presentation is supplemented by a statement for every function on `Icc a b`.
All derivatives are finite real numbers. Borel measurability of the chosen
zero extension is stronger than Lebesgue measurability; its integrals against
native real volume are the usual Lebesgue integrals of this Borel function.
-/

open Set MeasureTheory

namespace D11.Ch12.MonotoneDifferentiation

/-- The ordinary derivative on the open interval, zero elsewhere. The library's
`deriv` is zero at points where the function is not differentiable. -/
noncomputable def zeroExtendedDerivative (F : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (deriv F)

/-- Includes a measurable null exceptional set, a genuine derivative of the
original function at every remaining interior point, the zero convention,
everywhere nonnegativity, absolute integrability, and the exact bound. -/
def DifferentiationConclusion (F : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ N : Set ℝ, MeasurableSet N ∧ N ⊆ Ioo a b ∧ volume N = 0 ∧
    (∀ x ∈ Ioo a b, x ∉ N → HasDerivAt F (zeroExtendedDerivative F a b x) x) ∧
    (∀ x ∈ N, zeroExtendedDerivative F a b x = 0) ∧
    Measurable (zeroExtendedDerivative F a b) ∧
    (∀ x, 0 ≤ zeroExtendedDerivative F a b x) ∧
    Integrable (zeroExtendedDerivative F a b) volume ∧
    (∫ x in a..b, zeroExtendedDerivative F a b x) ≤ F b - F a

end D11.Ch12.MonotoneDifferentiation

namespace Specs.D11.Ch12.MonotoneDifferentiation
open _root_.D11.Ch12.MonotoneDifferentiation

def monotone_differentiation_type : Prop :=
  ∀ (F : ℝ → ℝ) {a b : ℝ}, a < b → MonotoneOn F (Icc a b) →
    DifferentiationConclusion F a b

/-- All original interval-domain functions are covered. The extension agrees
at every point, including the endpoints and any discontinuity. Differentiation
at an interior point depends only on these interval values. -/
def interval_domain_type : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (F : Icc a b → ℝ), Monotone F →
    ∃ G : ℝ → ℝ, (∀ x : Icc a b, G x = F x) ∧
      DifferentiationConclusion G a b

end Specs.D11.Ch12.MonotoneDifferentiation
