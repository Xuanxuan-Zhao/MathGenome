import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for `paper.tex:4121`, Differentiating BV functions.
The finite dimensional real vector space generality includes both scalar fields
with their usual norms. Variation is the classical strict-partition supremum.
No regularity of the original point values beyond BV is assumed. -/

open Set MeasureTheory

namespace D11.Ch12.BvDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordinary derivative of the original function on the interior, zero outside.
The totalized derivative is zero at every nondifferentiability point. -/
noncomputable def zeroExtendedDerivative (F : ℝ → E) (a b : ℝ) : ℝ → E :=
  (Ioo a b).indicator (deriv F)

/-- Finite a.e. differentiability, a measurable integrable zero extension, and
its sharp norm bound. This asserts no integral reconstruction of `F`. -/
def DifferentiationConclusion [MeasurableSpace E] (F : ℝ → E) (a b : ℝ) : Prop :=
  ∃ N : Set ℝ, MeasurableSet N ∧ N ⊆ Ioo a b ∧ volume N = 0 ∧
    (∀ x ∈ Ioo a b, x ∉ N → HasDerivAt F (zeroExtendedDerivative F a b x) x) ∧
    (∀ x ∈ N, zeroExtendedDerivative F a b x = 0) ∧
    Measurable (zeroExtendedDerivative F a b) ∧
    Integrable (zeroExtendedDerivative F a b) volume ∧
    (∫ x in a..b, ‖zeroExtendedDerivative F a b x‖) ≤
      (Specs.D11.Ch12.variation_value F a b).toReal

end D11.Ch12.BvDerivative

namespace Specs.D11.Ch12.BvDerivative
open _root_.D11.Ch12.BvDerivative

def bv_differentiation_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : ℝ → E) {a b : ℝ}, a < b → BV_value F a b →
    DifferentiationConclusion F a b

/-- Every function on the actual closed interval is covered by an ambient
extension agreeing at every point; no extension regularity is hypothesized. -/
def interval_domain_type : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (a b : ℝ), a < b → ∀ (F : Icc a b → E), eVariationOn F univ < ⊤ →
    ∃ G : ℝ → E, (∀ x : Icc a b, G x = F x) ∧
      (variation_value G a b = eVariationOn F univ) ∧
      DifferentiationConclusion G a b

end Specs.D11.Ch12.BvDerivative
