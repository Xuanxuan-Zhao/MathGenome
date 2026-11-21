import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent full statements of the finite scalar RN theorem,
`paper.tex:4876–4891`. The reference alone is sigma-finite. SignedMeasure
and ComplexMeasure are the shared countably additive scalar measures; their
finite variation is automatic, rather than an extra hypothesis. The witnesses
are measurable on the original sigma-algebra and absolutely integrable.
Uniqueness is expressly almost everywhere, thus uniqueness of the L¹ class.
The nonnegative integral of the norm expresses the variation identity. -/

open Set MeasureTheory
open scoped ENNReal
universe u

namespace Specs.D11.Ch15.RNSignedComplex

def rn_signed : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : SignedMeasure X), AbsoluteContinuity.scalarAbsolutelyContinuous_value ν μ →
    ∃ h : X → ℝ, Measurable h ∧ Integrable h μ ∧
      (∀ E, MeasurableSet E → ν E = ∫ x in E, h x ∂μ) ∧
      (∀ E, MeasurableSet E → Ch14.TotalVariation.totalVariation_value ν E =
        ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ) ∧
      ∀ k : X → ℝ, Integrable k μ →
        (∀ E, MeasurableSet E → ν E = ∫ x in E, k x ∂μ) → h =ᵐ[μ] k

def rn_complex : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : ComplexMeasure X), AbsoluteContinuity.scalarAbsolutelyContinuous_value ν μ →
    ∃ h : X → ℂ, Measurable h ∧ Integrable h μ ∧
      (∀ E, MeasurableSet E → ν E = ∫ x in E, h x ∂μ) ∧
      (∀ E, MeasurableSet E → Ch14.TotalVariation.totalVariation_value ν E =
        ∫⁻ x in E, ENNReal.ofReal ‖h x‖ ∂μ) ∧
      ∀ k : X → ℂ, Integrable k μ →
        (∀ E, MeasurableSet E → ν E = ∫ x in E, k x ∂μ) → h =ᵐ[μ] k

end Specs.D11.Ch15.RNSignedComplex
