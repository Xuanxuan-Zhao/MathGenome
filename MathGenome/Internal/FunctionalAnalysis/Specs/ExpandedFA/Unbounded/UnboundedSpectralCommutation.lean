import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem

/-! Independent statement of paper.tex, fa2:p3:unbounded-commutation.
All products below are actual partial-map products, including their domains.
Complex-valued Borel functions are finite everywhere; no boundedness,
separability, or nonempty-resolvent assumption is imposed. -/
noncomputable section
namespace ExpandedFA.Unbounded.UnboundedSpectralCommutation
open MeasurableSpectralCalculus OperatorDomainsSpec HilbertAdjointSpec
universe u

/-- A bounded operator regarded as an everywhere-defined partial linear map. -/
def boundedOperator {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (B : H →L[ℂ] H) : Operator ℂ H H := B.toLinearMap.toPMap ⊤

namespace Spec
/-- Both assertions for every spectral resolution of the given normal operator.
The upstream spectral theorem supplies such a resolution and its uniqueness. -/
def SpectralCommutation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : Operator ℂ H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    ∀ B : H →L[ℂ] H,
      productValue (boundedOperator B) N ≤ productValue N (boundedOperator B) →
      productValue (boundedOperator B) (adjointValue N) ≤
        productValue (adjointValue N) (boundedOperator B) →
      ∀ (E : SpectralMeasure.ProjectionValuedMeasure ℂ H) (C : BoundedRealization E),
        measurableIntegral C (fun z : ℂ => z) = N →
        (∀ S : Set ℂ, MeasurableSet S → Commute B (E S)) ∧
        ∀ f : ℂ → ℂ, Measurable f →
          (∀ x ∈ (measurableIntegral C f).domain,
            B x ∈ (measurableIntegral C f).domain) ∧
          productValue (boundedOperator B) (measurableIntegral C f) ≤
            productValue (measurableIntegral C f) (boundedOperator B)
end Spec
end ExpandedFA.Unbounded.UnboundedSpectralCommutation
