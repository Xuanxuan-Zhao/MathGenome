import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.RadonDisjointCompactLocalization
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LpDualFiniteMeasure

/-! Representation stage of paper.tex:5770–5789.  The measure and domain
are exactly the full Carathéodory extension of the given Borel Radon measure.
The `Lp` carrier is the shared ordinary a.e. quotient, and the scalar pairing
is bilinear, including over the complex numbers. -/
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch20.LocalNullEndpointRepresentative
universe u

/-- Every ordinary L¹ functional has a genuinely measurable representative
bounded at every point by the original operator norm.  Product integrability
is asserted before using the Bochner integral. -/
def endpoint_representative : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    letI : MeasurableSpace X := RadonDisjointCompactLocalization.M μ
    ∀ ℓ : Lp 𝕜 1 (RadonDisjointCompactLocalization.m μ) →L[𝕜] 𝕜,
    ∃ g : X → 𝕜, Measurable g ∧ (∀ x, ‖g x‖ ≤ ‖ℓ‖) ∧
      ∀ f : Lp 𝕜 1 (RadonDisjointCompactLocalization.m μ),
        Integrable (fun x => f x * g x) (RadonDisjointCompactLocalization.m μ) ∧
        ℓ f = ∫ x, f x * g x ∂(RadonDisjointCompactLocalization.m μ)

end Specs.D11.Ch20.LocalNullEndpointRepresentative
