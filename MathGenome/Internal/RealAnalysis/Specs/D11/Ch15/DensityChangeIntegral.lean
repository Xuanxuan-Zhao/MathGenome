import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.DensityMeasureVariation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration

/-! Independent statements for paper.tex:4947–4966. All functions are
measurable on the original sigma-algebra. The reference measure is arbitrary.
Nonnegative multiplication is in ENNReal, including `0 * ∞ = 0`.
For scalar integrals the conclusions supply absolute integrability before
evaluating the shared, proof-indexed integrals. `toReal` chooses zero on the
null set where a positive density is infinite. Finite scalar density measures
are the shared measures of absolutely integrable real or complex densities.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch15.DensityChangeIntegral
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral

def nonnegative_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h g : X → ℝ≥0∞),
    Measurable h → Measurable g →
    nonnegativeIntegral_value (Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_value μ h) g =
      nonnegativeIntegral_value μ (fun x => g x * h x)

def positive_scalar_integrable_iff : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → ℝ≥0∞)
    (g : X → 𝕜), Measurable h → (∀ᵐ x ∂μ, h x < ∞) → Measurable g →
    (scalarIntegrable_value (Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_value μ h) g ↔
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖g x‖ * h x) < ∞)

def positive_scalar_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (h : X → ℝ≥0∞)
    (g : X → 𝕜), Measurable h → (∀ᵐ x ∂μ, h x < ∞) → Measurable g →
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖g x‖ * h x) < ∞ →
    ∃ (hg : scalarIntegrable_value
        (Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_value μ h) g)
      (hgh : scalarIntegrable_value μ (fun x => (h x).toReal • g x)),
      scalarIntegral_value _ g hg = scalarIntegral_value μ _ hgh

def signed_scalar_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (k : X → ℝ)
    (hk : scalarIntegrable_value μ k) (g : X → 𝕜), Measurable g →
    nonnegativeIntegral_value μ
      (fun x => ENNReal.ofReal ‖g x‖ * ENNReal.ofReal ‖k x‖) < ∞ →
    ∃ (hg : Specs.D11.Ch14.ScalarIntegration.signedIntegrable_value
        (Specs.D11.Ch14.DensityMeasureVariation.densityMeasure_value μ k hk) g)
      (hgk : scalarIntegrable_value μ (fun x => k x • g x)),
      Specs.D11.Ch14.ScalarIntegration.signedIntegral_value _ g hg =
        scalarIntegral_value μ _ hgk

def complex_scalar_change : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (k : X → ℂ)
    (hk : scalarIntegrable_value μ k) (g : X → ℂ), Measurable g →
    nonnegativeIntegral_value μ
      (fun x => ENNReal.ofReal ‖g x‖ * ENNReal.ofReal ‖k x‖) < ∞ →
    ∃ (hg : Specs.D11.Ch14.ScalarIntegration.complexIntegrable_value
        (Specs.D11.Ch14.DensityMeasureVariation.densityMeasure_value μ k hk) g)
      (hgk : scalarIntegrable_value μ (fun x => g x * k x)),
      Specs.D11.Ch14.ScalarIntegration.complexIntegral_value _ g hg =
        scalarIntegral_value μ _ hgk

end Specs.D11.Ch15.DensityChangeIntegral
