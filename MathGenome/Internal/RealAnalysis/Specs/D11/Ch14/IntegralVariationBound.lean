import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for paper.tex:4710–4721. Set integrals against
scalar measures are the shared Jordan integrals of measurable indicators.
All representatives are measurable on the original sigma-algebra. Domination
and convergence are with respect to partition total variation. Integrability
of the sequence and limit is a conclusion, before evaluating scalar integrals.
The real norm integral on the right is finite by absolute integrability. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch14.IntegralVariationBound
open ScalarIntegration TotalVariation
open Specs.D11.Ch06.ScalarIntegral

def signed_integral_variation_bound : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : SignedMeasure X) (f : X → 𝕜)
    (_hf : signedIntegrable_value ν f) (E : Set X), MeasurableSet E →
    ∃ hEf : signedIntegrable_value ν (E.indicator f),
      ‖signedIntegral_value ν (E.indicator f) hEf‖ ≤
        ∫ x in E, ‖f x‖ ∂(totalVariation_value ν)

def complex_integral_variation_bound : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ν : ComplexMeasure X) (f : X → ℂ)
    (_hf : complexIntegrable_value ν f) (E : Set X), MeasurableSet E →
    ∃ hEf : complexIntegrable_value ν (E.indicator f),
      ‖complexIntegral_value ν (E.indicator f) hEf‖ ≤
        ∫ x in E, ‖f x‖ ∂(totalVariation_value ν)

def signed_dominated_convergence : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : SignedMeasure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (F n)) → Measurable f →
    scalarIntegrable_value (totalVariation_value ν) g →
    (∀ n, ∀ᵐ x ∂(totalVariation_value ν), ‖F n x‖ ≤ g x) →
    (∀ᵐ x ∂(totalVariation_value ν), Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    ∃ (hF : ∀ n, signedIntegrable_value ν (F n)) (hf : signedIntegrable_value ν f),
      (∀ n, scalarIntegrable_value (totalVariation_value ν) (fun x => ‖F n x - f x‖)) ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂(totalVariation_value ν)) atTop (𝓝 0) ∧
      Tendsto (fun n => signedIntegral_value ν (F n) (hF n))
        atTop (𝓝 (signedIntegral_value ν f hf))

def complex_dominated_convergence : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ν : ComplexMeasure X)
    (F : ℕ → X → ℂ) (f : X → ℂ) (g : X → ℝ),
    (∀ n, Measurable (F n)) → Measurable f →
    scalarIntegrable_value (totalVariation_value ν) g →
    (∀ n, ∀ᵐ x ∂(totalVariation_value ν), ‖F n x‖ ≤ g x) →
    (∀ᵐ x ∂(totalVariation_value ν), Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    ∃ (hF : ∀ n, complexIntegrable_value ν (F n)) (hf : complexIntegrable_value ν f),
      (∀ n, scalarIntegrable_value (totalVariation_value ν) (fun x => ‖F n x - f x‖)) ∧
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂(totalVariation_value ν)) atTop (𝓝 0) ∧
      Tendsto (fun n => complexIntegral_value ν (F n) (hF n))
        atTop (𝓝 (complexIntegral_value ν f hf))

end Specs.D11.Ch14.IntegralVariationBound
