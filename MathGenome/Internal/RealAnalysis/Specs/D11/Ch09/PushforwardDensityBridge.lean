import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.Pushforward
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements of the supplied-density bridge, paper.tex:3037–3052.
The measure equality is a hypothesis, with no Radon–Nikodym or size assumption.
Nonnegative products are ENNReal products, so zero times infinity is zero.
For scalar products, `toReal` resets the measurable null infinite-value set
to zero. The modification statement records both this prescription and
preservation of the density measure on the original measurable space.
Scalar integrals are evaluated only after establishing absolute integrability.
-/

open MeasureTheory
open scoped ENNReal
universe u v

namespace Specs.D11.Ch09.PushforwardDensityBridge

open Specs.D11.Ch09.Pushforward
open Specs.D11.Ch05.DensityMeasureDomains
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral

def nonnegative_bridge : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h g : Y → ℝ≥0∞), Measurable h → Measurable g →
    pushforward_value u hu μ = densityMeasure_value ν h →
    nonnegativeIntegral_value μ (g ∘ u) =
      nonnegativeIntegral_value ν (fun y => g y * h y)

def finite_density_modification : Prop :=
  ∀ {Y : Type v} [MeasurableSpace Y] (ν : Measure Y) (h : Y → ℝ≥0∞),
    Measurable h → (∀ᵐ y ∂ν, h y < ∞) →
    MeasurableSet {y | h y = ∞} ∧ ν {y | h y = ∞} = 0 ∧
    Measurable (fun y => (h y).toReal) ∧
    (∀ y, 0 ≤ (h y).toReal) ∧
    (∀ y, h y = ∞ → (h y).toReal = 0) ∧
    (∀ y, h y < ∞ → ENNReal.ofReal (h y).toReal = h y) ∧
    ((fun y => ENNReal.ofReal (h y).toReal) =ᵐ[ν] h) ∧
    densityMeasure_value ν (fun y => ENNReal.ofReal (h y).toReal) =
      densityMeasure_value ν h

def scalar_integrable_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h : Y → ℝ≥0∞) (g : Y → 𝕜),
    Measurable h → (∀ᵐ y ∂ν, h y < ∞) → Measurable g →
    pushforward_value u hu μ = densityMeasure_value ν h →
    (scalarIntegrable_value μ (g ∘ u) ↔
      nonnegativeIntegral_value ν (fun y => ENNReal.ofReal ‖g y‖ * h y) < ∞)

def scalar_bridge : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h : Y → ℝ≥0∞) (g : Y → 𝕜),
    Measurable h → (∀ᵐ y ∂ν, h y < ∞) → Measurable g →
    pushforward_value u hu μ = densityMeasure_value ν h →
    nonnegativeIntegral_value ν (fun y => ENNReal.ofReal ‖g y‖ * h y) < ∞ →
    ∃ (hc : scalarIntegrable_value μ (g ∘ u))
      (hp : scalarIntegrable_value ν (fun y => (h y).toReal • g y)),
      scalarIntegral_value μ (g ∘ u) hc =
        scalarIntegral_value ν (fun y => (h y).toReal • g y) hp

end Specs.D11.Ch09.PushforwardDensityBridge
