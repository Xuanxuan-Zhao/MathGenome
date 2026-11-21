import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.AveragesMaximalDefinition

/-! Independent statements of paper.tex:4370–4399. The domain is the
completed Euclidean Lebesgue space, and the maximal function is the shared
supremum over every strictly positive real radius. `Integrable` is absolute
integrability; actual measurability is retained by `locallyIntegrable_value`.
The norm on the right is the L¹ norm, written as the integral of the norm. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch13.MaximalWeak11
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch13.AveragesMaximalDefinition

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := lebesgueSpace_value n

def locallyIntegrable_of_integrable : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
    Measurable f → Integrable f (lebesgue_value n) → locallyIntegrable_value f

def continuous_ball_integral : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜),
    Integrable f (lebesgue_value n) → ∀ r : ℝ, 0 < r →
    Continuous (fun x => ∫ y in Metric.ball x r, ‖f y‖ ∂(lebesgue_value n))

def strict_superlevel_open : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜)
    (hf : locallyIntegrable_value f), Integrable f (lebesgue_value n) →
    ∀ α : ℝ≥0∞, IsOpen {x | α < maximal_value f hf x}

def maximal_measurable : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜)
    (hf : locallyIntegrable_value f), Integrable f (lebesgue_value n) →
    Measurable (maximal_value f hf)

def maximal_weak11 : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜)
    (hf : locallyIntegrable_value f), Integrable f (lebesgue_value n) →
    ∀ α : ℝ, 0 < α →
    lebesgue_value n {x | ENNReal.ofReal α < maximal_value f hf x} ≤
      (3 : ℝ≥0∞) ^ n * (ENNReal.ofReal α)⁻¹ *
        ENNReal.ofReal (∫ y, ‖f y‖ ∂(lebesgue_value n))

def maximal_finite_ae : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜)
    (hf : locallyIntegrable_value f), Integrable f (lebesgue_value n) →
    ∀ᵐ x ∂(lebesgue_value n), maximal_value f hf x < ∞

end Specs.D11.Ch13.MaximalWeak11
