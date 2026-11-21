import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MeasureDifferentiation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueDecompositionSigmaFinite
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent scope for paper.tex:4497–4534. Measures retain their Borel
sigma-algebra. Densities and exceptional sets use completed Lebesgue measure.
A family and its comparison constant are quantified after the exceptional set.
Extended signed ratios are evaluated only after local finiteness is established. -/
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace D11.Ch13.RegularMeasureDifferentiation
open D11.Ch03 Specs.D11.Ch03.LebesgueMeasures
open D11.Ch14.ScalarInterfaces

variable {n : ℕ} [NeZero n]

/-- Positive radii index Borel sets occupying a fixed positive ball fraction. -/
def NiceFamily (x : Point n) (c : ℝ) (E : ℝ → Set (Point n)) : Prop :=
  0 < c ∧ ∀ r, 0 < r → MeasurableSet (E r) ∧ E r ⊆ ball x r ∧
    ENNReal.ofReal c * lebesgue_value n (ball x r) ≤ lebesgue_value n (E r)

/-- Ratios of ordinary finite scalar set values. -/
def ScalarNiceLimit {𝕜 : Type} [RCLike 𝕜]
    (v : Set (Point n) → 𝕜) (a : 𝕜) (x : Point n) : Prop :=
  ∀ (c : ℝ) (E : ℝ → Set (Point n)), NiceFamily x c E →
    (∀ r, 0 < r → 0 < lebesgue_value n (E r) ∧ lebesgue_value n (E r) < ∞) ∧
    Tendsto (fun r => (lebesgue_value n (E r)).toReal⁻¹ • v (E r))
      (𝓝[>] (0 : ℝ)) (𝓝 a)

/-- Lebesgue points refer to the chosen completed-measurable representative. -/
def DensityLebesguePoint {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : Point n → 𝕜) (x : Point n) : Prop :=
  ∃ hf : Specs.D11.Ch13.AveragesMaximalDefinition.locallyIntegrable_value f,
    Specs.D11.Ch13.AveragesMaximalDefinition.lebesguePoint_value f hf x

/-- A totalization outside the Borel domain; conclusions use only Borel sets. -/
def signedValue (ν : ExtendedSignedMeasure (Point n)) (E : Set (Point n)) : ℝ :=
  by
    classical
    exact if h : MeasurableSet E then (ν.value ⟨E, h⟩).toReal else 0

/-- No extended signed infinity is converted to a purported finite numerator. -/
def SignedLocallyFinite (ν : ExtendedSignedMeasure (Point n)) : Prop :=
  ∀ (x : Point n) (r : ℝ) (E : Set (Point n)) (hE : MeasurableSet E),
    E ⊆ ball x r → ν.value ⟨E,hE⟩ ≠ ⊤ ∧ ν.value ⟨E,hE⟩ ≠ ⊥

end D11.Ch13.RegularMeasureDifferentiation

namespace Specs.D11.Ch13.RegularMeasureDifferentiation
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open _root_.D11.Ch13.RegularMeasureDifferentiation
open _root_.D11.Ch13.MeasureDifferentiation
open _root_.D11.Ch14.ScalarInterfaces

/-- The local singular theorem uses compact finiteness, never finite total mass. -/
def singular_centered_balls : Prop :=
  ∀ {n : ℕ} [NeZero n] (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ],
    σ ⟂ₘ borelMeasure_value n → ∀ᵐ x ∂lebesgue_value n,
      Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Positive measures, with existence of the density and singular part included.
The second assertion retains every selected completed-measurable representative. -/
def positive_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν : Measure (Point n))
    [IsFiniteMeasureOnCompacts ν] [Measure.OuterRegular ν],
    (∃ (f : Point n → ℝ) (σ : Measure (Point n)), DensityDecomposition ν σ f) ∧
    ∀ (f : Point n → ℝ) (σ : Measure (Point n)), DensityDecomposition ν σ f →
      Ch13.AveragesMaximalDefinition.locallyIntegrable_value f ∧
      (∀ (x : Point n) (r : ℝ), ν (ball x r) < ∞ ∧ σ (ball x r) < ∞) ∧
      ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
        ∀ x ∉ N,
          DensityLebesguePoint f x ∧
          Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
          ScalarNiceLimit (fun E => (ν E).toReal) (f x) x ∧
          ScalarNiceLimit (fun E => (σ E).toReal) 0 x

/-- Extended signed measures omitting one infinity, with locally integrable
finite real density and actual Borel Lebesgue decomposition as conclusions. -/
def signed_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν : ExtendedSignedMeasure (Point n))
    [IsFiniteMeasureOnCompacts (Ch14.ExtendedSignedVariant.variation_value ν)]
    [Measure.OuterRegular (Ch14.ExtendedSignedVariant.variation_value ν)],
    ∃ (a s : ExtendedSignedMeasure (Point n)) (f : Point n → ℝ),
      Ch15.LebesgueRNSigmaFiniteSigned.Decomposition ν (borelMeasure_value n) a s ∧
      Ch15.LebesgueRNSigmaFiniteSigned.Density (borelMeasure_value n) a f ∧
      Ch13.AveragesMaximalDefinition.locallyIntegrable_value f ∧
      SignedLocallyFinite ν ∧ SignedLocallyFinite s ∧
      ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
        ∀ x ∉ N,
          DensityLebesguePoint f x ∧
          Tendsto (fun r => measureRatio (Ch14.ExtendedSignedVariant.variation_value s)
            (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
          ScalarNiceLimit (signedValue ν) (f x) x ∧
          ScalarNiceLimit (signedValue s) 0 x

/-- Finite complex measures, with the usual scalar decomposition and density.
Global L1 supplied by RN implies the required local L1 without an extra assumption. -/
def complex_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν : ComplexMeasure (Point n))
    [IsFiniteMeasureOnCompacts (Ch14.TotalVariation.totalVariation_value ν)]
    [Measure.OuterRegular (Ch14.TotalVariation.totalVariation_value ν)],
    ∃ (a s : ComplexMeasure (Point n)) (f : Point n → ℂ),
      Ch15.LebesgueDecompositionFiniteTarget.Decomposition ν (borelMeasure_value n) a s ∧
      Ch15.LebesgueDecompositionSigmaFinite.ScalarDensity (borelMeasure_value n) a f ∧
      Ch13.AveragesMaximalDefinition.locallyIntegrable_value f ∧
      ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
        ∀ x ∉ N,
          DensityLebesguePoint f x ∧
          Tendsto (fun r => measureRatio (Ch14.TotalVariation.totalVariation_value s)
            (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
          ScalarNiceLimit (fun E => ν E) (f x) x ∧
          ScalarNiceLimit (fun E => s E) 0 x

/-- Uniform analytic statement for every completed-measurable scalar density.
The set identity is the local form of the supplied measure decomposition. -/
def scalar_local_differentiation : Prop :=
  ∀ {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (V S : Set (Point n) → 𝕜) (σ : Measure (Point n)) [IsFiniteMeasureOnCompacts σ],
    σ ⟂ₘ borelMeasure_value n →
    ∀ (f : Point n → 𝕜), Ch13.AveragesMaximalDefinition.locallyIntegrable_value f →
    (∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E →
      E ⊆ ball x r → ‖S E‖ ≤ (σ E).toReal) →
    (∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E →
      E ⊆ ball x r → V E = (∫ y in E, f y ∂lebesgue_value n) + S E) →
    ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N, DensityLebesguePoint f x ∧
        Tendsto (fun r => measureRatio σ (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ScalarNiceLimit V (f x) x ∧ ScalarNiceLimit S 0 x

/-- Every supplied extended signed decomposition and every chosen completed
representative of its density. The integral identity on bounded Borel sets is
weaker than a global density identity and suffices for all local conclusions. -/
def signed_given_decomposition : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν a s : ExtendedSignedMeasure (Point n))
    [IsFiniteMeasureOnCompacts (Ch14.ExtendedSignedVariant.variation_value ν)]
    [Measure.OuterRegular (Ch14.ExtendedSignedVariant.variation_value ν)],
    Ch15.LebesgueRNSigmaFiniteSigned.Decomposition ν (borelMeasure_value n) a s →
    ∀ (f : Point n → ℝ), Ch13.AveragesMaximalDefinition.locallyIntegrable_value f →
    (∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E → E ⊆ ball x r →
      signedValue a E = ∫ y in E, f y ∂lebesgue_value n) →
    SignedLocallyFinite ν ∧ SignedLocallyFinite s ∧
    ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N, DensityLebesguePoint f x ∧
        Tendsto (fun r => measureRatio (Ch14.ExtendedSignedVariant.variation_value s)
          (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ScalarNiceLimit (signedValue ν) (f x) x ∧ ScalarNiceLimit (signedValue s) 0 x

/-- Every supplied finite complex decomposition and every completed density
representative, with no Borel representative restriction on f. -/
def complex_given_decomposition : Prop :=
  ∀ {n : ℕ} [NeZero n] (ν a s : ComplexMeasure (Point n))
    [IsFiniteMeasureOnCompacts (Ch14.TotalVariation.totalVariation_value ν)]
    [Measure.OuterRegular (Ch14.TotalVariation.totalVariation_value ν)],
    Ch15.LebesgueDecompositionFiniteTarget.Decomposition ν (borelMeasure_value n) a s →
    ∀ (f : Point n → ℂ), Ch13.AveragesMaximalDefinition.locallyIntegrable_value f →
    (∀ (x : Point n) (r : ℝ) (E : Set (Point n)), MeasurableSet E → E ⊆ ball x r →
      a E = ∫ y in E, f y ∂lebesgue_value n) →
    ∃ N : Set (Point n), MeasurableSet[lebesgueSpace_value n] N ∧ lebesgue_value n N = 0 ∧
      ∀ x ∉ N, DensityLebesguePoint f x ∧
        Tendsto (fun r => measureRatio (Ch14.TotalVariation.totalVariation_value s)
          (ball x r)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ScalarNiceLimit (fun E => ν E) (f x) x ∧ ScalarNiceLimit (fun E => s E) 0 x

end Specs.D11.Ch13.RegularMeasureDifferentiation
