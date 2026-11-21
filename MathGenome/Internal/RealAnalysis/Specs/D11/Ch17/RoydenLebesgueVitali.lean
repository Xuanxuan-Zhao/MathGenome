import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Independent statements for the two Lebesgue variants at paper.tex:5282–5290.
`NullMeasurableSpace ℝ volume` is the real line with completed Borel Lebesgue
measurability. Functions have the trace domain E, and its measure is the shared
subtype restriction. The limit is finite and measurable, but its integrability
is a conclusion. Small-set UI includes individual integrability, not bounded
norms. The additional L1 conclusion records the stronger convergence proved.

The two abstract statements are useful stronger results from the same proof;
the explicit Lebesgue specializations below retain every original hypothesis.
The separately allocated general-measure Royden variant is not redefined here.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace Specs.D11.Ch17.RoydenLebesgueVitali
open Specs.D11.Ch17.UniformControls Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch07.ConvergenceDefinitions Specs.D11.Ch01.ExhaustionRestriction

def pointwise_vitali_spatial : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜) (hs : uiSmall_value μ F),
    spatialTails_value μ F → Measurable f → pointwiseConverges_value F f →
    ∃ hf : scalarIntegrable_value μ f,
      lpConverges_value μ 1 F f ∧
      Tendsto (fun n => scalarIntegral_value μ (F n) (hs.1 n)) atTop
        (𝓝 (scalarIntegral_value μ f hf))

def pointwise_vitali_finite : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜) (hs : uiSmall_value μ F),
    μ univ < ∞ → Measurable f → pointwiseConverges_value F f →
    ∃ hf : scalarIntegrable_value μ f,
      lpConverges_value μ 1 F f ∧
      Tendsto (fun n => scalarIntegral_value μ (F n) (hs.1 n)) atTop
        (𝓝 (scalarIntegral_value μ f hf))

def lebesgue_vitali_spatial : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (E : Set (NullMeasurableSpace ℝ (volume : Measure ℝ))), MeasurableSet E →
    let μ := restrictToSubtype_value (volume : Measure ℝ).completion E
    ∀ (F : ℕ → E → 𝕜) (f : E → 𝕜) (hs : uiSmall_value μ F),
      spatialTails_value μ F → Measurable f → pointwiseConverges_value F f →
      ∃ hf : scalarIntegrable_value μ f,
        lpConverges_value μ 1 F f ∧
        Tendsto (fun n => scalarIntegral_value μ (F n) (hs.1 n)) atTop
          (𝓝 (scalarIntegral_value μ f hf))

def lebesgue_vitali_finite : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (E : Set (NullMeasurableSpace ℝ (volume : Measure ℝ))), MeasurableSet E →
    (volume : Measure ℝ).completion E < ∞ →
    let μ := restrictToSubtype_value (volume : Measure ℝ).completion E
    ∀ (F : ℕ → E → 𝕜) (f : E → 𝕜) (hs : uiSmall_value μ F),
      Measurable f → pointwiseConverges_value F f →
      ∃ hf : scalarIntegrable_value μ f,
        lpConverges_value μ 1 F f ∧
        Tendsto (fun n => scalarIntegral_value μ (F n) (hs.1 n)) atTop
          (𝓝 (scalarIntegral_value μ f hf))

end Specs.D11.Ch17.RoydenLebesgueVitali
