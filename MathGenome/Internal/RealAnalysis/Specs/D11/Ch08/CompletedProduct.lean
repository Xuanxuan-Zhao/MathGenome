import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Completion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements for paper.tex:2684–2751. The completion is that of
 the ordinary product, not the ordinary product of completed factors. Every
 scalar integral carries the source integrability hypothesis. -/
open MeasureTheory
open scoped ENNReal
open Specs.D11.Ch02.Completion (completedSpace_value completedMeasure_value)
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value scalarIntegral_value)
open Specs.D11.Ch04.AeCommonException (almostEverywhere_value)
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)

universe u v
noncomputable section
namespace Specs.D11.Ch08.CompletedProduct

/-- Abbreviations for the already shared objects on their completed domains. -/
abbrev completedMeasurable {X : Type u} {E : Type*} [MeasurableSpace X]
    [MeasurableSpace E] (μ : Measure X) (f : X → E) : Prop :=
  @Measurable X E (completedSpace_value μ) _ f
abbrev completedNNIntegral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  @nonnegativeIntegral_value X (completedSpace_value μ) (completedMeasure_value μ) f
abbrev completedIntegrable {X : Type u} {𝕜 : Type} [MeasurableSpace X]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) : Prop :=
  @scalarIntegrable_value X 𝕜 (completedSpace_value μ) _ _ _ (completedMeasure_value μ) f
abbrev completedIntegral {X : Type u} {𝕜 : Type} [MeasurableSpace X]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (hf : completedIntegrable μ f) : 𝕜 :=
  @scalarIntegral_value X 𝕜 (completedSpace_value μ) _ _ _ (completedMeasure_value μ) f hf

def nonnegativeSectionLeft_type :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y],
    Measure Y → (X × Y → ℝ≥0∞) → X → ℝ≥0∞
def nonnegativeSectionLeft_value : nonnegativeSectionLeft_type.{u,v} := by
  classical
  exact fun ν f x => if completedMeasurable ν (fun y => f (x,y)) then
    completedNNIntegral ν (fun y => f (x,y)) else 0

def nonnegativeSectionRight_type :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y],
    Measure X → (X × Y → ℝ≥0∞) → Y → ℝ≥0∞
def nonnegativeSectionRight_value : nonnegativeSectionRight_type.{u,v} := by
  classical
  exact fun μ f y => if completedMeasurable μ (fun x => f (x,y)) then
    completedNNIntegral μ (fun x => f (x,y)) else 0

def scalarSectionLeft_type :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure Y → (X × Y → 𝕜) → X → 𝕜
def scalarSectionLeft_value : scalarSectionLeft_type.{u,v} := by
  classical
  exact fun ν f x => if h : completedIntegrable ν (fun y => f (x,y)) then
    completedIntegral ν (fun y => f (x,y)) h else 0

def scalarSectionRight_type :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure X → (X × Y → 𝕜) → Y → 𝕜
def scalarSectionRight_value : scalarSectionRight_type.{u,v} := by
  classical
  exact fun μ f y => if h : completedIntegrable μ (fun x => f (x,y)) then
    completedIntegral μ (fun x => f (x,y)) h else 0

/-- No size hypothesis is needed for preservation under completion. -/
def nonnegative_completion : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → completedMeasurable μ f ∧
      completedNNIntegral μ f = nonnegativeIntegral_value μ f

def scalar_completion : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (hf : scalarIntegrable_value μ f),
    ∃ hc : completedIntegrable μ f,
      completedIntegral μ f hc = scalarIntegral_value μ f hf

def tonelli : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (f : X × Y → ℝ≥0∞), completedMeasurable (productMeasure_value μ ν) f →
      @almostEverywhere_value X (completedSpace_value μ) (completedMeasure_value μ)
        (fun x => completedMeasurable ν (fun y => f (x,y))) ∧
      @almostEverywhere_value Y (completedSpace_value ν) (completedMeasure_value ν)
        (fun y => completedMeasurable μ (fun x => f (x,y))) ∧
      completedMeasurable μ (nonnegativeSectionLeft_value ν f) ∧
      completedMeasurable ν (nonnegativeSectionRight_value μ f) ∧
      completedNNIntegral (productMeasure_value μ ν) f =
        completedNNIntegral μ (nonnegativeSectionLeft_value ν f) ∧
      completedNNIntegral μ (nonnegativeSectionLeft_value ν f) =
        completedNNIntegral ν (nonnegativeSectionRight_value μ f)

def fubini : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (f : X × Y → 𝕜) (hf : completedIntegrable (productMeasure_value μ ν) f),
      @almostEverywhere_value X (completedSpace_value μ) (completedMeasure_value μ)
        (fun x => completedIntegrable ν (fun y => f (x,y))) ∧
      @almostEverywhere_value Y (completedSpace_value ν) (completedMeasure_value ν)
        (fun y => completedIntegrable μ (fun x => f (x,y))) ∧
      completedMeasurable μ (scalarSectionLeft_value ν f) ∧
      completedMeasurable ν (scalarSectionRight_value μ f) ∧
      ∃ (hl : completedIntegrable μ (scalarSectionLeft_value ν f))
        (hr : completedIntegrable ν (scalarSectionRight_value μ f)),
        completedIntegral (productMeasure_value μ ν) f hf =
          completedIntegral μ (scalarSectionLeft_value ν f) hl ∧
        completedIntegral μ (scalarSectionLeft_value ν f) hl =
          completedIntegral ν (scalarSectionRight_value μ f) hr

end Specs.D11.Ch08.CompletedProduct
