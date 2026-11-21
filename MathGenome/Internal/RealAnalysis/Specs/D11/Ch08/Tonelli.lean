import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure

/-!
Independent statements for Tonelli, paper.tex:2617–2637 (`D11.08.tonelli`).
The specified measurable spaces on X and Y are arbitrary; their product is
ordinary, with no completion. Both measures are sigma-finite. Every integral
uses the shared supremum of finite nonnegative simple minorants, and takes
values in ENNReal. Neither finite total mass nor finite integrals are assumed.
The statements include empty spaces and zero measures.
-/

open MeasureTheory
open scoped ENNReal
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open Specs.D11.Ch08.ProductMeasure (productMeasure_value)

universe u v
noncomputable section

namespace Specs.D11.Ch08.Tonelli

/-- Both section-integral maps are measurable at every parameter. -/
def section_integrals_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ f : X × Y → ℝ≥0∞, Measurable f →
      Measurable (fun x : X => nonnegativeIntegral_value ν (fun y : Y => f (x, y))) ∧
      Measurable (fun y : Y => nonnegativeIntegral_value μ (fun x : X => f (x, y)))

def integral_product_left : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ f : X × Y → ℝ≥0∞, Measurable f →
      nonnegativeIntegral_value (productMeasure_value μ ν) f =
        nonnegativeIntegral_value μ (fun x : X =>
          nonnegativeIntegral_value ν (fun y : Y => f (x, y)))

def integral_product_right : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ f : X × Y → ℝ≥0∞, Measurable f →
      nonnegativeIntegral_value (productMeasure_value μ ν) f =
        nonnegativeIntegral_value ν (fun y : Y =>
          nonnegativeIntegral_value μ (fun x : X => f (x, y)))

/-- The full source theorem, including the displayed chain of equalities. -/
def tonelli : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ f : X × Y → ℝ≥0∞, Measurable f →
      Measurable (fun x : X => nonnegativeIntegral_value ν (fun y : Y => f (x, y))) ∧
      Measurable (fun y : Y => nonnegativeIntegral_value μ (fun x : X => f (x, y))) ∧
      nonnegativeIntegral_value (productMeasure_value μ ν) f =
        nonnegativeIntegral_value μ (fun x : X =>
          nonnegativeIntegral_value ν (fun y : Y => f (x, y))) ∧
      nonnegativeIntegral_value μ (fun x : X =>
          nonnegativeIntegral_value ν (fun y : Y => f (x, y))) =
        nonnegativeIntegral_value ν (fun y : Y =>
          nonnegativeIntegral_value μ (fun x : X => f (x, y)))

end Specs.D11.Ch08.Tonelli
