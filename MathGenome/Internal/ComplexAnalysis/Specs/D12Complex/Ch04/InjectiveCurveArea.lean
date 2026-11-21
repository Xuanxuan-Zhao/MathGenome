import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set
open scoped ENNReal

namespace Specs.D12Complex.Ch04.InjectiveCurveArea

/-- The metric one-dimensional Hausdorff measure has the Lebesgue normalization. -/
def real_normalization_type : Prop :=
  (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) = volume

/-- The full injective curve area statement, with completed source measurability. -/
def image_area_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    Bornology.IsBounded s → NullMeasurableSet s volume → s ⊆ U →
    InjOn γ s → (∀ t ∈ s, deriv γ t ≠ 0) →
    NullMeasurableSet (γ '' s) (MeasureTheory.Measure.hausdorffMeasure 1) ∧
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (γ '' s) =
        ∫⁻ t in s, ENNReal.ofReal ‖deriv γ t‖

/-- The actual map of speed-weighted volume, including its required a.e. measurability. -/
def map_weighted_volume_type : Prop :=
  ∀ (γ : ℝ → ℂ) (U s : Set ℝ), IsOpen U → ContDiffOn ℝ 1 γ U →
    Bornology.IsBounded s → NullMeasurableSet s volume → s ⊆ U →
    InjOn γ s → (∀ t ∈ s, deriv γ t ≠ 0) →
    AEMeasurable γ ((volume.restrict s).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) ∧
      Measure.map γ ((volume.restrict s).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) =
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ).restrict (γ '' s)

end Specs.D12Complex.Ch04.InjectiveCurveArea
