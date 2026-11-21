import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The discrete signed representation used at `fa2:p4:krein-nonunique`.
The constant frequency belongs solely to the cosine measure. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinNonuniqueCoshSeries.Spec

/-- Full raw measure conclusion, independent of the candidate implementation. -/
def DiscreteDecomposition : Prop :=
  ∃ γ βp βm : Measure ℝ,
    IsFiniteMeasure γ ∧ IsFiniteMeasure βp ∧ IsFiniteMeasure βm ∧
    γ (Iio 0) = 0 ∧ βp (Iic 0) = 0 ∧ βm (Iic 0) = 0 ∧
    (∀ s : ℝ, Integrable (fun a => Real.cos (a * s)) γ ∧
      Integrable (fun b => Real.cosh (b * s)) βp ∧
      Integrable (fun b => Real.cosh (b * s)) βm ∧
      Real.exp (-Real.cosh s) = (∫ a, Real.cos (a * s) ∂γ) +
        (∫ b, Real.cosh (b * s) ∂βp) - ∫ b, Real.cosh (b * s) ∂βm) ∧
    (∀ R : ℝ, 0 < R → Integrable (fun b => Real.cosh (R * b)) βp ∧
      Integrable (fun b => Real.cosh (R * b)) βm) ∧
    0 < βm {1} ∧ βp {1} = 0

end ExpandedFA.PartIV.KreinNonuniqueCoshSeries.Spec
