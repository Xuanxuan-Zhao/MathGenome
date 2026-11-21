import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open MeasureTheory Set
namespace ExpandedFA.PartIV.KreinNonuniqueFourier.Spec

/-- The signed cosine representation used in the nonuniqueness construction.
Both positive measures are finite and supported on nonnegative frequencies. -/
def SignedCosineRepresentation : Prop :=
  ∃ αp αm : Measure ℝ,
    IsFiniteMeasure αp ∧ IsFiniteMeasure αm ∧
    αp (Iio 0) = 0 ∧ αm (Iio 0) = 0 ∧
    ∀ s : ℝ, Integrable (fun a => Real.cos (a * s)) αp ∧
      Integrable (fun a => Real.cos (a * s)) αm ∧
      Real.exp (-Real.cosh s) =
        (∫ a, Real.cos (a * s) ∂αp) - ∫ a, Real.cos (a * s) ∂αm

end ExpandedFA.PartIV.KreinNonuniqueFourier.Spec
