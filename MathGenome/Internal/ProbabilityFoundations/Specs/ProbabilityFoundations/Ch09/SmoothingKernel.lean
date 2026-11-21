import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace Specs.ProbabilityFoundations.Ch09.SmoothingKernel

/-- A single density on the real line, with the probability Fourier convention
`charFun μ t = ∫ x, exp (i*x*t) ∂μ`. No later law or scale is a parameter. -/
def KernelProperties (J : ℝ → ℝ) : Prop :=
  Continuous J ∧
  (∀ x, J (-x) = J x) ∧
  (∀ x, 0 ≤ J x) ∧
  (∃ C : ℝ, ∀ x, |J x| ≤ C) ∧
  Integrable J ∧
  (∫ x, J x) = 1 ∧
  Integrable (fun x => |x| * J x) ∧
  IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (J x))) ∧
  (∀ t : ℝ, 1 < |t| →
    charFun (volume.withDensity (fun x => ENNReal.ofReal (J x))) t = 0) ∧
  (∀ t : ℝ, ‖charFun (volume.withDensity (fun x => ENNReal.ofReal (J x))) t‖ ≤ 1) ∧
  Continuous (charFun (volume.withDensity (fun x => ENNReal.ofReal (J x)))) ∧
  Integrable (charFun (volume.withDensity (fun x => ENNReal.ofReal (J x))))

def ExistsSmoothingKernel : Prop := ∃ J : ℝ → ℝ, KernelProperties J

end Specs.ProbabilityFoundations.Ch09.SmoothingKernel
