import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSolutions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! The compensated (minus/odd) conclusion of `fa2:p4:krein-kernel`.
The scalar function is real, as explicitly required by the source. No finite
mass, differentiability, nonconstancy or nonzero-Hilbert-space premise is imposed. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinKernelMinus.Spec

/-- The source's compensated integrand, with its prescribed zero value. -/
def compensated (ξ s : ℝ) : ℝ :=
  if ξ = 0 then -(s ^ 2) / 2 else (1 - KreinSolutions.Specs.CValue ξ s) / ξ

/-- Absolute convergence and one integrable majorant for every compact interval
of the spatial variable. The measure is allowed to have infinite total mass. -/
def CompactDomination (ν : Measure ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ g : ℝ → ℝ,
    Integrable g ν ∧ (∀ ξ, 0 ≤ g ξ) ∧
      ∀ (s ξ : ℝ), |s| ≤ R → |compensated ξ s| ≤ g ξ

/-- The full minus-kernel representation, including the constant case. -/
def Main : Prop :=
  ∀ (F : ℝ → ℝ), Continuous F → Function.Even F →
    KreinSolutions.Specs.PositiveDefiniteValue (KreinSolutions.Specs.KernelMinusValue F) →
    ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      (∀ s : ℝ, Integrable (fun ξ => compensated ξ s) ν) ∧
      (∀ s : ℝ, F s = F 0 + ∫ ξ, compensated ξ s ∂ν) ∧ CompactDomination ν

end ExpandedFA.PartIV.KreinKernelMinus.Spec
