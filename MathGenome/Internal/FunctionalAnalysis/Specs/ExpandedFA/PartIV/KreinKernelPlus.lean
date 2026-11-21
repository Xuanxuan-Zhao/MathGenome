import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSolutions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! The plus clause of `fa2:p4:krein-kernel`, paper.tex:21219–21228.
The measure is a positive Borel measure on the real spectral parameter.
No uniqueness or nonzero-space hypothesis is imposed. -/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinKernelPlus.Spec

/-- The original finite-measure representation, with absolute integrability
and every positive-side hyperbolic moment. -/
def Main : Prop :=
  ∀ (F : ℝ → ℝ), Continuous F → Function.Even F →
    KreinSolutions.Specs.PositiveDefiniteValue
      (KreinSolutions.Specs.KernelPlusValue F) →
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ν.real univ = F 0 ∧
      (∀ s : ℝ, Integrable (fun ξ => KreinSolutions.Specs.CValue ξ s) ν ∧
        F s = ∫ ξ, KreinSolutions.Specs.CValue ξ s ∂ν) ∧
      ∀ R : ℝ, 0 < R →
        IntegrableOn (fun ξ => Real.cosh (R * Real.sqrt ξ)) (Ioi 0) ν

end ExpandedFA.PartIV.KreinKernelPlus.Spec
