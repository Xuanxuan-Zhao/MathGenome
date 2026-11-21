import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealFugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.FugledeIntertwining
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification

/-!
Complexify on the shared Hilbert space H ⊕ iH. Preservation of composition
and adjoints transfers normality and the intertwining equation to the
complex spaces. Complex Fuglede–Putnam then descends through the canonical
injective real inclusion.
-/

namespace ExpandedFA.SpectralMeasure.RealFugledeIntertwining
universe u v
open TraceIdeals.RealComplexification

theorem adjoint_intertwining : Spec.AdjointIntertwining.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  have hNC : (operator N).adjoint.comp (operator N) =
      (operator N).comp (operator N).adjoint := by
    rw [operator_adjoint, ← operator_comp, ← operator_comp, hN]
  have hMC : (operator M).adjoint.comp (operator M) =
      (operator M).comp (operator M).adjoint := by
    rw [operator_adjoint, ← operator_comp, ← operator_comp, hM]
  have hTC : (operator N).comp (operator T) = (operator T).comp (operator M) := by
    rw [← operator_comp, hT, operator_comp]
  have hC := FugledeIntertwining.adjoint_intertwining (Space H) (Space K)
    (operator N) (operator M) (operator T) hNC hMC hTC
  ext x
  apply inclusion.injective
  have hx := congrArg (fun A : Space K →L[ℂ] Space H => A (inclusion x)) hC
  simpa only [operator_adjoint, ContinuousLinearMap.comp_apply, operator_inclusion] using hx

end ExpandedFA.SpectralMeasure.RealFugledeIntertwining
