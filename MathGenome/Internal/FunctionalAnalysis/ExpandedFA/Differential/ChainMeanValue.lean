import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.ChainMeanValue
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Differential.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

namespace ExpandedFA.Differential

/-- Chain rule on open domains, with the canonical derivative from the
upstream interface. Openness of the outer domain makes its derivative an
ambient derivative at `f x`, so no global image containment is necessary. -/
theorem chain_rule : Spec.ChainRule := by
  intro 𝕜 E F G _ _ _ _ _ _ _ _ _ _ Ω Λ hΩ hΛ f g x hx hfx hf hg
  have hcomp := (hg.hasFDerivWithinAt.hasFDerivAt (hΛ.mem_nhds hfx)).comp_hasFDerivWithinAt
    x hf.hasFDerivWithinAt
  exact ⟨hcomp, hcomp.fderivWithin (hΩ.uniqueDiffOn x hx)⟩

/-- The segment estimate. Restrict each derivative on the open domain to the
segment, then apply Mathlib's mean-value inequality on that convex set. That
inequality restricts scalars to ℝ and differentiates the segment path, so it
also applies to complex Banach spaces. -/
theorem mean_value_estimate : Spec.MeanValueEstimate := by
  intro 𝕜 E F _ _ _ _ _ _ _
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro Ω _hΩ f x y M hseg hf hbound
  exact (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hf z hz).hasFDerivWithinAt.mono hseg) hbound
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

end ExpandedFA.Differential
