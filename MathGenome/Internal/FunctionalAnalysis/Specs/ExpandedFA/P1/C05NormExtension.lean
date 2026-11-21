import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual

/-!
Independent specification of `fa2:p1:c05:norm-extension`, paper.tex:902–908.
The scalar field includes both ℝ and ℂ. The continuous dual is the native
scalar-linear continuous-map space, with its operator norm. The subspace
carries its inherited norm; no completeness, closedness, or nontriviality
assumption is imposed.
-/

namespace ExpandedFA.P1.C05NormExtension.Spec

universe u v

/-- Every continuous scalar-linear functional on an arbitrary subspace extends
to the whole normed space with exactly the same operator norm. -/
def NormPreservingExtension : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (f : M →L[𝕜] 𝕜),
    ∃ F : E →L[𝕜] 𝕜,
      (∀ m : M, F (m : E) = f m) ∧ ‖F‖ = ‖f‖

end ExpandedFA.P1.C05NormExtension.Spec
