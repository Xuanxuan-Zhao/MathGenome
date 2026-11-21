import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair

/-!
The dual clause of `fa2:p1:c06:double-annihilator`, paper.tex 1215–1241.
The topology is explicitly σ(E′, E), using the shared bilinear evaluation
pairing with its arguments reversed. The continuous dual is formed with the
original norm topology on E before introducing this topology on E′.
No completeness, closedness, boundedness, or nonzero-space assumption is made.
-/

namespace ExpandedFA.P1.DoubleAnnihilatorDual.Spec

universe u v

/-- For every scalar-linear subspace N of the continuous linear dual, the
annihilator of its preannihilator is its weak-star closure. -/
def DoubleAnnihilatorClosure : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (N : Submodule 𝕜 (E →L[𝕜] 𝕜)),
    (C04Annihilators.Spec.AnnihilatorValue 𝕜 E
      (C04Annihilators.Spec.PreannihilatorValue 𝕜 E
        (N : Set (E →L[𝕜] 𝕜)) : Set E) : Set (E →L[𝕜] 𝕜)) =
      @closure (E →L[𝕜] 𝕜)
        (C12DualPairSpec.DualPairTopologyValue 𝕜 (E →L[𝕜] 𝕜) E
          (topDualPairing 𝕜 E).flip)
        (N : Set (E →L[𝕜] 𝕜))

end ExpandedFA.P1.DoubleAnnihilatorDual.Spec
