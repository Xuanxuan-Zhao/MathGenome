import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair

/-!
Independent statements of `fa2:p1:c06:double-annihilator`, paper.tex:1215–1226.
Both annihilators use the continuous scalar-linear dual of the original normed
space. The first closure is in its norm topology. The second closure explicitly
uses σ(E′, E), the shared topology induced by the evaluation pairing.
Neither completeness nor closedness of the subspaces is required; zero spaces
and zero subspaces are included, over both real and complex scalars.
-/

namespace ExpandedFA.P1.C06DoubleAnnihilator.Spec

universe u v

/-- The preannihilator of M's annihilator is the norm closure of M. -/
def PrimalClosure : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    (C04Annihilators.Spec.PreannihilatorValue 𝕜 E
      (C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E) :
        Set (E →L[𝕜] 𝕜)) : Set E) = closure (M : Set E)

/-- The annihilator of N's preannihilator is the weak-star closure of N. -/
def DualClosure : Prop :=
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

end ExpandedFA.P1.C06DoubleAnnihilator.Spec
