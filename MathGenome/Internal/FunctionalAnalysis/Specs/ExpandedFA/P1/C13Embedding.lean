import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Topology.Homeomorph.Defs

/-!
Independent statements for `fa2:p1:c13:embedding`, paper.tex 2616–2622.
All duals and the canonical map are formed with the original norm topologies.
The weak topology uses the continuous scalar-linear dual; the weak-star
topology on E″ uses E′, with its original operator norm, as predual.
The range has the subspace topology from this particular weak-star topology.
There is no completeness, separability, reflexivity or nonzero-space assumption.
-/

namespace ExpandedFA.P1.C13Embedding.Spec

universe u v w
open Filter
open scoped Topology
noncomputable section

/-- Pullback of σ(E″,E′) along J_E is exactly σ(E,E′). -/
def InducedTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) =
      TopologicalSpace.induced (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))

/-- The canonical map itself is a topological embedding for these topologies. -/
def WeakEmbedding : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    @Topology.IsEmbedding E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

/-- A homeomorphism onto the actual image, whose forward map is J_E. -/
def HomeomorphismOntoImage : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    let J := C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E
    ∃ h : @Homeomorph E (Set.range J)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (TopologicalSpace.induced Subtype.val
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))),
      ∀ x : E, (h x).val = J x

/-- Arbitrary filters include every directed net, with both limits specified. -/
def NetConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (A : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter A) (xₐ : A → E) (x : E),
    Tendsto xₐ l
      (@nhds E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) ↔
    Tendsto (fun a => C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (xₐ a)) l
      (@nhds ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
        (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x))

end
end ExpandedFA.P1.C13Embedding.Spec
