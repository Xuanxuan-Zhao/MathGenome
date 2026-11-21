import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Embedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Topology.Homeomorph.Lemmas

/-! The canonical bidual map is a homeomorphism from the weak topology onto
its image in the weak-star bidual, Proposition `fa2:p1:c13:embedding`. -/

namespace ExpandedFA.P1.C13Embedding

universe u v w
noncomputable section

/-- The coordinates of both initial topologies are precisely x ↦ f(x). -/
theorem canonicalEvaluation_weak_induced : Spec.InducedTopology.{u, v} := by
  intro 𝕜 E _ _ _
  rw [dualPairTopology_evaluation 𝕜 E,
    C12WeakStar.weakStarTopology_evaluations 𝕜 (E →L[𝕜] 𝕜), induced_iInf]
  simp only [induced_compose, Function.comp_def]
  rfl

/-- Injectivity uses the norm isometry; no completeness is required. -/
theorem canonicalEvaluation_weak_embedding : Spec.WeakEmbedding.{u, v} := by
  intro 𝕜 E _ _ _
  exact @Topology.IsEmbedding.mk E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
    (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
    (@Topology.IsInducing.mk E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
      (canonicalEvaluation_weak_induced 𝕜 E))
    (C05BidualIsometry.canonicalEvaluation_injective 𝕜 E)

/-- The range carries the subspace topology inherited from σ(E″,E′). -/
theorem canonicalEvaluation_weak_homeomorph_range :
    Spec.HomeomorphismOntoImage.{u, v} := by
  intro 𝕜 E _ _ _
  refine ⟨@Topology.IsEmbedding.toHomeomorph E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
    (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
    (canonicalEvaluation_weak_embedding 𝕜 E), fun _ => rfl⟩

/-- Weak convergence is exactly weak-star convergence of the images under J_E. -/
theorem canonicalEvaluation_weak_tendsto_iff : Spec.NetConvergence.{u, v, w} := by
  intro 𝕜 E A _ _ _ l xₐ x
  exact @Topology.IsEmbedding.tendsto_nhds_iff E ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) A
    (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)
    (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
    (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
    xₐ l x (canonicalEvaluation_weak_embedding 𝕜 E)

end
end ExpandedFA.P1.C13Embedding
