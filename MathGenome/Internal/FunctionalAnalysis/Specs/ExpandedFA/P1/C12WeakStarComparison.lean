import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
Independent statements for `fa2:p1:c12:weak-star-comparison`, paper.tex
2307–2321. Duals and the bidual are formed with the original norm topologies;
the compared topologies are on that same continuous-linear-dual carrier.
No completeness assumption is needed for the main equivalence or for the
description of continuous scalar-linear tests. Scalars may be real or complex.
-/

namespace ExpandedFA.P1.C12WeakStarComparison.Spec

universe u v
noncomputable section

/-- The weak-star continuous linear functionals are exactly evaluations.
The representing vector is unique, including in the zero space. -/
def ContinuousEvaluation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜),
    @Continuous (E →L[𝕜] 𝕜) 𝕜
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) inferInstance g ↔
      ∃! x : E, ∀ f : E →L[𝕜] 𝕜, g f = f x

/-- The canonical map, rather than an arbitrary bidual isomorphism,
characterizes equality of the weak and weak-star topologies. -/
def TopologiesEqualIffSurjective : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E =
      C12WeakStar.Spec.DualWeakTopologyValue 𝕜 E ↔
    Function.Surjective (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

/-- The consequence stated at the end of the source proof. -/
def NonreflexiveBanachTopologiesDiffer : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E ≠
      C12WeakStar.Spec.DualWeakTopologyValue 𝕜 E

end
end ExpandedFA.P1.C12WeakStarComparison.Spec
