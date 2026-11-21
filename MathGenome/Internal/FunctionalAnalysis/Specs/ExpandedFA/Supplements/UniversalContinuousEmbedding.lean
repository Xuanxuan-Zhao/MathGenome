import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
Independent statement of the universal embedding in
`fa2:p1:banach-stone`, paper.tex 6631–6648.

`DualUnitBall` consists of the continuous scalar-linear functionals on the
original normed space with operator norm at most one. Its topology is the
subspace topology of `WeakDual`, not the dual norm topology. The explicit
topology statement below identifies it with the shared weak-star topology.
Compactness is a conclusion, supplied before forming the supremum norm on
`C(DualUnitBall 𝕜 E, 𝕜)`. There is no completeness, separability, or
nontriviality assumption on E.
-/

namespace ExpandedFA.Supplements.UniversalContinuousEmbedding

universe u v

/-- The norm-closed unit ball of the continuous linear dual, with the
weak-star subspace topology inherited from `WeakDual 𝕜 E`. -/
abbrev DualUnitBall (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  {f : WeakDual 𝕜 E // ‖WeakDual.toStrongDual f‖ ≤ 1}

namespace Spec

/-- The topology on the domain is precisely the restriction of σ(E′, E)
along the map retaining the underlying norm-continuous functional. -/
def DomainTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (inferInstance : TopologicalSpace (DualUnitBall 𝕜 E)) =
      TopologicalSpace.induced
        (fun f : DualUnitBall 𝕜 E => WeakDual.toStrongDual f.val)
        (P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)

/-- Evaluation embeds E scalar-linearly and isometrically into the
continuous scalar-valued functions on its compact Hausdorff weak-star
dual unit ball. The displayed formula fixes the embedding itself. -/
def UniversalEmbedding : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    ∃ hcompact : CompactSpace (DualUnitBall 𝕜 E),
      letI := hcompact
      T2Space (DualUnitBall 𝕜 E) ∧
        ∃ J : E →ₗᵢ[𝕜] C(DualUnitBall 𝕜 E, 𝕜),
          ∀ (x : E) (f : DualUnitBall 𝕜 E),
            J x f = WeakDual.toStrongDual f.val x

end Spec
end ExpandedFA.Supplements.UniversalContinuousEmbedding
