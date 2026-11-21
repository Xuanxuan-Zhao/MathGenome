import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Sequences

/-! Independent statements of `fa2:p1:krein-smulian`, paper.tex:3373–3381.
The continuous scalar-linear dual and its norm are those of the original
Banach space. Convexity is over the reals for either scalar field. The ball
slices are closed in the ambient weak-star topology. -/

namespace ExpandedFA.P1.KreinSmulian.Spec

universe u v

/-- The closed-ball criterion for arbitrary real-convex subsets, including ∅. -/
def ConvexClosedCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (C : Set (E →L[𝕜] 𝕜)),
    Convex ℝ C →
    (@IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) C ↔
      ∀ r : ℝ, 0 < r → @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
        (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r}))

/-- For scalar-linear subspaces the closed unit ball alone suffices. -/
def SubspaceClosedCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (M : Submodule 𝕜 (E →L[𝕜] 𝕜)),
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) (M : Set _) ↔
    @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      ((M : Set _) ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ 1})

/-- Sequential closedness is taken in the whole weak-star dual, without any
extra boundedness assumption on the sequences. -/
def SequentialClosedCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (C : Set (E →L[𝕜] 𝕜)), Convex ℝ C →
    (@IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) C ↔
      @IsSeqClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) C)

end ExpandedFA.P1.KreinSmulian.Spec
