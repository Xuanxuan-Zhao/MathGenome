import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.Basic

/-! Independent statements for `fa2:p1:weak-compact-hull` (paper.tex 3171–3224).
Convexity is real; balance uses the original scalar field. All duals use the
original norm topology. The absolutely convex hull includes zero even for the
empty generating set, as stipulated at paper.tex 1194–1195. -/
namespace ExpandedFA.P1.WeakCompactHull.Spec
universe u v
open scoped Pointwise
noncomputable section
abbrev weakTopology := EberleinSmulian.Spec.weakTopology

/-- Real convex hull of the scalar unit-disk saturation together with zero.
This is precisely the convex balanced hull with the manuscript's empty-set convention. -/
def absolutelyConvexHull (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E) : Set E :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  convexHull ℝ (insert 0 (Metric.closedBall (0 : 𝕜) 1 • K))

/-- The disk-saturation construction is the least real-convex, scalar-balanced
set containing zero and K; in particular it is the source's actual hull. -/
def AbsolutelyConvexHullCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E),
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let H := absolutelyConvexHull 𝕜 K
    (0 ∈ H) ∧ (K ⊆ H) ∧ Convex ℝ H ∧ Balanced 𝕜 H ∧
      ∀ A : Set E, 0 ∈ A → K ⊆ A → Convex ℝ A → Balanced 𝕜 A → H ⊆ A

def ConvexHullCompact : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (K : Set E),
    @IsCompact E (weakTopology 𝕜 E) K →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    @IsCompact E (weakTopology 𝕜 E) (closure (convexHull ℝ K))

def AbsolutelyConvexHullCompact : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (K : Set E),
    @IsCompact E (weakTopology 𝕜 E) K →
      @IsCompact E (weakTopology 𝕜 E) (closure (absolutelyConvexHull 𝕜 K))

/-- Both hulls have identical closures in the two topologies. -/
def HullClosureEqualities : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E),
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    (@closure E (weakTopology 𝕜 E) (convexHull ℝ K) = closure (convexHull ℝ K)) ∧
    (@closure E (weakTopology 𝕜 E) (absolutelyConvexHull 𝕜 K) =
      closure (absolutelyConvexHull 𝕜 K))
end
end ExpandedFA.P1.WeakCompactHull.Spec
