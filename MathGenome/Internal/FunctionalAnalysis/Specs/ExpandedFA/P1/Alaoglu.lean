import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Compactness.Compact

/-!
Independent statements for `fa2:p1:alaoglu`, paper.tex:2119–2137.
The dual is always the continuous scalar-linear dual of the given topology.
The general weak-star topology is the accepted dual-pair topology of evaluation;
it makes sense on an arbitrary TVS, with no norm or local convexity assumption.
Equicontinuity uses the usual scalar uniformity and all points of E.
The normed corollary uses exactly the accepted normed weak-star topology.
No completeness, separability, nonzero-space, or nonempty-family assumption occurs.
-/

namespace ExpandedFA.P1.Alaoglu.Spec

universe u v
open scoped Topology
noncomputable section

/-- Evaluation topology on the continuous dual of the original topological space. -/
def weakStarTopology (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] :
    TopologicalSpace (E →L[𝕜] 𝕜) :=
  C12DualPairSpec.DualPairTopologyValue 𝕜 (E →L[𝕜] 𝕜) E
    (topDualPairing 𝕜 E).flip

/-- The polar uses absolute value (the scalar norm), including for complex scalars. -/
def polar (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    (U : Set E) : Set (E →L[𝕜] 𝕜) :=
  {f | ∀ x ∈ U, ‖f x‖ ≤ 1}

/-- Neighborhood polars in every Hausdorff real or complex TVS are weak-star compact. -/
def NeighborhoodPolarCompactness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    (U : Set E), U ∈ 𝓝 (0 : E) →
    @IsCompact (E →L[𝕜] 𝕜) (weakStarTopology 𝕜 E) (polar 𝕜 U)

/-- Every equicontinuous family lies in the polar of a single zero neighborhood. -/
def EquicontinuousPolarContainment : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    (A : Set (E →L[𝕜] 𝕜)),
    Equicontinuous (fun f : A => (f.1 : E → 𝕜)) →
    ∃ U ∈ 𝓝 (0 : E), A ⊆ polar 𝕜 U

/-- The closed dual unit ball of any normed predual is weak-star compact. -/
def UnitBallCompactness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    @IsCompact (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ 1}

end
end ExpandedFA.P1.Alaoglu.Spec
