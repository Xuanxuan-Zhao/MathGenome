import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statement of fa2:p1:c13:subsequences, paper.tex 2600–2604.
The sequence consists of norm-continuous scalar-linear functionals for the
original norm on E. Its range is bounded in the operator norm, and convergence
uses exactly σ(E′, E). Neither completeness of E nor separability of E′ is
assumed. Natural indices simply reindex the manuscript's sequence. -/

namespace ExpandedFA.P1.C13Subsequences.Spec

universe u v
open scoped Topology

/-- A bounded sequence in the dual of a separable normed space admits a
strictly increasing subsequence converging weak-star to a continuous functional. -/
def SubsequenceConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]
    (f : ℕ → (E →L[𝕜] 𝕜)), Bornology.IsBounded (Set.range f) →
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ g : E →L[𝕜] 𝕜,
      Filter.Tendsto (f ∘ k) Filter.atTop
        (@nhds (E →L[𝕜] 𝕜)
          (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) g)

end ExpandedFA.P1.C13Subsequences.Spec
