import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ClusterPt

/-!
Independent statements for the cluster-point implication of Eberlein–Šmulian,
`fa2:p1:eberlein-smulian`, paper.tex 3125–3141. The dual and norm structures
are those of the original real or complex normed space. Cluster points and
subsequence limits belong to E, with no completeness assumption. A sequence
clusters when every neighborhood is visited arbitrarily far out, expressed by
`ClusterPt x (Filter.map s atTop)`. No membership of the cluster point in A
is required. Empty sets and zero spaces are included.
-/

namespace ExpandedFA.P1.WeakClusterToSubsequence.Spec

universe u v
open Filter
open scoped Topology

/-- Relative weak sequential cluster compactness implies norm boundedness. -/
def ClusterImpliesBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    (∀ s : ℕ → E, (∀ n, s n ∈ A) → ∃ x : E,
      @ClusterPt E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
        x (map s atTop)) →
    Bornology.IsBounded A

/-- Every sequence in A admits a weakly convergent subsequence in E. -/
def ClusterImpliesSubsequence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    (∀ s : ℕ → E, (∀ n, s n ∈ A) → ∃ x : E,
      @ClusterPt E
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
        x (map s atTop)) →
    ∀ s : ℕ → E, (∀ n, s n ∈ A) →
      ∃ (x : E) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (s ∘ φ) atTop
          (@nhds E
            (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x)

end ExpandedFA.P1.WeakClusterToSubsequence.Spec
