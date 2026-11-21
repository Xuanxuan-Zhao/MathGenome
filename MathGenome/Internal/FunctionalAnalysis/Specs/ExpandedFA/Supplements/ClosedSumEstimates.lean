import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.RCLike.Basic

/-! Independent statements of the four primal conditions of
`fa2:p1:closed-sums`, paper.tex:6272–6287. `⊔` is the algebraic sum of
submodules; `⊓` is their intersection. Distances are infima, with no
nearest-point assumption. The scalar field includes both ℝ and ℂ, and
neither the ambient space nor either subspace is required to be nonzero.
The dual assertions of the source theorem belong to a separate goal. -/

universe u v
namespace ExpandedFA.Supplements.ClosedSumEstimates.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One positive constant controls exact decompositions of every vector
in the algebraic sum, measured by the sum of the two component norms. -/
def DecompositionBound (G L : Submodule 𝕜 E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : E, x ∈ G ⊔ L →
    ∃ g ∈ G, ∃ l ∈ L, g + l = x ∧ ‖g‖ + ‖l‖ ≤ C * ‖x‖

/-- Distance from g ∈ G to the intersection is controlled by distance to L. -/
def SubspaceDistanceBound (G L : Submodule 𝕜 E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : E, g ∈ G →
    Metric.infDist g (↑(G ⊓ L) : Set E) ≤ C * Metric.infDist g (L : Set E)

/-- The distance inequality holds for every ambient vector, including
vectors outside the algebraic sum. -/
def AmbientDistanceBound (G L : Submodule 𝕜 E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : E,
    Metric.infDist x (↑(G ⊓ L) : Set E) ≤
      C * (Metric.infDist x (G : Set E) + Metric.infDist x (L : Set E))

/-- All four conditions, with constants allowed to vary between them. -/
def ClosedSumEquivalences : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (G L : Submodule 𝕜 E), IsClosed (G : Set E) → IsClosed (L : Set E) →
      (IsClosed (↑(G ⊔ L) : Set E) ↔ DecompositionBound G L) ∧
      (DecompositionBound G L ↔ SubspaceDistanceBound G L) ∧
      (SubspaceDistanceBound G L ↔ AmbientDistanceBound G L)

end ExpandedFA.Supplements.ClosedSumEstimates.Spec
