import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Independent statement of Riesz's lemma, `fa2:p1:c01:riesz-lemma`
(paper.tex, lines 296–305). The ambient normed space need not be complete.
-/

namespace ExpandedFA.P1.C01RieszLemma.Spec

/-- Every proper closed real or complex linear subspace admits a unit vector
whose distance from the subspace is strictly greater than `θ`, for `0 < θ < 1`.
The distance is the infimum of `dist x m = ‖x - m‖` over `m ∈ M`.
A subspace contains zero, so the set in this infimum is always nonempty. -/
def RieszLemma : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), M ≠ ⊤ → IsClosed (M : Set E) →
    ∀ (θ : ℝ), 0 < θ → θ < 1 →
      ∃ x : E, ‖x‖ = 1 ∧ θ < Metric.infDist x (M : Set E)

end ExpandedFA.P1.C01RieszLemma.Spec
