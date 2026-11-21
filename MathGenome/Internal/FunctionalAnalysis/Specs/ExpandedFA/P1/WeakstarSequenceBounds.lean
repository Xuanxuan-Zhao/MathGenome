import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
The dual clauses of `fa2:p1:c12:bounded-sequences` and `fa2:p1:c12:norm-lsc`
(paper.tex 2363–2385, 2400–2411). The dual is the original continuous
scalar-linear dual with its operator norm. Convergence and closedness use
its separately specified weak-star topology σ(E′, E).

Only sequence boundedness and the real-valued liminf statement require a
Banach predual. Closed balls have arbitrary centers and real radii, including
zero and negative radii, and require no completeness. Zero spaces are allowed.
-/

namespace ExpandedFA.P1.WeakstarSequenceBounds.Spec

universe u v
open Filter
open scoped Topology
noncomputable section

/-- The entire weak-star convergent sequence has a finite norm bound. -/
def SequenceBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (s : ℕ → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto s atTop
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖s n‖ ≤ C

/-- Uniform boundedness makes the real norm liminf well behaved. -/
def SequenceNormLiminf : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (s : ℕ → (E →L[𝕜] 𝕜)) (f : E →L[𝕜] 𝕜),
    Tendsto s atTop
      (@nhds (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E) f) →
    ‖f‖ ≤ liminf (fun n => ‖s n‖) atTop

/-- Every norm-closed dual ball is weak-star closed, even for incomplete E. -/
def ClosedDualBalls : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f₀ : E →L[𝕜] 𝕜) (r : ℝ),
    @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (Metric.closedBall f₀ r)

end
end ExpandedFA.P1.WeakstarSequenceBounds.Spec
