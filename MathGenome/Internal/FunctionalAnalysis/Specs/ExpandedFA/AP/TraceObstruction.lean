import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Independent statement of `fa2:ap:trace-obstruction` (paper.tex:12630–12640).
The dual is the continuous scalar-linear dual, over either ℝ or ℂ.
The sole summability hypothesis implies absolute convergence of both series.
No bound on the norms of the AP approximants is assumed. -/
namespace ExpandedFA.AP.TraceObstructionSpec

universe u v
open scoped Topology

/-- A zero operator represented by an absolutely summable rank-one series
with nonzero scalar trace obstructs the ordinary approximation property. -/
def TraceObstruction : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (X : Type v)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (f : ℕ → X →L[𝕜] 𝕜) (x : ℕ → X),
    Summable (fun j => ‖f j‖ * ‖x j‖) →
    (∀ z : X, (∑' j, (f j z) • x j) = 0) →
    (∑' j, f j (x j)) ≠ 0 →
    ¬ Compactness.ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X

end ExpandedFA.AP.TraceObstructionSpec
