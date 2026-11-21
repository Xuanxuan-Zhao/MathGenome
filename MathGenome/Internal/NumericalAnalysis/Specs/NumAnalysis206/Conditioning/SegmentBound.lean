import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.RCLike.Basic

namespace Specs.NumAnalysis206.Conditioning

/-- The finite estimate in W13 (paper.tex, lines 448–451).
The segment is a real segment, also when the spaces are complex.
Differentiation is only required along the segment away from its endpoints;
there is no endpoint derivative hypothesis, including when `v = 0`.
A specified continuous linear derivative avoids imposing uniqueness of a
within-derivative on a segment of positive ambient codimension. -/
def segmentForwardBoundType : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (X Y : Type) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X → Y) (D : X → X →L[𝕜] Y) (x v : X) (L : ℝ),
    letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
    0 ≤ L →
    ContinuousOn f (segment ℝ x (x + v)) →
    (∀ z ∈ segment ℝ x (x + v), z ≠ x → z ≠ x + v →
      HasFDerivWithinAt f (D z) (segment ℝ x (x + v)) z) →
    (∀ z ∈ segment ℝ x (x + v), z ≠ x → z ≠ x + v → ‖D z‖ ≤ L) →
    ‖f (x + v) - f x‖ ≤ L * ‖v‖

end Specs.NumAnalysis206.Conditioning
