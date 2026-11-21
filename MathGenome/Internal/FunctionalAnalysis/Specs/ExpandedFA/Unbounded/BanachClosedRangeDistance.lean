import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statement of the distance assertion in
`fa2:p3:banach-closed-range`, paper.tex 13586–13612.
The kernel is a subspace of the original ambient space X, and `infDist`
uses its original norm metric. Both real and complex scalars, arbitrary
closed dense domains, and zero spaces are included. -/

namespace ExpandedFA.Unbounded.BanachClosedRangeDistanceSpec

def ClosedRangeDistance : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
      (_root_.IsClosed (A.toFun.range : Set Y) ↔
        ∃ C : ℝ, 0 < C ∧ ∀ x : A.domain,
          Metric.infDist (x : X) (A.ker : Set X) ≤ C * ‖A x‖)

end ExpandedFA.Unbounded.BanachClosedRangeDistanceSpec
