import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Metric
import Mathlib.Topology.Metrizable.Basic

/-! Independent statements for fa2:p1:c13:converse-metric, paper.tex 2632–2637.
The ball is the closed operator-norm unit ball of the continuous linear dual
of the original normed space. Its topology is explicitly the relative
σ(E′, E) topology from the shared pairing interface. Separability refers
to the original norm topology on E. Completeness and nontriviality are
not assumed, and no separability condition is placed on the normed dual. -/

namespace ExpandedFA.P1.C13ConverseMetric.Spec

universe u v
open TopologicalSpace
noncomputable section

def BallMetrizable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  @MetrizableSpace (Metric.closedBall (0 : E →L[𝕜] 𝕜) 1)
    (TopologicalSpace.induced Subtype.val
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E))

def Converse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    BallMetrizable 𝕜 E → SeparableSpace E

def Characterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    BallMetrizable 𝕜 E ↔ SeparableSpace E

end
end ExpandedFA.P1.C13ConverseMetric.Spec
