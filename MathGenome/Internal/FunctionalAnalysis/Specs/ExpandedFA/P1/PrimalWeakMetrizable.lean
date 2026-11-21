import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13ConverseMetric

/-! Independent statements for paper.tex 3265–3270. All balls are closed
norm unit balls, carrying the relative weak or weak-star topology. The dual
is always formed using the original norm topology. No completeness is assumed. -/
namespace ExpandedFA.P1.PrimalWeakMetrizable.Spec
universe u v
open TopologicalSpace
noncomputable section

def PrimalBallMetrizable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  @MetrizableSpace (Metric.closedBall (0 : E) 1)
    (TopologicalSpace.induced Subtype.val
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)))

def PrimalCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    PrimalBallMetrizable 𝕜 E ↔ SeparableSpace (E →L[𝕜] 𝕜)

def DualCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C13ConverseMetric.Spec.BallMetrizable 𝕜 E ↔ SeparableSpace E
end
end ExpandedFA.P1.PrimalWeakMetrizable.Spec
