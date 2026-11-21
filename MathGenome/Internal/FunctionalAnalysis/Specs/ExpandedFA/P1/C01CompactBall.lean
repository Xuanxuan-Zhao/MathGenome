import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for `fa2:p1:c01:compact-ball`, paper.tex lines 308–313.
Both compactness notions refer to the topology induced by the displayed norm.
`RCLike` includes both real and complex scalars. No completeness or nontriviality
of the vector space is assumed, so the zero-dimensional case is included.
-/

namespace ExpandedFA.P1.C01CompactBall.Spec

/-- Compactness of the closed unit ball characterizes finite dimension. -/
def CompactClosedUnitBall : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsCompact (Metric.closedBall (0 : E) 1) ↔ FiniteDimensional 𝕜 E

/-- Local compactness of the norm topology characterizes finite dimension. -/
def LocalCompactness : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    LocallyCompactSpace E ↔ FiniteDimensional 𝕜 E

end ExpandedFA.P1.C01CompactBall.Spec
