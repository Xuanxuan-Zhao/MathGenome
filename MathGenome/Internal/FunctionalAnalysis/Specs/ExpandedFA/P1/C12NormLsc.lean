import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12ConvexClosure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakClosedBalls
import Mathlib.Order.WithBot
import Mathlib.Topology.Semicontinuity.Basic

/-!
Independent statements for `fa2:p1:c12:norm-lsc` (paper.tex 2400–2415).
The codomain `WithTop ℝ` is exactly ℝ ∪ {+∞}, excluding −∞. As specified
in paper.tex 1264–1274, convexity means convexity of the finite-height
epigraph in E × ℝ. This includes the identically +∞ function and does
not assume properness. Convexity is real also for complex E.
The dual and all norms are formed using the original norm topology;
only the conclusion's topology is changed to σ(E,E′).
-/

namespace ExpandedFA.P1.C12NormLsc.Spec

universe u v

/-- Norm-lower-semicontinuous convex extended-real functions are weakly
lower semicontinuous, without a completeness or properness assumption. -/
def ConvexWeakLowerSemicontinuous : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ Φ : E → WithTop ℝ,
      Convex ℝ {p : E × ℝ | Φ p.1 ≤ (p.2 : WithTop ℝ)} →
      LowerSemicontinuous Φ →
      @LowerSemicontinuous E (WithTop ℝ)
        (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
          (topDualPairing 𝕜 E)) inferInstance Φ

/-- All centers and real radii, including empty negative-radius balls. -/
def WeakClosedBalls : Prop := WeakClosedBalls.Spec.WeakClosedBalls.{u,v}

/-- All dual centers and real radii in the specified weak-star topology. -/
def WeakStarClosedBalls : Prop := WeakClosedBalls.Spec.WeakStarClosedBalls.{u,v}

end ExpandedFA.P1.C12NormLsc.Spec
