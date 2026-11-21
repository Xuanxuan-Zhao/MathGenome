import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactness.Compact

/-!
Independent statements for `fa2:p1:c14:ball-characterization`, paper.tex 2733–2751.
The norm, continuous linear dual, and canonical evaluation are fixed by the
original normed-space structure. All compactness and closedness below use
precisely σ(E,E′). Boundedness uses the original norm bornology. No separability,
nontriviality, or nonemptiness assumption is imposed.
-/
namespace ExpandedFA.P1.C14BallCharacterization.Spec
universe u v

/-- The canonical map is onto exactly when the norm-closed unit ball is weakly compact. -/
def ReflexiveIffCompactBall : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
        {x : E | ‖x‖ ≤ 1}

/-- Compactness of the unit ball is equivalent to compactness of every
norm-bounded weakly closed set, including the empty set. -/
def CompactBallIffClosedBounded : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      {x : E | ‖x‖ ≤ 1} ↔
    ∀ A : Set E, Bornology.IsBounded A →
      @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A →
      @IsCompact E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) A

end ExpandedFA.P1.C14BallCharacterization.Spec
