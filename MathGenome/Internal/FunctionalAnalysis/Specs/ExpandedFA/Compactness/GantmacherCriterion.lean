import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! The three equivalent conditions in `fa2:p2:gantmacher`.
The chapter assumes Banach spaces over ℝ or ℂ. Duals are the original
norm-continuous scalar-linear duals. `WeakDual 𝕜 Y` carries σ(Y′,Y),
whereas `WeakSpace 𝕜 (X →L[𝕜] 𝕜)` carries σ(X′,X″).
The bidual condition quantifies over every element of X″.
-/
namespace ExpandedFA.Compactness.GantmacherCriterion.Spec
universe u v w
noncomputable section

/-- The full image of the second transpose lies in the canonical image of Y. -/
def BidualRange (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y) : Prop :=
  ∀ ξ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜, ∃ y : Y,
    P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 (Y →L[𝕜] 𝕜) (X →L[𝕜] 𝕜)
      (P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 X Y T) ξ =
        P1.C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 Y y

def WeakCompactIffBidualRange : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y),
    DefinitionsSpec.IsWeaklyCompactOperatorValue T ↔ BidualRange 𝕜 X Y T

/-- Continuity for the actual weak-star domain and weak codomain topologies. -/
def BidualRangeIffAdjointContinuity : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y),
    BidualRange 𝕜 X Y T ↔
      Continuous (fun f : WeakDual 𝕜 Y => toWeakSpace 𝕜 (X →L[𝕜] 𝕜)
        (P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 X Y T
          (WeakDual.toStrongDual f)))

end
end ExpandedFA.Compactness.GantmacherCriterion.Spec
