import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for Example `fa2:p1:c24:topology-example`, paper.tex:5033–5046.
The weak topology is σ(H,H′), with H′ the original norm-continuous scalar-linear
 dual. The norm, its topology and its unit ball are fixed before forming that
topology. Convex combinations and extreme points use real scalars for either
field. Hilbert means complete; no separability is assumed.
-/

universe u v
namespace ExpandedFA.P1.C24TopologyExample.Spec

/-- Compactness in the specified weak topology. -/
def WeakCompactUnitBall : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H →
    @IsCompact H
      (C12DualPairSpec.DualPairTopologyValue 𝕜 H (H →L[𝕜] 𝕜) (topDualPairing 𝕜 H))
      {x : H | ‖x‖ ≤ 1}

/-- Real extreme points of the closed unit ball are its unit sphere. -/
def ExtremeUnitBall : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H →
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
    C24FacesSpec.extremePoints {x : H | ‖x‖ ≤ 1} = {x : H | ‖x‖ = 1}

/-- Krein–Milman here closes finite real convex combinations in σ(H,H′). -/
def WeakClosedConvexHull : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H →
    letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
    {x : H | ‖x‖ ≤ 1} =
      @closure H
        (C12DualPairSpec.DualPairTopologyValue 𝕜 H (H →L[𝕜] 𝕜) (topDualPairing 𝕜 H))
        (convexHull ℝ {x : H | ‖x‖ = 1})

/-- This same unit ball is not compact in the original norm topology. -/
def NormNotCompact : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ¬ FiniteDimensional 𝕜 H → ¬ IsCompact {x : H | ‖x‖ ≤ 1}

end ExpandedFA.P1.C24TopologyExample.Spec
