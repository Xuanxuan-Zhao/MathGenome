import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar

/-!
Independent statements of the closed-ball clauses of
`fa2:p1:c12:norm-lsc`, paper.tex 2400–2411.
The norms and continuous scalar-linear dual are fixed using the original
normed space. Only closedness uses the weak or weak-star topology.
Centers and real radii are arbitrary, including zero and negative radii;
there is no completeness or nontriviality assumption.
-/

namespace ExpandedFA.P1.WeakClosedBalls.Spec

universe u v

def WeakClosedBalls : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (c : E) (r : ℝ),
    @IsClosed E
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E))
      {x : E | ‖x - c‖ ≤ r}

def WeakStarClosedBalls : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (c : E →L[𝕜] 𝕜) (r : ℝ),
    @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      {f : E →L[𝕜] 𝕜 | ‖f - c‖ ≤ r}

end ExpandedFA.P1.WeakClosedBalls.Spec
