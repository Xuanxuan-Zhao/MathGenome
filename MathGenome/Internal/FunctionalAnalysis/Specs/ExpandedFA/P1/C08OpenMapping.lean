import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-!
Independent statements for Theorem `fa2:p1:c08:open-mapping`, paper.tex
1537–1548. The native `CompleteSpace` condition is the Banach condition
identified in the shared C01Banach. The maps are the native
continuous linear maps fixed by C03OperatorNorm, with the original norm topology.
`RCLike` includes both real and complex scalars. Neither vector space is
required to be nonzero, and surjectivity is the only algebraic hypothesis on T.
-/

namespace ExpandedFA.P1.C08OpenMapping.Spec

universe u v w

/-- Every open set has open image under a surjective bounded linear map
between Banach spaces. -/
def OpenMapping : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Surjective T →
      ∀ U : Set E, IsOpen U → IsOpen (T '' U)

/-- The actual image of the open unit ball contains a positive open ball
at zero; there is no closure on the image. -/
def UnitBallImage : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Surjective T →
      ∃ c : ℝ, 0 < c ∧ Metric.ball (0 : F) c ⊆ T '' Metric.ball (0 : E) 1

/-- One positive constant works for every target vector, with an exact
preimage and a non-strict norm estimate. No regularity of a selection is imposed. -/
def ControlledPreimages : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Surjective T →
      ∃ C : ℝ, 0 < C ∧ ∀ y : F, ∃ x : E, T x = y ∧ ‖x‖ ≤ C * ‖y‖

end ExpandedFA.P1.C08OpenMapping.Spec
