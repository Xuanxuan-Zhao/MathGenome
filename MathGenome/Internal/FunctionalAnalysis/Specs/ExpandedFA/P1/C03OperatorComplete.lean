import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent statements for `fa2:p1:c03:operator-complete`, paper.tex 648–652.

The operator space is the native continuous linear map space, with exactly
the operator norm fixed in C03OperatorNorm. Only the target is complete:
the domain is an arbitrary normed space, including the zero space.
`RCLike` covers both real and complex scalars.
-/

namespace ExpandedFA.P1.C03OperatorComplete.Spec

universe u v w

/-- Completeness in the canonical operator-norm uniformity. -/
def CompleteTarget : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (E →L[𝕜] F)

/-- The same conclusion in the manuscript's sequential Banach definition. -/
def BanachTarget : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    C01Banach.Spec.IsBanachSpaceValue F →
      C01Banach.Spec.IsBanachSpaceValue (E →L[𝕜] F)

end ExpandedFA.P1.C03OperatorComplete.Spec
