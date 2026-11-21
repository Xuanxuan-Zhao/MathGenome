import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach

/-!
Independent specification of the completeness clause of
`fa2:p1:c05:bidual-isometry`, paper.tex:967–979.
The range is that of the shared scalar-linear evaluation map in the
continuous linear bidual with its operator norm topology. Banach means
convergence of every norm Cauchy sequence in the given norm. No
completeness or nontriviality of the original space is assumed.
-/

namespace ExpandedFA.P1.BidualClosedImage.Spec

universe u v

/-- The canonical image is norm closed if and only if the domain is Banach. -/
def CanonicalEvaluationClosedRangeIffBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsClosed (Set.range (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)) ↔
      C01Banach.Spec.IsBanachSpaceValue E

/-- Surjectivity of the canonical evaluation map forces completeness. -/
def ReflexiveBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C01Banach.Spec.IsBanachSpaceValue E

end ExpandedFA.P1.BidualClosedImage.Spec
