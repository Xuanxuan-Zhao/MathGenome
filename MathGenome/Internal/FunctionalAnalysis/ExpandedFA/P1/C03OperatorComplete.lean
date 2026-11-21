import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach

/-!
A Banach target suffices for completeness of the operator space.

Mathlib's `ContinuousLinearMap.instCompleteSpace` requires a sequential
domain (automatic for a normed space), but does not require its completeness.
The uniformity used by this instance is also the operator-norm uniformity:
`ContinuousLinearMap.toPseudoMetricSpace` preserves that uniformity when
installing the operator-norm metric. Thus the library result applies to
the original norm, without replacing any norm or topology.
-/

namespace ExpandedFA.P1.C03OperatorComplete

theorem operator_completeSpace : Spec.CompleteTarget := by
  intro 𝕜 E F _ _ _ _ _ _
  infer_instance

theorem operator_banach : Spec.BanachTarget := by
  intro 𝕜 E F _ _ _ _ _ hF
  letI : CompleteSpace F := (C01Banach.isBanachSpace_iff_completeSpace F).mp hF
  letI : CompleteSpace (C03OperatorNorm.Operator 𝕜 E F) := operator_completeSpace 𝕜 E F
  exact (C01Banach.isBanachSpace_iff_completeSpace
    (C03OperatorNorm.Operator 𝕜 E F)).mpr inferInstance

end ExpandedFA.P1.C03OperatorComplete
