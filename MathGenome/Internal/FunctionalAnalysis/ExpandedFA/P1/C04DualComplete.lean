import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04DualComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorComplete

/-!
Completeness and evaluation for the continuous linear dual.

Specialize the accepted complete-target operator theorem to the complete
scalar field. The domain remains an arbitrary normed space throughout.
The evaluation inequality is the operator-norm bound for a scalar-valued map.
-/

namespace ExpandedFA.P1.C04DualComplete

universe u v

theorem dual_completeSpace : Spec.DualCompleteSpace.{u, v} := by
  intro 𝕜 E _ _ _
  change CompleteSpace (C04Dual.ContinuousDual 𝕜 E)
  exact C03OperatorComplete.operator_completeSpace 𝕜 E 𝕜

theorem dual_banach : Spec.DualBanach.{u, v} := by
  intro 𝕜 E _ _ _
  change C01Banach.IsBanachSpace (C04Dual.ContinuousDual 𝕜 E)
  exact C03OperatorComplete.operator_banach 𝕜 E 𝕜
    ((C01Banach.isBanachSpace_iff_completeSpace 𝕜).mpr inferInstance)

theorem dual_evaluation_bound : Spec.EvaluationBound.{u, v} := by
  intro 𝕜 E _ _ _ f x
  exact f.le_opNorm x

end ExpandedFA.P1.C04DualComplete
