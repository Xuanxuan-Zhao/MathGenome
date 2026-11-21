import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04EvaluationContractive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorEstimates

/-!
Evaluation is continuous and scalar-linear in both variables. Its norm bound
uses the operator evaluation estimate and the operator norm upper-bound
criterion, without norming functionals or completeness of the domain.
-/

namespace ExpandedFA.P1.C04EvaluationContractive

universe u v

theorem evaluation_continuous_linear : Spec.EvaluationContinuousLinear.{u, v} := by
  intro 𝕜 E _ _ _ x
  exact ⟨(C04CanonicalMap.canonicalEvaluation 𝕜 E x).continuous,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem canonicalEvaluation_continuous_linear :
    Spec.CanonicalEvaluationContinuousLinear.{u, v} := by
  intro 𝕜 E _ _ _
  exact ⟨(C04CanonicalMap.canonicalEvaluation 𝕜 E).continuous,
    fun x y => (C04CanonicalMap.canonicalEvaluation 𝕜 E).map_add x y,
    fun a x => (C04CanonicalMap.canonicalEvaluation 𝕜 E).map_smul a x⟩

theorem canonicalEvaluation_norm_le : Spec.CanonicalEvaluationContractive.{u, v} := by
  intro 𝕜 E _ _ _ x
  change ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ ≤ ‖x‖
  apply (C04CanonicalMap.canonicalEvaluation 𝕜 E x).opNorm_le_bound (norm_nonneg x)
  intro f
  calc
    ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x f‖ = ‖f x‖ := rfl
    _ ≤ ‖f‖ * ‖x‖ := C03OperatorEstimates.operator_evaluation_bound 𝕜 E 𝕜 f x
    _ = ‖x‖ * ‖f‖ := mul_comm _ _

end ExpandedFA.P1.C04EvaluationContractive
