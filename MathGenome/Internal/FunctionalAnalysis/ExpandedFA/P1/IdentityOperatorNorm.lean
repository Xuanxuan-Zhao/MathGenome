import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.IdentityOperatorNorm

/-! The norm of the identity, including the zero-space boundary case. -/

namespace ExpandedFA.P1.IdentityOperatorNorm

theorem operator_identity_norm_nontrivial : Spec.IdentityNormNontrivial := by
  intro 𝕜 E _ _ _ _
  exact ContinuousLinearMap.norm_id

theorem operator_identity_norm_subsingleton : Spec.IdentityNormSubsingleton := by
  intro 𝕜 E _ _ _ _
  exact (ContinuousLinearMap.id 𝕜 E).opNorm_subsingleton

end ExpandedFA.P1.IdentityOperatorNorm
