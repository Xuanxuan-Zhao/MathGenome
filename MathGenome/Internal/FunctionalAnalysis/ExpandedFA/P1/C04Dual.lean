import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm

/-! The continuous linear dual, algebraic dual, and bidual of Definition
`fa2:p1:c04:dual`. These aliases preserve the native structures and can be used
directly as the corresponding Mathlib spaces in downstream results. -/

namespace ExpandedFA.P1.C04Dual

universe u v

/-- The continuous linear dual E′ = L(E, 𝕜), using the shared operator space. -/
abbrev ContinuousDual : Spec.ContinuousDualType.{u, v} :=
  fun 𝕜 E _ _ _ => C03OperatorNorm.Operator 𝕜 E 𝕜

/-- The algebraic dual: all scalar-linear maps, without a continuity condition. -/
abbrev AlgebraicDual : Spec.AlgebraicDualType.{u, v} :=
  fun 𝕜 E _ _ _ => E →ₗ[𝕜] 𝕜

/-- The bidual E″ = (E′)′, using the dual's operator norm topology. -/
abbrev Bidual : Spec.BidualType.{u, v} :=
  fun 𝕜 E _ _ _ => ContinuousDual 𝕜 (ContinuousDual 𝕜 E)

theorem dual_norm_supremum : Spec.DualNormSupremum.{u, v} := by
  intro 𝕜 E _ _ _ f
  exact C03OperatorNorm.operator_norm_supremum 𝕜 E 𝕜 f

end ExpandedFA.P1.C04Dual
