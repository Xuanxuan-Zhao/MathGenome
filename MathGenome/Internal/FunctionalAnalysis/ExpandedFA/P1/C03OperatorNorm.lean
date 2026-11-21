import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-! The native operator-space interface for Definition `fa2:p1:c03:operator-norm`.
The aliases keep the native vector operations, operator norm, and topology.
No construction here requires either space to be complete. -/

namespace ExpandedFA.P1.C03OperatorNorm

universe u v

abbrev Operator : Spec.OperatorType :=
  fun 𝕜 E F _ _ _ _ _ => E →L[𝕜] F

abbrev EndOperator : Spec.EndOperatorType.{u, v} :=
  fun 𝕜 E _ _ _ => Operator 𝕜 E E

theorem bounded_operator_identification : Spec.BoundedMapIdentification := by
  intro 𝕜 E F _ _ _ _ _ f
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨‖T‖, norm_nonneg T, T.le_opNorm⟩
  · rintro ⟨C, _, hC⟩
    exact ⟨f.mkContinuous C hC, rfl⟩

theorem operator_unit_ball_nonempty : Spec.UnitBallNonempty := by
  intro 𝕜 E F _ _ _ _ _ T
  have h : ({x : E | ‖x‖ ≤ 1}).Nonempty := ⟨0, by simp⟩
  exact ⟨h, h.image _⟩

theorem operator_norm_supremum : Spec.NormSupremum := by
  intro 𝕜 E F _ _ _ _ _ T
  simpa only [Metric.closedBall, dist_zero_right] using T.sSup_unitClosedBall_eq_norm.symm

theorem operator_norm_infimum : Spec.NormInfimum := by
  intro 𝕜 E F _ _ _ _ _ T
  exact T.norm_def

theorem operator_bounds_nonempty : Spec.BoundsNonempty := by
  intro 𝕜 E F _ _ _ _ _ T
  refine ⟨ContinuousLinearMap.bounds_nonempty, ContinuousLinearMap.bounds_bddBelow, ?_⟩
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact T.unit_le_opNorm x hx

theorem operator_zero_domain : Spec.ZeroDomain := by
  intro 𝕜 E F _ _ _ _ _ _ T
  refine ⟨?_, T.opNorm_subsingleton⟩
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    simp [Subsingleton.elim x 0]
  · intro hy
    have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
    exact ⟨0, by simp, by simp [hy0]⟩

end ExpandedFA.P1.C03OperatorNorm
