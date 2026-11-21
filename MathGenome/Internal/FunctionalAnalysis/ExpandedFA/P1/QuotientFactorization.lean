import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.QuotientFactorization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm

/-! Unique algebraic and norm-preserving bounded quotient factorizations. -/

noncomputable section

namespace ExpandedFA.P1.QuotientFactorization

theorem quotient_algebraic_factorization : Spec.AlgebraicFactorization := by
  intro 𝕜 E F _ _ _ _ _ M T hT
  let h : M ≤ T.ker := hT
  refine ⟨M.liftQ T h, fun _ => rfl, ?_⟩
  intro V hV
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := M.mkQ_surjective z
  exact hV x

/-- The induced algebraic map obeys the operator bound for the distance
seminorm, even without closedness of the subspace. -/
theorem quotient_lift_bound {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (M : Submodule 𝕜 E) (T : E →L[𝕜] F) (h : M ≤ T.ker)
    (z : E ⧸ M) : ‖M.liftQ T.toLinearMap h z‖ ≤ ‖T‖ * ‖z‖ := by
  let f : NormedAddGroupHom E F :=
    { T.toLinearMap.toAddMonoidHom with bound' := ⟨‖T‖, T.le_opNorm⟩ }
  have hf : ∀ x ∈ M.toAddSubgroup, f x = 0 := fun x hx => h hx
  have hf_norm : ‖f‖ ≤ ‖T‖ :=
    NormedAddGroupHom.opNorm_le_bound f (norm_nonneg T) T.le_opNorm
  exact (QuotientAddGroup.norm_lift_apply_le f hf z).trans
    (mul_le_mul_of_nonneg_right hf_norm (norm_nonneg z))

theorem quotient_bounded_factorization : Spec.BoundedFactorization := by
  intro 𝕜 E F _ _ _ _ _ M hM
  letI : IsClosed (M : Set E) := hM
  intro T hT
  let h : M ≤ T.ker := hT
  let U : (E ⧸ M) →L[𝕜] F :=
    (M.liftQ T.toLinearMap h).mkContinuous ‖T‖ (quotient_lift_bound M T h)
  have hU : ∀ x : E, U (M.mkQ x) = T x := fun _ => rfl
  refine ⟨U, hU, le_antisymm ?_ ?_, ?_⟩
  · exact U.opNorm_le_bound (norm_nonneg T) (quotient_lift_bound M T h)
  · apply T.opNorm_le_bound (norm_nonneg U)
    intro x
    calc
      ‖T x‖ = ‖U (M.mkQ x)‖ := congrArg norm (hU x).symm
      _ ≤ ‖U‖ * ‖M.mkQ x‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le M x) (norm_nonneg U)
  · intro V hV
    apply ContinuousLinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := M.mkQ_surjective z
    exact (hV x).trans (hU x).symm

end ExpandedFA.P1.QuotientFactorization
