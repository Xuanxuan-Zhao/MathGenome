import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08EquivalentNorms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse

namespace ExpandedFA.P1.C08EquivalentNorms

/-- A one-sided norm bound for an algebraic equivalence of Banach spaces
makes it a homeomorphism and supplies the reverse norm bound. -/
theorem compare_banach_equiv
    (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (e : E ≃ₗ[𝕜] F) (C : ℝ) (hC : ∀ x, ‖e x‖ ≤ C * ‖x‖) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      (∀ x, ‖e x‖ ≤ A * ‖x‖) ∧ (∀ x, ‖x‖ ≤ D * ‖e x‖) ∧
      TopologicalSpace.induced e inferInstance = (inferInstance : TopologicalSpace E) := by
  let T : E →L[𝕜] F := e.toLinearMap.mkContinuous C hC
  obtain ⟨S, hST, hTS, _⟩ :=
    ExpandedFA.P1.C08BoundedInverse.bounded_inverse 𝕜 E F T e.bijective
  have hSe : ∀ y, S y = e.symm y := by
    intro y
    apply e.injective
    exact (hTS y).trans (e.apply_symm_apply y).symm
  let h : E ≃ₜ F :=
    { e.toEquiv with
      continuous_toFun := T.continuous
      continuous_invFun := by
        change Continuous (fun y => e.symm y)
        have heq : (fun y => e.symm y) = (fun y => S y) :=
          funext (fun y => (hSe y).symm)
        rw [heq]
        exact S.continuous }
  refine ⟨max C 1, ‖S‖ + 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    by positivity, ?_, ?_, h.induced_eq⟩
  · intro x
    exact (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  · intro x
    calc
      ‖x‖ = ‖S (T x)‖ := congrArg norm (hST x).symm
      _ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm _
      _ ≤ (‖S‖ + 1) * ‖e x‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

/-- Comparison of the two complete norms, including mutual bounds and
identity of their induced topologies on the original vector space. -/
theorem equivalent_complete_norms : Spec.EquivalentCompleteNorms := by
  intro 𝕜 E _ _ m p q hp hq hcompletep hcompleteq C hC
  let np : @NormedSpace 𝕜 E _ (C01Norm.normedGroup p hp).toSeminormedAddCommGroup :=
    letI := C01Norm.normedGroup p hp
    { m with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }
  let nq : @NormedSpace 𝕜 E _ (C01Norm.normedGroup q hq).toSeminormedAddCommGroup :=
    letI := C01Norm.normedGroup q hq
    { m with norm_smul_le := fun a x => (map_smul_eq_mul q a x).le }
  obtain ⟨A, D, hA, hD, hforward, hreverse, htop⟩ :=
    @compare_banach_equiv 𝕜 E E _ (C01Norm.normedGroup p hp) (C01Norm.normedGroup q hq)
      np nq hcompletep hcompleteq (LinearEquiv.refl 𝕜 E) C hC
  refine ⟨A, D, hA, hD, hforward, hreverse, ?_⟩
  change TopologicalSpace.induced id (C01Norm.normedGroup q hq).toUniformSpace.toTopologicalSpace =
    (C01Norm.normedGroup p hp).toUniformSpace.toTopologicalSpace at htop
  simpa only [induced_id] using htop.symm

end ExpandedFA.P1.C08EquivalentNorms
