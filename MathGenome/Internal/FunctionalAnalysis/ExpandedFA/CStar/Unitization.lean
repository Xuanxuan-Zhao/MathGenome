import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.Conventions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NeumannResolvent
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Unitization
import Mathlib.Analysis.Normed.Operator.Banach

/-! The C*-unitization norm (paper.tex:12049–12079).
The native C*-norm is used throughout; the new scalar estimate identifies
it with the left-action norm precisely in the genuinely nonunital case. -/
noncomputable section
namespace ExpandedFA.CStar.Unitization
universe u

abbrev NoIdentity : Spec.NoIdentityType.{u} := Spec.NoIdentityValue
abbrev leftAction : Spec.LeftActionType.{u} := Spec.LeftActionValue

theorem left_action_formula : Spec.LeftActionFormula.{u} := by
  intro A _ x a
  change x.fst • a + x.snd * a = _
  exact add_comm _ _

theorem left_multiplication_norm : Spec.LeftMultiplicationNorm.{u} := by
  intro A _ a
  exact ContinuousLinearMap.opNorm_mul_apply ℂ A a

private theorem identity_of_left_identity {A : Type u} [NonUnitalCStarAlgebra A]
    (e : A) (he : ∀ a : A, e * a = a) :
    ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a := by
  have hr (a : A) : a * star e = a := by
    simpa only [star_mul, star_star] using congrArg star (he (star a))
  have hs : e = star e := (hr e).symm.trans (he (star e))
  exact ⟨e, fun a => ⟨he a, hs.symm ▸ hr a⟩⟩

private theorem identity_of_isUnit_mul {A : Type u} [NonUnitalCStarAlgebra A]
    (a : A) (h : IsUnit (ContinuousLinearMap.mul ℂ A a)) :
    ∃ e : A, ∀ b : A, e * b = b ∧ b * e = b := by
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp h
  obtain ⟨e, he⟩ := hb.2 a
  apply identity_of_left_identity e
  intro b
  apply hb.1
  change a * (e * b) = a * b
  rw [← mul_assoc]
  change (ContinuousLinearMap.mul ℂ A a e) * b = a * b
  rw [he]

/-- The scalar estimate is the nonunital step: an invertible left
multiplication operator would manufacture an identity in the original algebra. -/
theorem scalar_bound : Spec.ScalarBound.{u} := by
  intro A _ _ hA x
  by_contra! h
  have hzpos : 0 < ‖x.fst‖ := (norm_nonneg _).trans_lt h
  have hz : x.fst ≠ 0 := norm_pos_iff.mp hzpos
  have hsmall : ‖x.fst⁻¹ • leftAction A x‖ < 1 := by
    rw [norm_smul, norm_inv, inv_mul_lt_iff₀ hzpos, mul_one]
    exact h
  have hu := isUnit_one_sub_of_norm_lt_one hsmall
  have heq : 1 - x.fst⁻¹ • leftAction A x =
      ContinuousLinearMap.mul ℂ A (-(x.fst⁻¹) • x.snd) := by
    ext a
    rw [sub_apply, one_apply_eq_self, smul_apply]
    rw [show leftAction A x a = x.snd * a + x.fst • a from left_action_formula A x a]
    simp [smul_add, smul_smul, hz, sub_eq_add_neg, add_comm]
  rw [heq] at hu
  exact hA (identity_of_isUnit_mul _ hu)

private theorem action_eq (A : Type u) [NonUnitalCStarAlgebra A]
    (x : Unitization ℂ A) :
    leftAction A x = algebraMap ℂ (A →L[ℂ] A) x.fst + ContinuousLinearMap.mul ℂ A x.snd := rfl

theorem action_norm : Spec.ActionNorm.{u} := by
  intro A _ _ hA x
  rw [Unitization.norm_eq_sup, ← action_eq]
  exact max_eq_right (scalar_bound A hA x)

theorem faithful_action : Spec.FaithfulAction.{u} := by
  intro A _ _ hA
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply norm_eq_zero.mp
  rw [action_norm A hA x, hx, norm_zero]

theorem sum_norm_comparison : Spec.SumNormComparison.{u} := by
  intro A _ _ hA x
  have hz := scalar_bound A hA x
  have ha : ‖x.snd‖ ≤ ‖leftAction A x‖ + ‖x.fst‖ := by
    rw [← ContinuousLinearMap.opNorm_mul_apply ℂ A x.snd]
    have heq : ContinuousLinearMap.mul ℂ A x.snd =
        leftAction A x - algebraMap ℂ (A →L[ℂ] A) x.fst := by
      rw [action_eq]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_algebraMap'])
  constructor
  · rw [action_eq]
    exact (norm_add_le _ _).trans_eq (by
      rw [norm_algebraMap', ContinuousLinearMap.opNorm_mul_apply]; exact add_comm _ _)
  · linarith

theorem cstar_structure : Spec.CStarStructure.{u} := by
  intro A _
  exact ⟨inferInstance, fun x => by
    simpa only [pow_two] using CStarRing.norm_star_mul_self (x := x)⟩

theorem closed_ideal_embedding : Spec.ClosedIdealEmbedding.{u} := by
  intro A _
  have hi : Isometry (Unitization.inrNonUnitalStarAlgHom ℂ A) := Unitization.isometry_inr
  refine ⟨hi, hi.isClosedEmbedding.isClosed_range, ?_⟩
  intro x a
  constructor
  · refine ⟨x.fst • a + x.snd * a, ?_⟩
    apply Unitization.ext <;> simp [Unitization.snd_mul]
  · refine ⟨x.fst • a + a * x.snd, ?_⟩
    apply Unitization.ext <;> simp [Unitization.snd_mul]

theorem zero_alternative : Spec.ZeroAlternative.{u} :=
  ExpandedFA.CStar.Conventions.zero_unitization_alternative

theorem unital_alternative : Spec.UnitalAlternative.{u} :=
  ExpandedFA.CStar.Conventions.unital_unitization_alternative

end ExpandedFA.CStar.Unitization
