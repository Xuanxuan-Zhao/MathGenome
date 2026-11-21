import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03ResolventIdentity
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Ring.Commute

/-! Inverse difference and resolvent identities, with supplied bounded inverses.
All arguments are algebraic and apply to incomplete and zero spaces as well. -/

namespace ExpandedFA.P1.C03ResolventIdentity

theorem inverse_difference : Spec.InverseDifference := by
  intro 𝕜 E F _ _ _ _ _ A B Ai Bi hAiA _ _ hBBi
  symm
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_assoc, hBBi, hAiA,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

/-- `R(lam,T) = (lam id - T)⁻¹` on its domain of bounded invertibility. -/
noncomputable def operatorResolvent : Spec.ResolventType :=
  fun 𝕜 E _ _ _ T lam => Ring.inverse (lam • ContinuousLinearMap.id 𝕜 E - T)

theorem bounded_inverse_identification :
    Spec.BoundedInverseIdentification := by
  intro 𝕜 E _ _ _ A
  constructor
  · intro h
    exact ⟨Ring.inverse A, Ring.inverse_mul_cancel A h, Ring.mul_inverse_cancel A h⟩
  · rintro ⟨S, hSA, hAS⟩
    exact ⟨⟨A, S, hAS, hSA⟩, rfl⟩

theorem operator_resolvent_inverse : Spec.ResolventInverse := by
  intro 𝕜 E _ _ _ T lam h
  exact ⟨Ring.inverse_mul_cancel _ h, Ring.mul_inverse_cancel _ h⟩

theorem operator_resolvent_identity : Spec.ResolventIdentity := by
  intro 𝕜 E _ _ _ T lam mu hlam hmu
  obtain ⟨hlaml, hlamr⟩ := operator_resolvent_inverse 𝕜 E T lam hlam
  obtain ⟨hmul, hmur⟩ := operator_resolvent_inverse 𝕜 E T mu hmu
  rw [inverse_difference 𝕜 E E _ _ _ _ hlaml hlamr hmul hmur]
  have hd : (mu • ContinuousLinearMap.id 𝕜 E - T) -
      (lam • ContinuousLinearMap.id 𝕜 E - T) =
      (mu - lam) • ContinuousLinearMap.id 𝕜 E := by
    rw [sub_sub_sub_cancel_right, sub_smul]
  rw [hd, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.smul_comp]

theorem operator_resolvents_commute : Spec.ResolventCommute := by
  intro 𝕜 E _ _ _ T lam mu _ _
  have hcentral (r : 𝕜) (S : E →L[𝕜] E) : Commute (r • (1 : E →L[𝕜] E)) S := by
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commute_algebraMap_left r S
  have hc : Commute (lam • (1 : E →L[𝕜] E) - T) (mu • (1 : E →L[𝕜] E) - T) := by
    exact (hcentral lam _).sub_left ((hcentral mu T).symm.sub_right (Commute.refl T))
  exact hc.ringInverse_ringInverse.eq

end ExpandedFA.P1.C03ResolventIdentity
