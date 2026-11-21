import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08BoundedInverse
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08OpenMapping

/-!
The bounded inverse is constructed from the algebraic inverse and the accepted
controlled-preimage theorem. Injectivity identifies each controlled preimage
with that inverse. For the sharp constant, scaling into the strict target ball
bounds the inverse at every t > ‖y‖/c; letting t decrease to ‖y‖/c gives the
non-strict estimate. This step does not require a nonzero vector or space.
-/

namespace ExpandedFA.P1.C08BoundedInverse

/-- A left inverse inherits the sharp norm bound from an open-ball image
inclusion. Completeness is unnecessary once the inverse is bounded. -/
theorem inverse_norm_le_of_ball_image
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (S : F →L[𝕜] E) (hST : ∀ x, S (T x) = x)
    {c : ℝ} (hc : 0 < c)
    (hball : Metric.ball (0 : F) c ⊆ T '' Metric.ball (0 : E) 1) :
    ‖S‖ ≤ 1 / c := by
  apply S.opNorm_le_bound (div_nonneg zero_le_one hc.le)
  intro y
  have hy : ‖S y‖ ≤ ‖y‖ / c := by
    apply le_of_forall_gt
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt (div_nonneg (norm_nonneg y) hc.le) ht
    have hscaled : (t : 𝕜)⁻¹ • y ∈ Metric.ball (0 : F) c := by
      rw [mem_ball_zero_iff, norm_smul, norm_inv,
        RCLike.norm_ofReal, abs_of_pos htpos]
      rw [inv_mul_eq_div, div_lt_iff₀ htpos]
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp ht
    obtain ⟨x, hx, hTx⟩ := hball hscaled
    have hS : (t : 𝕜)⁻¹ • S y = x := by
      rw [← S.map_smul, ← hTx, hST]
    have hnorm : t⁻¹ * ‖S y‖ < 1 := by
      have hxnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      rw [← hS, norm_smul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos htpos] at hxnorm
      exact hxnorm
    have hlt : ‖S y‖ < t := by
      simpa only [one_mul] using (div_lt_iff₀ htpos).mp
        (show ‖S y‖ / t < 1 by simpa only [inv_mul_eq_div] using hnorm)
    exact hlt
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hy

/-- Corollary `fa2:p1:c08:bounded-inverse`, including its quantitative conclusion. -/
theorem bounded_inverse : Spec.BoundedInverse := by
  intro 𝕜 E F _ _ _ _ _ _ _ T hT
  let e : E ≃ₗ[𝕜] F := LinearEquiv.ofBijective T.toLinearMap hT
  obtain ⟨C, _, hC⟩ := ExpandedFA.P1.C08OpenMapping.open_mapping_controlled_preimages 𝕜 E F T hT.2
  have hbound : ∀ y : F, ‖e.symm y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨x, hx, hnorm⟩ := hC y
    have hex : e x = y := hx
    rw [← hex, e.symm_apply_apply]
    simpa only [hex] using hnorm
  let S : F →L[𝕜] E := e.symm.toLinearMap.mkContinuous C hbound
  have hST : ∀ x : E, S (T x) = x := fun x => e.symm_apply_apply x
  have hTS : ∀ y : F, T (S y) = y := fun y => e.apply_symm_apply y
  refine ⟨S, hST, hTS, ?_⟩
  intro c hc hball
  exact inverse_norm_le_of_ball_image T S hST hc hball

end ExpandedFA.P1.C08BoundedInverse
