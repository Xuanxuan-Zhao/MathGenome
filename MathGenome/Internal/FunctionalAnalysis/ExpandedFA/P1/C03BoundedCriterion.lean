import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03BoundedCriterion
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! The boundedness criterion for algebraic linear maps, with neither space
assumed complete. See Theorem `fa2:p1:c03:bounded-criterion` in the manuscript. -/

namespace ExpandedFA.P1.C03BoundedCriterion

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A bound on the closed unit ball gives a global norm bound by normalization.
The zero vector is treated separately, so the zero domain is included. -/
theorem norm_bound_of_bounded_unit_ball (T : E →ₗ[𝕜] F)
    (h : Bornology.IsBounded (T '' Metric.closedBall (0 : E) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos_norm_le
  refine ⟨C, hC.le, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : (‖x‖⁻¹ : 𝕜) • x ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_smul_inv_norm hx).le
  have hb := hbound _ (Set.mem_image_of_mem T hu)
  rw [map_smul, norm_smul, norm_inv, RCLike.norm_coe_norm] at hb
  calc
    ‖T x‖ = (‖x‖⁻¹ * ‖T x‖) * ‖x‖ := by field_simp
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg x)

/-- The nonnegative uniform bound is equivalent to norm continuity. -/
theorem continuous_iff_norm_bound (T : E →ₗ[𝕜] F) :
    Continuous T ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  constructor
  · intro h
    obtain ⟨C, hC, hb⟩ := SemilinearMapClass.bound_of_continuous T h
    exact ⟨C, hC.le, hb⟩
  · rintro ⟨C, _, hb⟩
    exact (T.mkContinuous C hb).continuous

/-- All five conditions of the manuscript's boundedness criterion. -/
theorem boundedness_criterion : Spec.BoundednessCriterion := by
  intro 𝕜 E F _ _ _ _ _ T
  have hzero : Continuous T ↔ ContinuousAt T (0 : E) :=
    ⟨fun h => h.continuousAt, fun h => continuous_of_continuousAt_zero T h⟩
  have hsets : Continuous T ↔ ∀ s : Set E, Bornology.IsBounded s →
      Bornology.IsBounded (T '' s) := by
    constructor
    · intro h s hs
      exact hs.image (show E →L[𝕜] F from ⟨T, h⟩)
    · intro h
      obtain ⟨C, _, hb⟩ := norm_bound_of_bounded_unit_ball T
        (h _ (Metric.isBounded_closedBall))
      exact (T.mkContinuous C hb).continuous
  refine ⟨hzero, continuous_iff_norm_bound T, ?_, hsets⟩
  constructor
  · intro h
    exact hsets.mp h _ Metric.isBounded_closedBall
  · intro h
    exact (continuous_iff_norm_bound T).mpr (norm_bound_of_bounded_unit_ball T h)

end ExpandedFA.P1.C03BoundedCriterion
