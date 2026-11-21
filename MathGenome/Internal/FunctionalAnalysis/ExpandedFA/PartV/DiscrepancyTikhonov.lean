import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.DiscrepancyTikhonov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.TikhonovMinimizer
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Filter Set
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.DiscrepancyTikhonov
universe u v w
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]
local notation "R" => TikhonovMinimizer.Spec.regularizer
local notation "N" => TikhonovMinimizer.Spec.normalOperator

/-- Comparison with every fixed competitor, with no range hypothesis. -/
theorem objective_le (A : H →L[𝕜] G) (f : G) {α : ℝ} (hα : 0 < α) (x : H) :
    ‖A (R A α f) - f‖ ^ 2 + α * ‖R A α f‖ ^ 2 ≤
      ‖A x - f‖ ^ 2 + α * ‖x‖ ^ 2 :=
  (TikhonovMinimizer.unique_minimizer 𝕜 H G A α hα f).1 x

/-- Increasing the penalty decreases the reconstruction norm and increases
its residual. This follows by adding the two minimizing inequalities. -/
theorem residual_monotone (A : H →L[𝕜] G) (f : G) : Spec.ResidualMonotonicity A f := by
  intro α hα β hβ hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_rfl
  have ha := objective_le A f hα (R A β f)
  have hb := objective_le A f hβ (R A α f)
  have hn : ‖R A β f‖ ^ 2 ≤ ‖R A α f‖ ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hn hα.le
  have hr : ‖A (R A α f) - f‖ ^ 2 ≤ ‖A (R A β f) - f‖ ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

/-- A pointwise inverse is continuous at each positive normal operator. -/
theorem regularizer_continuousAt (A : H →L[𝕜] G) {α : ℝ} (hα : 0 < α) :
    ContinuousAt (fun β : ℝ => R A β) α := by
  obtain ⟨e, he⟩ := TikhonovMinimizer.normal_invertible 𝕜 H G A α hα
  have hn : Continuous (fun β : ℝ => N A β) := by
    unfold TikhonovMinimizer.Spec.normalOperator
    fun_prop
  have hi : ContinuousAt Ring.inverse (N A α) := by
    rw [← he]
    exact NormedRing.inverse_continuousAt e.toUnit
  have ht := hi.comp hn.continuousAt
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at ht
  exact ht.clm_comp continuousAt_const

theorem residual_continuous (A : H →L[𝕜] G) (f : G) : Spec.ResidualContinuity A f := by
  intro α hα
  exact (((A.continuous.continuousAt.comp
    ((regularizer_continuousAt A hα).clm_apply continuousAt_const)).sub
      continuousAt_const).norm).continuousWithinAt

omit [CompleteSpace H] [CompleteSpace G] in
/-- The range-distance is a lower bound for every residual. -/
theorem distance_le_residual (A : H →L[𝕜] G) (f : G) (x : H) :
    Metric.infDist f (closure (A.range : Set G)) ≤ ‖A x - f‖ := by
  rw [Metric.infDist_closure]
  simpa only [dist_eq_norm, norm_sub_rev] using
    (Metric.infDist_le_dist_of_mem (x := f) (show A x ∈ (A.range : Set G) from ⟨x, rfl⟩))

/-- Fixed-competitor comparison proves the lower endpoint limit even if the
range is not closed and the nearest range point is not attained. -/
theorem residual_limit_zero (A : H →L[𝕜] G) (f : G) : Spec.ResidualLimitZero A f := by
  unfold Spec.ResidualLimitZero
  rw [Metric.infDist_closure]
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun α => hb.trans_le (by
      simpa only [Metric.infDist_closure] using distance_le_residual A f (R A α f))
  · intro b hb
    have hbpos : 0 < b := Metric.infDist_nonneg.trans_lt hb
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
      (Metric.infDist_lt_iff (show (A.range : Set G).Nonempty from ⟨A 0, 0, rfl⟩)).mp hb
    rw [dist_eq_norm, norm_sub_rev] at hx
    have hsq : ‖A x - f‖ ^ 2 < b ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hbpos.le).mpr hx
    have hc : Continuous (fun α : ℝ => ‖A x - f‖ ^ 2 + α * ‖x‖ ^ 2) := by fun_prop
    have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [zero_mul, add_zero] at ht
    filter_upwards [self_mem_nhdsWithin, ht.eventually (Iio_mem_nhds hsq)] with α hα hs
    have hmin := objective_le A f hα x
    have hp := mul_nonneg hα.le (sq_nonneg ‖R A α f‖)
    apply (sq_lt_sq₀ (norm_nonneg _) hbpos.le).mp
    exact lt_of_le_of_lt (by linarith) hs

/-- Coercivity tested on the solution gives decay at infinity. -/
theorem norm_regularized_le (A : H →L[𝕜] G) (f : G) {α : ℝ} (hα : 0 < α) :
    ‖R A α f‖ ≤ ‖A.adjoint f‖ / α := by
  have he := TikhonovMinimizer.normal_coercive A α (R A α f)
  rw [TikhonovMinimizer.normal_equation 𝕜 H G A α hα f] at he
  have hc := re_inner_le_norm (𝕜 := 𝕜) (R A α f) (A.adjoint f)
  apply (le_div_iff₀ hα).mpr
  by_cases hz : ‖R A α f‖ = 0
  · simp only [hz, zero_mul]
    exact norm_nonneg _
  · have hp : 0 < ‖R A α f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [he.trans hc]

theorem residual_limit_infinity (A : H →L[𝕜] G) (f : G) : Spec.ResidualLimitInfinity A f := by
  have hx : Tendsto (fun α : ℝ => R A α f) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      ((eventually_gt_atTop (0 : ℝ)).mono fun α hα => norm_regularized_le A f hα)
    exact tendsto_const_nhds.div_atTop tendsto_id
  have ht := ((A.continuous.tendsto 0).comp hx).sub_const f
  simpa only [Spec.ResidualLimitInfinity, map_zero, zero_sub, norm_neg, Function.comp_apply] using ht.norm

theorem kernel_component (A : H →L[𝕜] G) (f : G) : Spec.KernelComponent A f := by
  intro α _hα y hy
  rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left]
  simp only [(show A.adjoint y = 0 from hy), inner_zero_left, zero_sub]

/-- The minimizing inequality cancels the equal residuals. Equality in the
norm bound forces equality in the strictly convex Tikhonov objective. -/
theorem minimum_norm_at_residual (A : H →L[𝕜] G) (f : G) :
    Spec.MinimumNormAtResidual A f := by
  intro α hα
  have hmin : ∀ z : H, ‖A z - f‖ ≤ ‖A (R A α f) - f‖ → ‖R A α f‖ ≤ ‖z‖ := by
    intro z hz
    have he := objective_le A f hα z
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hz
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith
  intro x
  constructor
  · rintro ⟨hx, hn⟩
    apply (TikhonovMinimizer.unique_minimizer 𝕜 H G A α hα f).2 x
    intro z
    have he := objective_le A f hα z
    have hnorm := hn (R A α f) le_rfl
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
    have hs' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
    change ‖A x - f‖ ^ 2 + α * ‖x‖ ^ 2 ≤ _
    exact (add_le_add hs (mul_le_mul_of_nonneg_left hs' hα.le)).trans he
  · rintro rfl
    exact ⟨le_rfl, hmin⟩

theorem discrepancy_solution (A : H →L[𝕜] G) (f : G) : Spec.DiscrepancySolution A f := by
  intro δ hlo hhi
  have hzero : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioi 0) := inf_le_right
  have hinf : (atTop : Filter ℝ) ≤ 𝓟 (Ioi 0) :=
    le_principal_iff.mpr (eventually_gt_atTop 0)
  obtain ⟨α, hα, he⟩ := isPreconnected_Ioi.intermediate_value_Ioo hzero hinf
    (residual_continuous A f) (residual_limit_zero A f) (residual_limit_infinity A f) ⟨hlo, hhi⟩
  refine ⟨α, hα, he, ?_⟩
  simpa only [he] using minimum_norm_at_residual A f α hα

end ExpandedFA.PartV.DiscrepancyTikhonov
