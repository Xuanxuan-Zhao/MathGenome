import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Metric

namespace D12Complex.DiskCauchyFormula

abbrev circlePath : Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_type :=
  Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value

theorem circlePath_apply :
    Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_apply_type := by
  intro a r t
  rfl

theorem circlePath_trace :
    Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_trace_type := by
  intro a r hr
  change circleMap a r '' Icc 0 (2 * Real.pi) = sphere a r
  apply Subset.antisymm
  · rintro w ⟨t, _, rfl⟩
    exact circleMap_mem_sphere a hr t
  · intro w hw
    have hw' : w ∈ sphere a |r| := by simpa only [abs_of_nonneg hr] using hw
    rw [← image_circleMap_Ioc] at hw'
    exact image_mono (f := circleMap a r) Ioc_subset_Icc_self hw'

theorem circlePath_closed :
    Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_closed_type := by
  intro a r
  change circleMap a r (2 * Real.pi) = circleMap a r 0
  simpa using (periodic_circleMap a r) 0

theorem integral_eq_circleIntegral :
    Specs.D12Complex.Ch04.DiskCauchyFormula.integral_eq_circleIntegral_type := by
  intro a r g hr hg
  have hg' : ContinuousOn g (circlePath a r).trace := by
    rw [circlePath_trace a r hr]
    exact hg
  rw [PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral _ _ g hg']
  change (∫ t in (0 : ℝ)..2 * Real.pi, g (circleMap a r t) * deriv (circleMap a r) t) = _
  unfold circleIntegral
  simp only [smul_eq_mul, mul_comm]

theorem circle_integral_sub_inv :
    Specs.D12Complex.Ch04.DiskCauchyFormula.circle_integral_sub_inv_type := by
  intro a z r hr hz
  have hz' : z ∈ ball a r := mem_ball_iff_norm.mpr hz
  have hc : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere a r) := by
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro w hw
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hw (ne_of_lt hz'))
  rw [integral_eq_circleIntegral a r _ hr.le hc]
  exact circleIntegral.integral_sub_inv_of_mem_ball hz'

theorem cauchy_formula_of_continuous_differentiable :
    Specs.D12Complex.Ch04.DiskCauchyFormula.cauchy_formula_of_continuous_differentiable_type := by
  intro a z r f hr hz hc hd
  have hz' : z ∈ ball a r := mem_ball_iff_norm.mpr hz
  have hden : ∀ w ∈ sphere a r, w - z ≠ 0 := by
    intro w hw
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hw (ne_of_lt hz'))
  have hg : ContinuousOn (fun w => f w / (w - z)) (sphere a r) :=
    (hc.mono sphere_subset_closedBall).div
      (continuousOn_id.sub continuousOn_const) hden
  rw [integral_eq_circleIntegral a r _ hr.le hg]
  have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) countable_empty hz' hc (fun w hw => hd w hw.1)
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h.symm

theorem disk_cauchy_formula :
    Specs.D12Complex.Ch04.DiskCauchyFormula.disk_cauchy_formula_type := by
  intro a z r U f hr hf hU hz
  apply cauchy_formula_of_continuous_differentiable a z r f hr hz
  · intro w hw
    exact (hf.2 w (hU hw)).continuousAt.continuousWithinAt
  · intro w hw
    exact hf.2 w (hU (ball_subset_closedBall hw))

end D12Complex.DiskCauchyFormula
