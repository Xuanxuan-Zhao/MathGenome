import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.DiskCauchyDerivatives

theorem holomorphicOn_iteratedDeriv :
    Specs.D12Complex.Ch04.DiskCauchyDerivatives.holomorphicOn_iteratedDeriv_type := by
  intro U f hf
  have hh : ∀ n : ℕ, HolomorphicOn U (iteratedDeriv n f) := by
    intro n
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hf
    | succ n ih =>
      rw [iteratedDeriv_succ]
      have hd : DifferentiableOn ℂ (iteratedDeriv n f) U :=
        fun w hw => (ih.2 w hw).differentiableWithinAt
      exact ⟨hf.1, fun z hz => (hd.deriv hf.1).differentiableAt (hf.1.mem_nhds hz)⟩
  intro n
  refine ⟨hh n, ?_⟩
  intro z hz
  rw [iteratedDeriv_succ]
  exact ((hh n).2 z hz).hasDerivAt

theorem continuousOn_iteratedDeriv :
    Specs.D12Complex.Ch04.DiskCauchyDerivatives.continuousOn_iteratedDeriv_type := by
  intro U f hf n z hz
  exact ((holomorphicOn_iteratedDeriv U f hf n).1.2 z hz).continuousAt.continuousWithinAt

/-- Parameter differentiation uses Mathlib's dominated local differentiation
lemma. Its proof constructs a uniform positive lower bound for |w-z| on
an entire neighborhood of z, and an integrable bound for the kernel derivative. -/
private theorem hasDerivAt_kernel_integral (a z : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hr : 0 < r) (hz : ‖z - a‖ < r) (hc : ContinuousOn f (sphere a r)) (n : ℕ) :
    HasDerivAt (fun z => circleIntegral (fun w => f w / (w-z)^(n+1)) a r)
      ((n+1 : ℂ) * circleIntegral (fun w => f w / (w-z)^(n+2)) a r) z := by
  have hnot : z ∉ sphere a |r| := by
    rw [abs_of_pos hr]
    exact ne_of_lt (mem_ball_iff_norm.mpr hz)
  have hci : CircleIntegrable f a r := hc.circleIntegrable hr.le
  have h := Complex.hasDerivAt_circleIntegral_sub_zpow_smul
    (n := -((n+1 : ℕ) : ℤ)) hci hnot
  have he : -((n+1 : ℕ) : ℤ) - 1 = -((n+2 : ℕ) : ℤ) := by omega
  rw [he] at h
  simp only [zpow_neg, zpow_natCast] at h
  convert h using 1 <;> simp [smul_eq_mul, div_eq_mul_inv, mul_comm]


private theorem continuousOn_kernel (a z : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hz : ‖z - a‖ < r) (hc : ContinuousOn f (sphere a r)) (n : ℕ) :
    ContinuousOn (fun w => f w / (w-z)^(n+1)) (sphere a r) := by
  refine hc.div ((continuousOn_id.sub continuousOn_const).pow _) ?_
  intro w hw
  exact pow_ne_zero _ (sub_ne_zero.mpr
    (ne_of_mem_of_not_mem hw (ne_of_lt (mem_ball_iff_norm.mpr hz))))

private theorem circle_derivative_formula (a : ℂ) (r : ℝ) (U : Set ℂ) (f : ℂ → ℂ)
    (hr : 0 < r) (hf : HolomorphicOn U f) (hU : closedBall a r ⊆ U) :
    ∀ (n : ℕ) (z : ℂ), ‖z - a‖ < r →
      iteratedDeriv n f z = (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
        circleIntegral (fun w => f w / (w-z)^(n+1)) a r := by
  have hc : ContinuousOn f (sphere a r) := fun w hw =>
    (hf.2 w (hU (sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
  intro n
  induction n with
  | zero =>
    intro z hz
    have h := DiskCauchyFormula.disk_cauchy_formula a z r U f hr hf hU hz
    rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le
      (by simpa using continuousOn_kernel a z r f hz hc 0)] at h
    simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_div,
      zero_add, pow_one] using h
  | succ n ih =>
    intro z hz
    have heq : iteratedDeriv n f =ᶠ[𝓝 z]
        (fun z => (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
          circleIntegral (fun w => f w / (w-z)^(n+1)) a r) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_iff_norm.mpr hz))
        (fun w hw => ih w (mem_ball_iff_norm.mp hw))
    have hd := ((hasDerivAt_kernel_integral a z r f hr hz hc n).const_mul
      ((n.factorial : ℂ) / (2 * Real.pi * Complex.I))).congr_of_eventuallyEq heq
    rw [iteratedDeriv_succ]
    rw [hd.deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem disk_cauchy_derivatives :
    Specs.D12Complex.Ch04.DiskCauchyDerivatives.disk_cauchy_derivatives_type := by
  intro a z r U f hr hf hU hz n
  have hc : ContinuousOn f (sphere a r) := fun w hw =>
    (hf.2 w (hU (sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
  rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le
    (continuousOn_kernel a z r f hz hc n)]
  exact circle_derivative_formula a r U f hr hf hU n z hz

theorem disk_cauchy_estimate :
    Specs.D12Complex.Ch04.DiskCauchyDerivatives.disk_cauchy_estimate_type := by
  intro a r U f M hr hf hU hM n
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ *
      circleIntegral (fun w => f w / (w-a)^(n+1)) a r‖ ≤ r * (M / r^(n+1)) := by
    apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
    intro w hw
    rw [norm_div, norm_pow, ← dist_eq_norm] 
    rw [mem_sphere.mp hw]
    exact div_le_div_of_nonneg_right (hM w hw) (pow_nonneg hr.le _)
  have heq : iteratedDeriv n f a = (n.factorial : ℂ) *
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        circleIntegral (fun w => f w / (w-a)^(n+1)) a r) := by
    rw [circle_derivative_formula a r U f hr hf hU n a (by simpa using hr)]
    ring
  rw [heq, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (n.factorial : ℝ) * (r * (M / r^(n+1))) :=
      mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)
    _ = (n.factorial : ℝ) * M / r^n := by
      rw [pow_succ]
      field_simp

theorem disk_cauchy_estimate_max :
    Specs.D12Complex.Ch04.DiskCauchyDerivatives.disk_cauchy_estimate_max_type := by
  intro a r U f hr hf hU
  have hc : ContinuousOn f (sphere a r) := fun w hw =>
    (hf.2 w (hU (sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
  obtain ⟨b, hb, hmax⟩ := (isCompact_sphere a r).exists_isMaxOn
    ⟨circleMap a r 0, circleMap_mem_sphere a hr.le 0⟩ hc.norm
  exact ⟨b, hb, hmax, disk_cauchy_estimate a r U f ‖f b‖ hr hf hU hmax⟩

end D12Complex.DiskCauchyDerivatives
