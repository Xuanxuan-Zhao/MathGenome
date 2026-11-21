import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.HolomorphicLimits

open private circle_derivative_formula from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives

theorem holomorphic_limit :
    Specs.D12Complex.Ch11.HolomorphicLimits.holomorphic_limit_type := by
  intro Ω F f hΩ hF hlim
  have hd : DifferentiableOn ℂ f Ω := hlim.differentiableOn
    (Eventually.of_forall fun n z hz => (hF n).2 z hz |>.differentiableWithinAt) hΩ
  exact ⟨hΩ, fun z hz => hd.differentiableAt (hΩ.mem_nhds hz)⟩

theorem iteratedDeriv_locallyUniform_limit :
    Specs.D12Complex.Ch11.HolomorphicLimits.iteratedDeriv_locallyUniform_limit_type := by
  intro Ω F f hΩ hF hlim k
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hlim
  | succ k ih =>
    have hd : ∀ᶠ n in atTop, DifferentiableOn ℂ (iteratedDeriv k (F n)) Ω :=
      Eventually.of_forall fun n z hz =>
        ((DiskCauchyDerivatives.holomorphicOn_iteratedDeriv Ω (F n) (hF n) k).1.2
          z hz).differentiableWithinAt
    simpa only [Function.comp_def, iteratedDeriv_succ] using ih.deriv hd hΩ

/-- Cauchy's formula on the original outer circle bounds every point of the
inner closed disk, with a single constant independent of that point. -/
theorem norm_iteratedDeriv_le_of_boundary_bound (Ω : Set ℂ) (h : ℂ → ℂ)
    (hh : HolomorphicOn Ω h) (a : ℂ) (r R M : ℝ) (hr : 0 ≤ r)
    (hrR : r < R) (hΩ : closedBall a R ⊆ Ω) (hM : 0 ≤ M)
    (hbound : ∀ w ∈ sphere a R, ‖h w‖ ≤ M) (k : ℕ)
    (z : ℂ) (hz : z ∈ closedBall a r) :
    ‖iteratedDeriv k h z‖ ≤ ((k.factorial : ℝ) * R / (R-r)^(k+1)) * M := by
  have hR : 0 < R := hr.trans_lt hrR
  have hgap : 0 < R-r := sub_pos.mpr hrR
  have hzr : ‖z-a‖ ≤ r := mem_closedBall_iff_norm.mp hz
  have hzi : ‖z-a‖ < R := hzr.trans_lt hrR
  have hint : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ *
      circleIntegral (fun w => h w / (w-z)^(k+1)) a R‖ ≤
      R * (M / (R-r)^(k+1)) := by
    apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    intro w hw
    have hden : R-r ≤ ‖w-z‖ := by
      have htri : ‖w-a‖ ≤ ‖w-z‖ + ‖z-a‖ := by
        simpa only [dist_eq_norm] using dist_triangle w z a
      have hwR : ‖w-a‖ = R := mem_sphere_iff_norm.mp hw
      linarith
    rw [norm_div, norm_pow]
    exact div_le_div₀ hM (hbound w hw) (pow_pos hgap _)
      (pow_le_pow_left₀ hgap.le hden _)
  have heq : iteratedDeriv k h z = (k.factorial : ℂ) *
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        circleIntegral (fun w => h w / (w-z)^(k+1)) a R) := by
    rw [circle_derivative_formula a R Ω h hR hh hΩ k z hzi]
    ring
  rw [heq, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (k.factorial : ℝ) * (R * (M / (R-r)^(k+1))) :=
      mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The estimate actually holds for any two holomorphic functions, independent
of a convergence hypothesis. -/
theorem disk_derivative_difference_estimate (Ω : Set ℂ) (f g : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g)
    (a : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (hΩ : closedBall a R ⊆ Ω) (k : ℕ) :
    sSup ((fun z => ‖iteratedDeriv k f z - iteratedDeriv k g z‖) '' closedBall a r) ≤
      ((k.factorial : ℝ) * R / (R-r)^(k+1)) *
        sSup ((fun w => ‖f w - g w‖) '' sphere a R) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hh : HolomorphicOn Ω (f-g) := ⟨hf.1, fun z hz => (hf.2 z hz).sub (hg.2 z hz)⟩
  have hc : ContinuousOn (fun w => ‖f w - g w‖) (sphere a R) :=
    fun w hw => ((hh.2 w (hΩ (sphere_subset_closedBall hw))).continuousAt.norm).continuousWithinAt
  have hbdd := (isCompact_sphere a R).bddAbove_image hc
  have hbound : ∀ w ∈ sphere a R,
      ‖(f-g) w‖ ≤ sSup ((fun w => ‖f w - g w‖) '' sphere a R) := by
    intro w hw
    exact le_csSup hbdd (mem_image_of_mem _ hw)
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := a) (r := R)).mpr hR.le
  have hM := (norm_nonneg ((f-g) w)).trans (hbound w hw)
  have hnonempty : ((fun z => ‖iteratedDeriv k f z - iteratedDeriv k g z‖) ''
      closedBall a r).Nonempty := ⟨_, mem_image_of_mem _ (mem_closedBall_self hr)⟩
  apply csSup_le hnonempty
  rintro _ ⟨z, hz, rfl⟩
  have hzΩ : z ∈ Ω := hΩ (closedBall_subset_closedBall hrR.le hz)
  have hdf : ContDiffAt ℂ k f z :=
    (DifferentiableOn.contDiffOn (fun z hz => (hf.2 z hz).differentiableWithinAt)
      hf.1).contDiffAt (hf.1.mem_nhds hzΩ)
  have hdg : ContDiffAt ℂ k g z :=
    (DifferentiableOn.contDiffOn (fun z hz => (hg.2 z hz).differentiableWithinAt)
      hg.1).contDiffAt (hg.1.mem_nhds hzΩ)
  simpa only [iteratedDeriv_sub hdf hdg] using
    norm_iteratedDeriv_le_of_boundary_bound Ω (f-g) hh a r R _ hr hrR hΩ hM hbound k z hz

theorem holomorphic_limits_disk_estimate :
    Specs.D12Complex.Ch11.HolomorphicLimits.holomorphic_limits_disk_estimate_type := by
  intro Ω F f hΩ hF hlim a r R hr hrR hsub n k
  exact disk_derivative_difference_estimate Ω (F n) f (hF n)
    (holomorphic_limit Ω F f hΩ hF hlim) a r R hr hrR hsub k

end D12Complex.HolomorphicLimits
