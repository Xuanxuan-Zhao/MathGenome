import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GeometricBarriers
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.BarrierSqueeze
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicFoundation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Topology

namespace D12Complex.GeometricBarriers

abbrev LocalExteriorCone := D12Complex.LocalExteriorCone
abbrev ExteriorTangentDisk := D12Complex.ExteriorTangentDisk
abbrev diskLinearBarrier := D12Complex.diskLinearBarrier
abbrev wedgePowerBarrier := D12Complex.wedgePowerBarrier
abbrev tangentLogBarrier := D12Complex.tangentLogBarrier

lemma harmonic_superharmonic {U : Set ℂ} {b : ℂ → ℝ}
    (hb : HarmonicOn U b) : SuperharmonicOn U b := by
  apply SubharmonicOperations.harmonicOn_subharmonicOn
  exact (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U _ hb.1).mpr
    (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U b hb.1).mp hb).neg)

/-- Squared distance identity used to make the supporting barrier strict. -/
lemma disk_barrier_distance_identity (c ξ z : ℂ) (R : ℝ)
    (hR : 0 < R) (hξ : dist ξ c = R) :
    ‖z - ξ‖ ^ 2 = ‖z - c‖ ^ 2 - R ^ 2 +
      2 * R * diskLinearBarrier c ξ R z := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have he : ‖ξ - c‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hξ]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    sub_re, sub_im] at he ⊢
  simp only [diskLinearBarrier, D12Complex.diskLinearBarrier,
    Complex.div_ofReal, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, sub_re, sub_im]
  field_simp
  nlinarith

lemma disk_barrier_continuous (c ξ : ℂ) (R : ℝ) :
    Continuous (diskLinearBarrier c ξ R) := by
  unfold diskLinearBarrier D12Complex.diskLinearBarrier
  fun_prop

lemma disk_barrier_harmonic (c ξ : ℂ) (R : ℝ) (U : Set ℂ) (hU : IsOpen U) :
    HarmonicOn U (diskLinearBarrier c ξ R) := by
  let F : ℂ → ℂ := fun z => (R : ℂ) - starRingEnd ℂ ((ξ - c) / (R : ℂ)) * (z - c)
  have hf : HolomorphicOn U F := ⟨hU, fun z _ => by dsimp [F]; fun_prop⟩
  change HarmonicOn U (fun z => R - (starRingEnd ℂ ((ξ - c) / (R : ℂ)) * (z - c)).re)
  simpa only [F, Complex.sub_re, Complex.ofReal_re] using
    HarmonicFoundation.holomorphic_harmonic_re U F hf

theorem disk_linear_barrier :
    Specs.D12Complex.Ch14.GeometricBarriers.disk_linear_barrier_type := by
  intro c ξ R hR hξ r hr
  have hξR : dist ξ c = R := hξ
  have hzero : diskLinearBarrier c ξ R ξ = 0 := by
    have he := disk_barrier_distance_identity c ξ ξ R hR hξR
    rw [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
    rw [← dist_eq_norm, hξR] at he
    nlinarith
  refine ⟨hr, harmonic_superharmonic (disk_barrier_harmonic c ξ R _
    (isOpen_ball.inter isOpen_ball)), (disk_barrier_continuous c ξ R).continuousOn,
    hzero, ?_⟩
  intro z hz hne
  have hzR : dist z c ≤ R := closure_ball_subset_closedBall
    (closure_mono inter_subset_left hz)
  have hn : 0 < ‖z - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have he := disk_barrier_distance_identity c ξ z R hR hξR
  have hsq : dist z c ^ 2 ≤ R ^ 2 := sq_le_sq₀ dist_nonneg hR.le |>.mpr hzR
  simp only [dist_eq_norm] at hsq
  change 0 < diskLinearBarrier c ξ R z
  nlinarith [sq_pos_of_pos hn]

theorem disk_boundary_regular :
    Specs.D12Complex.Ch14.GeometricBarriers.disk_boundary_regular_type := by
  intro c ξ R hR hξ
  refine ⟨hξ, 1, diskLinearBarrier c ξ R, ?_⟩
  exact disk_linear_barrier c ξ R hR
    (by simpa [frontier_ball c hR.ne'] using hξ) 1 zero_lt_one

/-- A closed angular inequality gives the exact principal-argument bound. -/
lemma arg_bound_of_cone {w : ℂ} {β : ℝ} (hw : w ≠ 0)
    (hβ : 0 ≤ β)
    (h : Real.cos β * ‖w‖ ≤ w.re) : |w.arg| ≤ β := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hc : Real.cos β ≤ Real.cos |w.arg| := by
    rw [Real.cos_abs, Complex.cos_arg hw]
    exact (le_div_iff₀ hn).mpr h
  by_contra hh
  exact (not_lt_of_ge hc) (Real.cos_lt_cos_of_nonneg_of_le_pi hβ
    (Complex.abs_arg_le_pi w) (lt_of_not_ge hh))

lemma slitPlane_of_arg_bound {w : ℂ} {β : ℝ} (hw : w ≠ 0)
    (hβ : β < Real.pi) (harg : |w.arg| ≤ β) : w ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff_arg.mpr
  refine ⟨?_, hw⟩
  intro he
  rw [he, abs_of_pos Real.pi_pos] at harg
  exact (not_le_of_gt hβ) harg

/-- Strictly narrower angular data give a positive selected wedge power. -/
lemma wedge_power_pos {w : ℂ} {β ω : ℝ} (hw : w ≠ 0)
    (hω : 0 < ω) (hβω : 2 * β < ω)
    (harg : |w.arg| ≤ β) : 0 < (w ^ ((Real.pi / ω : ℝ) : ℂ)).re := by
  rw [Complex.cpow_ofReal_re]
  have ha : 0 < Real.pi / ω := div_pos Real.pi_pos hω
  have hm : β * (Real.pi / ω) < Real.pi / 2 := by
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ hω (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith [Real.pi_pos]
  have hb : |w.arg * (Real.pi / ω)| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_right harg ha.le).trans_lt hm
  exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _)
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hb))

/-- The omitted cone forces a closed angular bound on the cap closure. -/
lemma cap_cone_inequality {Ω : Set ℂ} {ξ q : ℂ} {β r : ℝ}
    (hc : ∀ z ∈ ball ξ r,
      (q * (z - ξ)).re < Real.cos β * ‖q * (z - ξ)‖ → z ∉ Ω) :
    ∀ z ∈ closure (Ω ∩ ball ξ r),
      Real.cos β * ‖q * (z - ξ)‖ ≤ (q * (z - ξ)).re := by
  have hclosed : IsClosed {z : ℂ |
      Real.cos β * ‖q * (z - ξ)‖ ≤ (q * (z - ξ)).re} := by
    apply isClosed_le <;> fun_prop
  apply closure_minimal _ hclosed
  intro z hz
  exact le_of_not_gt (fun hh => hc z hz.2 hh hz.1)

lemma wedge_barrier_on_cap {Ω : Set ℂ} {ξ q : ℂ} {β ω r : ℝ}
    (hΩ : IsOpen Ω) (hξ : ξ ∈ frontier Ω) (hq : ‖q‖ = 1)
    (hβ : 0 ≤ β) (hβπ : β < Real.pi) (hω : 0 < ω)
    (hβω : 2 * β < ω) (hr : 0 < r)
    (hc : ∀ z ∈ closure (Ω ∩ ball ξ r),
      Real.cos β * ‖q * (z - ξ)‖ ≤ (q * (z - ξ)).re) :
    PositiveLocalBarrier Ω ξ r (wedgePowerBarrier ξ q ω) := by
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  have hξnot : ξ ∉ Ω := by
    rw [hΩ.frontier_eq] at hξ
    exact hξ.2
  have harg (z : ℂ) (hz : z ∈ closure (Ω ∩ ball ξ r)) (hne : z ≠ ξ) :
      |(q * (z - ξ)).arg| ≤ β :=
    arg_bound_of_cone (mul_ne_zero hq0 (sub_ne_zero.mpr hne)) hβ (hc z hz)
  have hslit (z : ℂ) (hz : z ∈ closure (Ω ∩ ball ξ r)) (hne : z ≠ ξ) :
      q * (z - ξ) ∈ Complex.slitPlane :=
    slitPlane_of_arg_bound (mul_ne_zero hq0 (sub_ne_zero.mpr hne)) hβπ (harg z hz hne)
  have ha : 0 < Real.pi / ω := div_pos Real.pi_pos hω
  have ha0 : ((Real.pi / ω : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hh : HarmonicOn (Ω ∩ ball ξ r) (wedgePowerBarrier ξ q ω) := by
    apply HarmonicFoundation.holomorphic_harmonic_re
    refine ⟨hΩ.inter isOpen_ball, fun z hz => ?_⟩
    apply DifferentiableAt.cpow_const
    · fun_prop
    · exact hslit z (subset_closure hz) (fun he => hξnot (he ▸ hz.1))
  refine ⟨hr, harmonic_superharmonic hh, ?_, ?_, ?_⟩
  · intro z hz
    have ht : ContinuousAt (fun z : ℂ => (q * (z - ξ)) ^
        ((Real.pi / ω : ℝ) : ℂ)) z := by
      by_cases he : z = ξ
      · subst z
        have hh := Complex.continuousAt_cpow_zero_of_re_pos
          (by simpa using ha : 0 < (((Real.pi / ω : ℝ) : ℂ)).re)
        have hp : ContinuousAt (fun w : ℂ => w ^ ((Real.pi / ω : ℝ) : ℂ)) 0 :=
          hh.comp (f := fun w : ℂ => (w, ((Real.pi / ω : ℝ) : ℂ)))
            (continuousAt_id.prodMk continuousAt_const)
        have hp' : ContinuousAt (fun w : ℂ => w ^ ((Real.pi / ω : ℝ) : ℂ))
            (q * (ξ - ξ)) := by simpa only [sub_self, mul_zero] using hp
        exact hp'.comp (f := fun w : ℂ => q * (w - ξ)) (by fun_prop)
      · exact (continuousAt_cpow_const (b := ((Real.pi / ω : ℝ) : ℂ)) (hslit z hz he)).comp
          (f := fun w : ℂ => q * (w - ξ)) (by fun_prop)
    exact (Complex.continuous_re.continuousAt.comp ht).continuousWithinAt
  · change ((q * (ξ - ξ)) ^ ((Real.pi / ω : ℝ) : ℂ)).re = 0
    simp only [sub_self, mul_zero, Complex.zero_cpow ha0, Complex.zero_re]
  · intro z hz hne
    exact wedge_power_pos (mul_ne_zero hq0 (sub_ne_zero.mpr hne)) hω hβω
      (harg z hz hne)

theorem exterior_cone_barrier :
    Specs.D12Complex.Ch14.GeometricBarriers.exterior_cone_barrier_type := by
  intro Ω ξ hΩ hξ hcone
  obtain ⟨q, β, r, hq, hβ, hβπ, hr, hc⟩ := hcone
  let ω := β + Real.pi
  have hω : 0 < ω := by dsimp [ω]; linarith [Real.pi_pos]
  refine ⟨q, ω, r, hq, hω, by dsimp [ω]; linarith, ?_⟩
  exact wedge_barrier_on_cap hΩ hξ hq hβ.le hβπ hω
    (by dsimp [ω]; linarith) hr (cap_cone_inequality hc)

theorem wedge_power_selected_branch :
    Specs.D12Complex.Ch14.GeometricBarriers.wedge_power_selected_branch_type := by
  intro ξ q z ω hz
  change ((q * (z - ξ)) ^ ((Real.pi / ω : ℝ) : ℂ)).re = _
  rw [Complex.cpow_def_of_ne_zero (PrincipalLogarithm.principalSlitPlane_ne_zero _ hz)]
  change (Complex.exp (Complex.log (q * (z - ξ)) * ((Real.pi / ω : ℝ) : ℂ))).re =
    (E (((Real.pi / ω : ℝ) : ℂ) * PrincipalLog (q * (z - ξ)))).re
  rw [Exponential.E_eq_exp, PrincipalLogarithm.principalLog_eq_log _ hz, mul_comm]

theorem wedge_power_polar :
    Specs.D12Complex.Ch14.GeometricBarriers.wedge_power_polar_type := by
  intro ξ q z ω ρ t hω hωπ hρ ht htω hz
  have hang : t - ω / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith
  have harg : (q * (z - ξ)).arg = t - ω / 2 := by
    rw [hz]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I hρ hang
  have hn : ‖q * (z - ξ)‖ = ρ := by
    have hN : ‖(Real.cos (t - ω / 2) : ℂ) + (Real.sin (t - ω / 2) : ℂ) * I‖ = 1 := by
      simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
        Complex.norm_cos_add_sin_mul_I (t - ω / 2)
    rw [hz, norm_mul, Complex.norm_of_nonneg hρ.le, hN, mul_one]
  change ((q * (z - ξ)) ^ ((Real.pi / ω : ℝ) : ℂ)).re = _
  rw [Complex.cpow_ofReal_re, harg, hn]
  have halg : (t - ω / 2) * (Real.pi / ω) = Real.pi * t / ω - Real.pi / 2 := by
    field_simp
  rw [halg, Real.cos_sub_pi_div_two]

theorem exterior_cone_regular :
    Specs.D12Complex.Ch14.GeometricBarriers.exterior_cone_regular_type := by
  intro Ω ξ hΩ hξ hc
  obtain ⟨q, ω, r, _, _, _, hb⟩ := exterior_cone_barrier Ω ξ hΩ hξ hc
  exact ⟨hξ, r, wedgePowerBarrier ξ q ω, hb⟩

/-- A parallelogram identity for the strictly smaller internally tangent disk. -/
lemma midpoint_distance_identity (c ξ z : ℂ) :
    4 * ‖z - (c + ξ) / 2‖ ^ 2 =
      2 * ‖z - c‖ ^ 2 + 2 * ‖z - ξ‖ ^ 2 - ‖ξ - c‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    sub_re, sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, add_re, add_im]
  ring

lemma tangent_disk_closure_distance {Ω : Set ℂ} {c : ℂ} {R : ℝ}
    (hd : Disjoint Ω (ball c R)) : ∀ z ∈ closure Ω, R ≤ dist z c := by
  have hc : IsClosed {z : ℂ | R ≤ dist z c} := isClosed_le continuous_const
    (continuous_id.dist continuous_const)
  apply closure_minimal _ hc
  intro z hz
  exact le_of_not_gt (fun (hh : dist z c < R) => Set.disjoint_left.mp hd hz hh)

/-- The small closed disk meets the exterior of the original open disk only at `ξ`. -/
lemma strict_midpoint_distance {c ξ z : ℂ} {R : ℝ} (hR : 0 < R)
    (hξ : dist ξ c = R) (hz : R ≤ dist z c) (hne : z ≠ ξ) :
    R / 2 < dist z ((c + ξ) / 2) := by
  have he := midpoint_distance_identity c ξ z
  have hn : 0 < ‖z - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsq : R ^ 2 ≤ dist z c ^ 2 :=
    (sq_le_sq₀ hR.le dist_nonneg).mpr hz
  simp only [dist_eq_norm] at hξ hz hsq ⊢
  rw [hξ] at he
  nlinarith [sq_pos_of_pos hn, norm_nonneg (z - (c + ξ) / 2)]

lemma vertex_midpoint_distance {c ξ : ℂ} {R : ℝ} (hξ : dist ξ c = R) :
    dist ξ ((c + ξ) / 2) = R / 2 := by
  have he : ξ - (c + ξ) / 2 = (ξ - c) / 2 := by ring
  rw [dist_eq_norm, he, norm_div]
  norm_num
  simpa only [dist_eq_norm] using hξ

/-- Harmonicity of logarithmic distance uses local logarithms and needs only
that the center is absent, not that a global logarithm exists. -/
lemma log_distance_harmonic (U : Set ℂ) (m : ℂ) (s : ℝ)
    (hU : IsOpen U) (hs : 0 < s) (hm : ∀ z ∈ U, z ≠ m) :
    HarmonicOn U (fun z => Real.log (dist z m / s)) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U _ hU).mpr
  intro z hz
  have ha : AnalyticAt ℂ (fun w : ℂ => w - m) z := by fun_prop
  have hh := (ha.harmonicAt_log_norm (sub_ne_zero.mpr (hm z hz))).sub
    (harmonicAt_const (Real.log s))
  apply (harmonicAt_congr_nhds (f₁ := fun w : ℂ => Real.log (dist w m / s))
    (f₂ := fun w : ℂ => Real.log ‖w - m‖ - Real.log s) _).mpr hh
  filter_upwards [(isOpen_ne.preimage (continuous_id.sub continuous_const)).mem_nhds
    (show z - m ≠ 0 from sub_ne_zero.mpr (hm z hz))] with w hw
  have hwm : w - m ≠ 0 := hw
  simpa only [dist_eq_norm] using Real.log_div (norm_ne_zero_iff.mpr hwm) hs.ne'

theorem exterior_tangent_disk_barrier :
    Specs.D12Complex.Ch14.GeometricBarriers.exterior_tangent_disk_barrier_type := by
  intro Ω ξ c R hΩ hξ hD
  obtain ⟨hR, hξR, hdis⟩ := hD
  let m := (c + ξ) / 2
  have hs : 0 < R / 2 := half_pos hR
  have hdist (z : ℂ) (hz : z ∈ closure Ω) : R / 2 ≤ dist z m := by
    by_cases he : z = ξ
    · simp [he, m, vertex_midpoint_distance hξR]
    · exact (strict_midpoint_distance hR hξR (tangent_disk_closure_distance hdis z hz) he).le
  have hne (z : ℂ) (hz : z ∈ closure Ω) : z ≠ m := by
    intro he
    have hh := hdist z hz
    rw [he, dist_self] at hh
    linarith
  refine ⟨1, zero_lt_one, ?_, ?_, ?_, ?_⟩
  · apply harmonic_superharmonic
    exact log_distance_harmonic _ m (R / 2) (hΩ.inter isOpen_ball) hs
      (fun z hz => hne z (subset_closure hz.1))
  · intro z hz
    have hzΩ : z ∈ closure Ω := closure_mono inter_subset_left hz
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log
    · fun_prop
    · exact div_ne_zero (dist_ne_zero.mpr (hne z hzΩ)) hs.ne'
  · change Real.log (dist ξ m / (R / 2)) = 0
    rw [show dist ξ m = R / 2 from vertex_midpoint_distance hξR, div_self hs.ne', Real.log_one]
  · intro z hz hneξ
    apply Real.log_pos
    apply (one_lt_div hs).mpr
    exact strict_midpoint_distance hR hξR
      (tangent_disk_closure_distance hdis z (closure_mono inter_subset_left hz)) hneξ

theorem exterior_tangent_disk_regular :
    Specs.D12Complex.Ch14.GeometricBarriers.exterior_tangent_disk_regular_type := by
  intro Ω ξ c R hΩ hξ hD
  obtain ⟨r, hb⟩ := exterior_tangent_disk_barrier Ω ξ c R hΩ hξ hD
  exact ⟨hξ, r, tangentLogBarrier ξ c R, hb⟩

end D12Complex.GeometricBarriers
