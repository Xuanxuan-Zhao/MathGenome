import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.SectorPhragmenLindelof
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.BoundaryModulus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Sector Phragmén–Lindelöf (paper.tex:1561–1608).

The barrier is `exp (-ε z^γ)` with `β < γ < α`. A compact-superlevel
maximum argument handles the finite boundary limsups and decay at infinity
directly. For sharpness, continuity of absolute principal argument away from
zero gives the modulus limit even across the negative-ray cut.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace D12Complex.SectorPhragmenLindelof

/-- The canonical sector from the independent specification. -/
abbrev sector : Specs.D12Complex.Ch06.SectorPhragmenLindelof.sector_type :=
  Definitions.sector

/-- Affine image of the canonical sector. -/
abbrev affineSector : Specs.D12Complex.Ch06.SectorPhragmenLindelof.affineSector_type :=
  Definitions.affineSector

/-- The critical-growth example on the principal sector branch. -/
abbrev criticalExample : Specs.D12Complex.Ch06.SectorPhragmenLindelof.criticalExample_type :=
  Definitions.criticalExample

theorem halfOpening_pos {α : ℝ} (hα : 1 / 2 ≤ α) :
    0 < Real.pi / (2 * α) :=
  div_pos Real.pi_pos (by linarith)

theorem halfOpening_le_pi {α : ℝ} (hα : 1 / 2 ≤ α) :
    Real.pi / (2 * α) ≤ Real.pi := by
  apply (div_le_iff₀ (by linarith : 0 < 2 * α)).mpr
  nlinarith [Real.pi_pos]

theorem positive_mem_sector {α r : ℝ} (hα : 1 / 2 ≤ α) (hr : 0 < r) :
    (r : ℂ) ∈ sector α := by
  refine ⟨?_, ?_⟩
  · exact Complex.mem_slitPlane_iff.mpr (by simpa using hr)
  · simpa [Complex.arg_ofReal_of_nonneg hr.le] using halfOpening_pos hα

theorem sector_eq_exp_image {α : ℝ} (hα : 1 / 2 ≤ α) :
    sector α = Complex.exp '' {w : ℂ | |w.im| < Real.pi / (2 * α)} := by
  ext z
  constructor
  · intro hz
    refine ⟨Complex.log z, ?_, Complex.exp_log (Complex.slitPlane_ne_zero hz.1)⟩
    simpa only [mem_ofPred_eq, Complex.log_im] using hz.2
  · rintro ⟨w, hw, rfl⟩
    have hwπ : |w.im| < Real.pi := hw.trans_le (halfOpening_le_pi hα)
    have hs : Complex.exp w ∈ Complex.slitPlane :=
      Complex.expOpenPartialHomeomorph.map_source (abs_lt.mp hwπ)
    refine ⟨hs, ?_⟩
    have hl := Complex.log_exp (abs_lt.mp hwπ).1 (abs_lt.mp hwπ).2.le
    simpa only [mem_ofPred_eq, ← Complex.log_im, hl] using hw

theorem isDomain_sector {α : ℝ} (hα : 1 / 2 ≤ α) : IsDomain (sector α) := by
  have ho : IsOpen {w : ℂ | |w.im| < Real.pi / (2 * α)} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  have hc : Convex ℝ {w : ℂ | |w.im| < Real.pi / (2 * α)} := by
    simpa only [abs_lt, ofPred_and] using
      (convex_halfSpace_im_gt (-(Real.pi / (2 * α)))).inter
        (convex_halfSpace_im_lt (Real.pi / (2 * α)))
  refine ⟨⟨1, by simpa using positive_mem_sector hα zero_lt_one⟩, ?_, ?_⟩
  · rw [sector_eq_exp_image hα]
    exact Complex.isOpenMap_exp _ ho
  · rw [sector_eq_exp_image hα]
    exact hc.isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem zero_mem_frontier {α : ℝ} (hα : 1 / 2 ≤ α) : 0 ∈ frontier (sector α) := by
  rw [frontier, (isDomain_sector hα).2.1.interior_eq]
  refine ⟨Metric.mem_closure_iff.mpr ?_, ?_⟩
  · intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), positive_mem_sector hα (by linarith), ?_⟩
    simpa [dist_eq_norm, abs_of_pos hε] using
      (show ε / 2 < ε by linarith)
  · exact fun h => Complex.slitPlane_ne_zero h.1 rfl

/-- A boundary-limsup maximum principle with a bound outside a sufficiently
large disk. No boundary extension is assumed. -/
theorem norm_le_of_boundary_and_infinity {Ω : Set ℂ} {f : ℂ → ℂ} {M : ℝ}
    (hΩ : IsDomain Ω) (hf : HolomorphicOn Ω f)
    (hfr : (frontier Ω).Nonempty)
    (hlim : ∀ ξ ∈ frontier Ω, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[Ω] ξ, ‖f z‖ < M + ε)
    (hinf : ∀ c : ℝ, M < c → ∃ R : ℝ,
      ∀ z ∈ Ω, R ≤ ‖z‖ → ‖f z‖ < c) :
    ∀ z ∈ Ω, ‖f z‖ ≤ M := by
  intro z hz
  by_contra hn
  obtain ⟨c, hMc, hcz⟩ := exists_between (lt_of_not_ge hn)
  let K : Set ℂ := {w | w ∈ Ω ∧ c ≤ ‖f w‖}
  have hKΩ : K ⊆ Ω := fun w hw => hw.1
  have hcl : closure K ⊆ Ω := by
    intro w hw
    by_contra hwΩ
    have hwfront : w ∈ frontier Ω := by
      rw [frontier, hf.1.interior_eq]
      exact ⟨closure_mono hKΩ hw, hwΩ⟩
    have hev : ∀ᶠ v in 𝓝 w, v ∈ Ω → ‖f v‖ < c := by
      simpa only [add_sub_cancel] using
        (eventually_nhdsWithin_iff.mp (hlim w hwfront (c - M) (sub_pos.mpr hMc)))
    obtain ⟨v, hvK, hv⟩ := ((mem_closure_iff_frequently.mp hw).and_eventually hev).exists
    exact (not_lt_of_ge hvK.2) (hv hvK.1)
  obtain ⟨R, hR⟩ := hinf c hMc
  have hb : Bornology.IsBounded K := by
    apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_not_ge (fun hn => (hR w hw.1 hn).not_ge hw.2)
  have hcK : IsCompact (closure K) := hb.isCompact_closure
  have hcont : ContinuousOn (fun w => ‖f w‖) (closure K) :=
    fun w hw => ((hf.2 w (hcl hw)).continuousAt.norm).continuousWithinAt
  obtain ⟨a, ha, hmax⟩ := hcK.exists_isMaxOn
    ⟨z, subset_closure ⟨hz, hcz.le⟩⟩ hcont
  have hza : ‖f z‖ ≤ ‖f a‖ := hmax (subset_closure ⟨hz, hcz.le⟩)
  have hglobal : ∀ w ∈ Ω, ‖f w‖ ≤ ‖f a‖ := by
    intro w hw
    by_cases hcw : c ≤ ‖f w‖
    · exact hmax (subset_closure ⟨hw, hcw⟩)
    · exact (lt_of_not_ge hcw).le.trans (hcz.le.trans hza)
  have hlocal : IsLocalMaxOn (fun w => ‖f w‖) Ω a := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hglobal w hw
  have heq := StrongModulus.constant_of_local_maximum_modulus Ω f a hΩ hf (hcl ha) hlocal
  obtain ⟨ξ, hξ⟩ := hfr
  have : NeBot (𝓝[Ω] ξ) := mem_closure_iff_nhdsWithin_neBot.mp
    (frontier_subset_closure hξ)
  have hmem : ∀ᶠ w in 𝓝[Ω] ξ, w ∈ Ω := self_mem_nhdsWithin
  obtain ⟨w, hwΩ, hw⟩ :=
    (hmem.and (hlim ξ hξ (c - M) (sub_pos.mpr hMc))).exists
  have hw' : ‖f a‖ < c := by simpa [heq w hwΩ] using hw
  exact (not_lt_of_ge (hcz.le.trans hza)) hw'

theorem principalPower_eq_exp (γ : ℝ) (z : ℂ) :
    principalPower (γ : ℂ) z = Complex.exp ((γ : ℂ) * Complex.log z) := by
  change E ((γ : ℂ) * PrincipalLog z) = _
  rw [Exponential.E_eq_exp]
  rfl

theorem principalPower_re {z : ℂ} (hz : z ≠ 0) (γ : ℝ) :
    (principalPower (γ : ℂ) z).re = ‖z‖ ^ γ * Real.cos (γ * z.arg) := by
  rw [principalPower_eq_exp, Complex.exp_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.log_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.mul_im, Complex.log_im, add_zero]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm (Real.log ‖z‖)]

theorem norm_principalPower {z : ℂ} (hz : z ≠ 0) (γ : ℝ) :
    ‖principalPower (γ : ℂ) z‖ = ‖z‖ ^ γ := by
  rw [principalPower_eq_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.log_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), mul_comm (Real.log ‖z‖)]

theorem principalPower_differentiable {α : ℝ} {z : ℂ} (hz : z ∈ sector α) (γ : ℝ) :
    DifferentiableAt ℂ (principalPower (γ : ℂ)) z := by
  apply (ChosenPowers.holomorphicOn_principalPower _).2
  rw [PrincipalLogarithm.principalSlitPlane_eq_slitPlane]
  exact hz.1

theorem sector_power_re_lower {α γ : ℝ} (_hα : 1 / 2 ≤ α)
    (hγ : 0 ≤ γ) (hγα : γ < α) {z : ℂ} (hz : z ∈ sector α) :
    Real.cos (γ * (Real.pi / (2 * α))) * ‖z‖ ^ γ ≤
      (principalPower (γ : ℂ) z).re := by
  rw [principalPower_re (Complex.slitPlane_ne_zero hz.1)]
  have hangle : γ * (Real.pi / (2 * α)) < Real.pi / 2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < 2 * α)).mpr
    nlinarith [Real.pi_pos]
  have harg : |γ * z.arg| ≤ γ * (Real.pi / (2 * α)) := by
    rw [abs_mul, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left hz.2.le hγ
  have hcos : Real.cos (γ * (Real.pi / (2 * α))) ≤ Real.cos (γ * z.arg) := by
    rw [← Real.cos_abs (γ * z.arg)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (hangle.le.trans (by linarith [Real.pi_pos])) harg
  nlinarith [Real.rpow_nonneg (norm_nonneg z) γ]

theorem power_exponential_decay {β γ d : ℝ} (hβγ : β < γ) (hγ : 0 < γ)
    (hd : 0 < d) (A B : ℝ) :
    Tendsto (fun r : ℝ => A * Real.exp (B * r ^ β - d * r ^ γ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun r : ℝ => r ^ (β - γ)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hβγ)
  have hcoef : Tendsto (fun r : ℝ => B * r ^ (β - γ) - d) atTop (𝓝 (-d)) := by
    simpa using (tendsto_const_nhds.mul hr).sub tendsto_const_nhds
  have hexp : Tendsto (fun r : ℝ => B * r ^ β - d * r ^ γ) atTop atBot := by
    apply (hcoef.neg_mul_atTop (neg_neg_of_pos hd) (tendsto_rpow_atTop hγ)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [sub_mul, mul_assoc, ← Real.rpow_add hr, sub_add_cancel]
  simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hexp)

theorem norm_le : Specs.D12Complex.Ch06.SectorPhragmenLindelof.norm_le_type := by
  intro α f M A B β R hα hf hM hlim hA hB hβ hβα hgrowth z hz
  obtain ⟨γ, hβγ, hγα⟩ := exists_between hβα
  have hγ : 0 < γ := hβ.trans_lt hβγ
  let c := Real.cos (γ * (Real.pi / (2 * α)))
  have hc : 0 < c := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < γ * (Real.pi / (2 * α)) := mul_pos hγ (halfOpening_pos hα)
      linarith [Real.pi_pos]
    · rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by linarith : 0 < 2 * α)).mpr
      nlinarith [Real.pi_pos]
  have hpower (w : ℂ) (hw : w ∈ sector α) :
      c * ‖w‖ ^ γ ≤ (principalPower (γ : ℂ) w).re :=
    sector_power_re_lower hα hγ.le hγα hw
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ∀ w ∈ sector α,
        ‖f w * Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) w)‖ ≤ M := by
    let F : ℂ → ℂ := fun w => f w * Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) w)
    have hnorm (w : ℂ) :
        ‖Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) w)‖ =
          Real.exp (-ε * (principalPower (γ : ℂ) w).re) := by
      simp [Complex.norm_exp, Complex.mul_re]
    have hsmall (w : ℂ) (hw : w ∈ sector α) :
        ‖Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) w)‖ ≤ 1 := by
      rw [hnorm, Real.exp_le_one_iff]
      have hp : 0 ≤ (principalPower (γ : ℂ) w).re :=
        (mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg w) γ)).trans (hpower w hw)
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hp
    have hFsmall (w : ℂ) (hw : w ∈ sector α) : ‖F w‖ ≤ ‖f w‖ := by
      dsimp [F]
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hsmall w hw) (norm_nonneg _)).trans_eq (mul_one _)
    have hF : HolomorphicOn (sector α) F := by
      refine ⟨hf.1, fun w hw => ?_⟩
      exact (hf.2 w hw).mul (((principalPower_differentiable hw γ).const_mul _).cexp)
    apply norm_le_of_boundary_and_infinity (isDomain_sector hα) hF
      ⟨0, zero_mem_frontier hα⟩
    · intro ξ hξ δ hδ
      filter_upwards [self_mem_nhdsWithin, hlim ξ hξ δ hδ] with w hw hfw
      exact (hFsmall w hw).trans_lt hfw
    · intro k hk
      have hk0 : 0 < k := hM.trans_lt hk
      have hdecay := power_exponential_decay hβγ hγ (mul_pos hε hc) A B
      obtain ⟨T, hT⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds hk0))
      refine ⟨max R T, fun w hw hwR => ?_⟩
      have hrR : R ≤ ‖w‖ := (le_max_left _ _).trans hwR
      have hrT : T ≤ ‖w‖ := (le_max_right _ _).trans hwR
      apply lt_of_le_of_lt ?_ (hT _ hrT)
      change ‖f w * Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) w)‖ ≤ _
      rw [norm_mul, hnorm]
      calc
        _ ≤ (A * Real.exp (B * ‖w‖ ^ β)) * Real.exp (-ε * (c * ‖w‖ ^ γ)) := by
          apply mul_le_mul (hgrowth w hw hrR) (Real.exp_le_exp.mpr ?_)
            (Real.exp_pos _).le (mul_nonneg hA.le (Real.exp_pos _).le)
          exact mul_le_mul_of_nonpos_left (hpower w hw) (neg_nonpos.mpr hε.le)
        _ = A * Real.exp (B * ‖w‖ ^ β - (ε * c) * ‖w‖ ^ γ) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have ht : ContinuousAt
      (fun ε : ℝ => ‖f z * Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) z)‖) 0 := by
    fun_prop
  have ht' : Tendsto
      (fun ε : ℝ => ‖f z * Complex.exp (-(ε : ℂ) * principalPower (γ : ℂ) z)‖)
      (𝓝[>] 0) (𝓝 ‖f z‖) := by
    simpa using ht.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε z hz

theorem sector_polar : Specs.D12Complex.Ch06.SectorPhragmenLindelof.sector_polar_type := by
  intro α hα z
  constructor
  · intro hz
    have harg := PrincipalLogarithm.principalArg_bounds z
      (PrincipalLogarithm.principalSlitPlane_eq_slitPlane ▸ hz.1)
    exact ⟨‖z‖, z.arg, norm_pos_iff.mpr (Complex.slitPlane_ne_zero hz.1),
      hz.2, harg.1, harg.2, (Complex.norm_mul_exp_arg_mul_I z).symm⟩
  · rintro ⟨r, θ, hr, hθ, _, _, rfl⟩
    change (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ sector α
    rw [sector_eq_exp_image hα]
    refine ⟨(Real.log r : ℂ) + (θ : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using hθ
    · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

theorem norm_le_affine : Specs.D12Complex.Ch06.SectorPhragmenLindelof.norm_le_affine_type := by
  intro α a b f M A B β R hα ha hf hM hlim hA hB hβ hβα hgrowth w hw
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addLeft b)
  have he (z : ℂ) : e z = b + a * z := rfl
  have hcoord (z : ℂ) : (b + a * z - b) / a = z := by
    field_simp
    ring
  have hmaps : MapsTo e (sector α) (affineSector α a b) := fun z hz => ⟨z, hz, rfl⟩
  have hfront (ξ : ℂ) (hξ : ξ ∈ frontier (sector α)) :
      e ξ ∈ frontier (affineSector α a b) := by
    change e ξ ∈ frontier (e '' sector α)
    rw [← e.image_frontier]
    exact mem_image_of_mem e hξ
  have hcomp : HolomorphicOn (sector α) (fun z => f (e z)) := by
    refine ⟨(isDomain_sector hα).2.1, fun z hz => ?_⟩
    exact (hf.2 (e z) (hmaps hz)).comp z
      ((differentiableAt_id.const_mul a).const_add b)
  have hbound := norm_le α (fun z => f (e z)) M A B β R hα hcomp hM
    (fun ξ hξ δ hδ => ?_) hA hB hβ hβα (fun z hz hzR => ?_)
  · obtain ⟨z, hz, rfl⟩ := hw
    exact hbound z hz
  · have ht : Tendsto e (𝓝[sector α] ξ) (𝓝[affineSector α a b] (e ξ)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨e.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          by filter_upwards [self_mem_nhdsWithin] with z hz; exact hmaps hz⟩
    exact ht.eventually (hlim (e ξ) (hfront ξ hξ) δ hδ)
  · simpa only [he, hcoord] using hgrowth (e z) (hmaps hz) (by simpa only [he, hcoord] using hzR)

theorem abs_arg_eq_arccos {z : ℂ} (hz : z ≠ 0) :
    |z.arg| = Real.arccos (z.re / ‖z‖) := by
  rw [← Complex.cos_arg hz, ← Real.cos_abs z.arg,
    Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi _)]

/-- Taking the absolute value removes the jump of principal argument at the cut. -/
theorem continuousAt_abs_arg {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w : ℂ => |w.arg|) z := by
  have he : (fun w : ℂ => |w.arg|) =ᶠ[𝓝 z]
      (fun w => Real.arccos (w.re / ‖w‖)) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact abs_arg_eq_arccos hw
  exact (Real.continuous_arccos.continuousAt.comp
    (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt
      (norm_ne_zero_iff.mpr hz))).congr_of_eventuallyEq he

theorem frontier_abs_arg {α : ℝ} (hα : 1 / 2 ≤ α) {ξ : ℂ}
    (hξ : ξ ∈ frontier (sector α)) (hne : ξ ≠ 0) :
    |ξ.arg| = Real.pi / (2 * α) := by
  have : NeBot (𝓝[sector α] ξ) := mem_closure_iff_nhdsWithin_neBot.mp
    (frontier_subset_closure hξ)
  have hle : |ξ.arg| ≤ Real.pi / (2 * α) := by
    apply le_of_tendsto ((continuousAt_abs_arg hne).tendsto.mono_left
      (nhdsWithin_le_nhds (s := sector α)))
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.2.le
  apply hle.antisymm
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hslit : ξ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff_arg.mpr
    exact ⟨ne_of_lt ((le_abs_self _).trans_lt (hlt.trans_le (halfOpening_le_pi hα))), hne⟩
  have hnot : ξ ∉ sector α := by
    rw [frontier, (isDomain_sector hα).2.1.interior_eq] at hξ
    exact hξ.2
  exact hnot ⟨hslit, hlt⟩

theorem norm_criticalExample {z : ℂ} (hz : z ≠ 0) (α : ℝ) :
    ‖criticalExample α z‖ = Real.exp (‖z‖ ^ α * Real.cos (α * |z.arg|)) := by
  rw [criticalExample, Definitions.criticalExample, Complex.norm_exp, principalPower_re hz]
  congr 2
  rw [← Real.cos_abs (α * z.arg), ← Real.cos_abs (α * |z.arg|)]
  simp only [abs_mul, abs_abs]

theorem criticalExample_boundary {α : ℝ} (hα : 1 / 2 ≤ α) :
    ∀ ξ ∈ frontier (sector α),
      Tendsto (fun z => ‖criticalExample α z‖) (𝓝[sector α] ξ) (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  intro ξ hξ
  by_cases hne : ξ = 0
  · subst ξ
    have ht : Tendsto (fun z : ℂ => ‖z‖ ^ α) (𝓝[sector α] 0) (𝓝 0) := by
      have hc : Continuous (fun z : ℂ => ‖z‖ ^ α) :=
        continuous_norm.rpow_const (fun _ => Or.inr hα0.le)
      simpa [Real.zero_rpow hα0.ne'] using hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := sector α) (a := (0 : ℂ)))
    have hnorm : Tendsto (fun z => ‖principalPower (α : ℂ) z‖)
        (𝓝[sector α] 0) (𝓝 0) := by
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (norm_principalPower (Complex.slitPlane_ne_zero hz.1) α).symm
    have hp : Tendsto (principalPower (α : ℂ)) (𝓝[sector α] 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    simpa [criticalExample, Definitions.criticalExample] using (Complex.continuous_exp.continuousAt.tendsto.comp hp).norm
  · have hc : ContinuousAt (fun z : ℂ =>
        Real.exp (‖z‖ ^ α * Real.cos (α * |z.arg|))) ξ :=
      Real.continuous_exp.continuousAt.comp
        ((continuous_norm.continuousAt.rpow_const (Or.inr hα0.le)).mul
          (Real.continuous_cos.continuousAt.comp
            ((continuousAt_abs_arg hne).const_mul α)))
    have hangle : α * (Real.pi / (2 * α)) = Real.pi / 2 := by
      field_simp
    have hv : Real.exp (‖ξ‖ ^ α * Real.cos (α * |ξ.arg|)) = 1 := by
      rw [frontier_abs_arg hα hξ hne, hangle, Real.cos_pi_div_two, mul_zero, Real.exp_zero]
    rw [← hv]
    apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (norm_criticalExample (Complex.slitPlane_ne_zero hz.1) α).symm

theorem sharpness : Specs.D12Complex.Ch06.SectorPhragmenLindelof.sharpness_type := by
  intro α hα
  have hα0 : 0 < α := by linarith
  refine ⟨⟨(isDomain_sector hα).2.1, fun z hz =>
    (principalPower_differentiable hz α).cexp⟩,
    criticalExample_boundary hα, ?_, fun r hr => positive_mem_sector hα hr, ?_⟩
  · intro z hz
    rw [norm_criticalExample (Complex.slitPlane_ne_zero hz.1)]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.rpow_nonneg (norm_nonneg z) α)).trans_eq
      (mul_one _)
  · apply (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hα0)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [norm_criticalExample (Complex.ofReal_ne_zero.mpr hr.ne')]
    simp [Complex.arg_ofReal_of_nonneg hr.le, abs_of_pos hr]

end D12Complex.SectorPhragmenLindelof
