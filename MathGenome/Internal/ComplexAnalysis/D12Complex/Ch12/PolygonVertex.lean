import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.PolygonVertex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.AnalyticArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.ChosenPowers
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace D12Complex.PolygonVertex

namespace Definitions
abbrev halfPlane := D12Complex.PolygonVertex.halfPlane
abbrev closedHalfPlane := D12Complex.PolygonVertex.closedHalfPlane
abbrev compactifiedClosedHalfPlane := D12Complex.PolygonVertex.compactifiedClosedHalfPlane
abbrev HasBoundaryExtension := D12Complex.PolygonVertex.HasBoundaryExtension
abbrev wedge := D12Complex.PolygonVertex.wedge
abbrev Corner := D12Complex.PolygonVertex.Corner
abbrev upperPower := D12Complex.PolygonVertex.upperPower
abbrev HasCornerFactor := D12Complex.PolygonVertex.HasCornerFactor
abbrev HasLogDerivExtension := D12Complex.PolygonVertex.HasLogDerivExtension
end Definitions

private lemma analyticAt_of_holomorphic {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z :=
  (show DifferentiableOn ℂ f U from fun w hw =>
    (hf.2 w hw).differentiableWithinAt).analyticAt (hf.1.mem_nhds hz)

private lemma holomorphic_deriv {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) : HolomorphicOn U (deriv f) :=
  ⟨hf.1, fun _ hz => (analyticAt_of_holomorphic hf hz).deriv.differentiableAt⟩

theorem simple_zero_factor :
    Specs.D12Complex.Ch12.PolygonVertex.simple_zero_factor_type := by
  intro q a hq hzero hn
  obtain ⟨p, hp⟩ := hq
  have hb : AnalyticAt ℂ (dslope q a) a :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  obtain ⟨U, haU, hU⟩ :=
    (LocalZeroFactorization.holomorphicNear_iff_analyticAt (dslope q a) a).mpr hb
  have he : ∀ᶠ z in 𝓝 a, dslope q a z ≠ 0 :=
    hb.continuousAt.eventually_ne (by simpa using hn)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.1.mem_nhds haU) he)
  refine ⟨r, dslope q a, hr, ⟨isOpen_ball, fun z hz => hU.2 z (hrU hz).1⟩,
    fun z hz => (hrU hz).2, dslope_same q a, ?_⟩
  intro z _
  simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hzero z).symm

theorem straightening_reflection :
    Specs.D12Complex.Ch12.PolygonVertex.straightening_reflection_type := by
  intro a r q hr hq hc hreal hi hnc hpos hzero
  obtain ⟨hQ, hagree, _, _⟩ :=
    Reflection.schwarz_reflection a r q (by simp) hr hq hc hreal
  have hQzero : Reflection.extension q a = 0 := by
    rw [hagree ⟨mem_ball_self hr, by simp⟩, hzero]
  have hQnc := AnalyticArcs.reflection_deriv_ne_zero (by simp) hr hq hc hreal hi hnc hpos
  obtain ⟨s, b, hs, hb, hbn, _, he⟩ := simple_zero_factor (Reflection.extension q) a
    (analyticAt_of_holomorphic hQ (mem_ball_self hr)) hQzero hQnc
  let t := min s r
  have ht : 0 < t := lt_min hs hr
  have hts : ball (a : ℂ) t ⊆ ball (a : ℂ) s := ball_subset_ball (min_le_left s r)
  have htr : ball (a : ℂ) t ⊆ ball (a : ℂ) r := ball_subset_ball (min_le_right s r)
  refine ⟨t, b, ht, min_le_right s r,
    ⟨isOpen_ball, fun z hz => hb.2 z (hts hz)⟩,
    fun z hz => hbn z (hts hz), ?_⟩
  intro z hz
  rw [← hagree ⟨htr hz.1, hz.2⟩]
  exact he z (hts hz.1)

/-- The principal slit branch restricted to H; this derivative never uses a
branch-independent power-of-a-product rule. -/
theorem hasDerivAt_upperPower (α : ℂ) (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (upperPower α a)
      (upperPower α a z * (α / (z - (a : ℂ)))) z := by
  have hslit : z - (a : ℂ) ∈ PrincipalSlitPlane :=
    (PrincipalLogarithm.mem_principalSlitPlane_iff _).mpr (Or.inr (by
      simpa using ne_of_gt hz))
  have hl := (PrincipalLogarithm.hasDerivAt_principalLog _ hslit).comp z
    ((hasDerivAt_id z).sub_const (a : ℂ))
  have hd := (Exponential.hasDerivAt_E (α * PrincipalLog (z - (a : ℂ)))).comp z
    (hl.const_mul α)
  convert hd using 1 <;> first | rfl | simp [upperPower, principalPower, powerWithLog, div_eq_mul_inv]

private lemma upperPower_ne_zero (α : ℂ) (a : ℝ) (z : ℂ) :
    upperPower α a z ≠ 0 := Exponential.E_ne_zero _

private lemma upper_ne_prevertex (a : ℝ) {z : ℂ} (hz : 0 < z.im) :
    z - (a : ℂ) ≠ 0 := by
  intro he
  have : z = (a : ℂ) := sub_eq_zero.mp he
  simp [this] at hz

/-- Differentiate the factorization on its actual open upper-side domain. -/
theorem deriv_corner_factor {U : Set ℂ} {F u : ℂ → ℂ} {a : ℝ} {v α : ℂ}
    (hu : HolomorphicOn U u)
    (he : ∀ z ∈ U ∩ halfPlane, F z - v = upperPower α a z * u z) :
    ∀ z ∈ U ∩ halfPlane,
      deriv F z = upperPower α a z *
        ((α * u z + (z - (a : ℂ)) * deriv u z) / (z - (a : ℂ))) := by
  intro z hz
  have hw := upper_ne_prevertex a hz.2
  have hp := hasDerivAt_upperPower α a hz.2
  have hd := (hp.mul (hu.2 z hz.1).hasDerivAt).const_add v
  have hevent : F =ᶠ[𝓝 z] (fun w => v + upperPower α a w * u w) := by
    filter_upwards [(hu.1.inter (isOpen_lt continuous_const continuous_im)).mem_nhds hz] with w hw
    exact (sub_eq_iff_eq_add.mp (he w hw)).trans (add_comm _ _)
  have hF := hd.congr_of_eventuallyEq hevent
  rw [hF.deriv]
  field_simp

/-- Removing the prescribed simple principal part is a local analytic
consequence of the unit factor. Its denominator at a is α*u(a), so the
nonzero-angle premise is used rather than assumed away. -/
theorem logDeriv_of_cornerFactor :
    Specs.D12Complex.Ch12.PolygonVertex.logDeriv_of_cornerFactor_type := by
  intro F a v α hα hfac
  obtain ⟨r, u, hr, hu, hun, he⟩ := hfac
  let p : ℂ → ℂ := fun z => α * u z + (z - (a : ℂ)) * deriv u z
  have hdu := holomorphic_deriv hu
  have hp : HolomorphicOn (ball (a : ℂ) r) p := by
    refine ⟨isOpen_ball, fun z hz => ?_⟩
    exact ((hu.2 z hz).const_mul α).add
      ((differentiableAt_id.sub_const (a : ℂ)).mul (hdu.2 z hz))
  have hpa : p a ≠ 0 := by
    simpa [p] using mul_ne_zero hα (hun a (mem_ball_self hr))
  have hpn := (hp.2 a (mem_ball_self hr)).continuousAt.eventually_ne hpa
  obtain ⟨s, hs, hsr⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) hpn)
  have hdp := holomorphic_deriv hp
  let h : ℂ → ℂ := fun z => deriv p z / p z
  refine ⟨s, h, hs, ⟨isOpen_ball, fun z hz =>
    (hdp.2 z (hsr hz).1).div (hp.2 z (hsr hz).1) (hsr hz).2⟩, ?_⟩
  intro z hz
  have hzr := (hsr hz.1).1
  have hn : p z ≠ 0 := (hsr hz.1).2
  have hw := upper_ne_prevertex a hz.2
  have hpow := upperPower_ne_zero α a z
  have hF : EqOn (deriv F)
      (fun w => upperPower α a w * (p w / (w - (a : ℂ))))
      (ball (a : ℂ) r ∩ halfPlane) := deriv_corner_factor hu he
  have hF2 := hF.deriv
    (isOpen_ball.inter (isOpen_lt continuous_const continuous_im)) ⟨hzr, hz.2⟩
  have hd := (hasDerivAt_upperPower α a hz.2).mul
    ((hp.2 z hzr).hasDerivAt.div ((hasDerivAt_id z).sub_const (a : ℂ)) hw)
  have hd' : HasDerivAt (fun w => upperPower α a w * (p w / (w - (a : ℂ)) ))
      (upperPower α a z * (α / (z - (a : ℂ))) * (p z / (z - (a : ℂ))) +
        upperPower α a z * ((deriv p z * (z - (a : ℂ)) - p z) / (z - (a : ℂ))^2)) z :=
    by convert hd using 1 <;> first | rfl | simp
  rw [hF2, hd'.deriv, hF ⟨hzr, hz.2⟩]
  dsimp [h]
  field_simp [hw, hn, hpow]
  ring

/-- A local logarithm of the simple-zero unit absorbs the possible integral
logarithm shift. Constancy is proved on the connected upper half-disk;
no unqualified logarithm-of-a-product formula is invoked. -/
theorem power_simple_zero_factor :
    Specs.D12Complex.Ch12.PolygonVertex.power_simple_zero_factor_type := by
  intro q a R α hR hq hzero hn hpos
  obtain ⟨r, b, hr, hb, hbn, _, hfactor⟩ := simple_zero_factor q a
    (analyticAt_of_holomorphic hq (mem_ball_self hR)) hzero hn
  have hba : b a ≠ 0 := hbn a (mem_ball_self hr)
  have hexp : E (Complex.log (b a)) = b a := by
    rw [Exponential.E_eq_exp, Complex.exp_log hba]
  obtain ⟨U, L, haU, hUr, hL, _, hEL, hdL⟩ :=
    LocalLogarithmsRoots.local_logarithm (ball (a : ℂ) r) b a
      (Complex.log (b a)) hb (mem_ball_self hr) hba hexp
  obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hL.1.mem_nhds haU) (isOpen_ball.mem_nhds (mem_ball_self hR)))
  let t := min s R
  have ht : 0 < t := lt_min hs hR
  have hts : ball (a : ℂ) t ⊆ ball (a : ℂ) s := ball_subset_ball (min_le_left s R)
  have htU : ball (a : ℂ) t ⊆ U := fun z hz => (hsU (hts hz)).1
  have htR : ball (a : ℂ) t ⊆ ball (a : ℂ) R := ball_subset_ball (min_le_right s R)
  have htr : ball (a : ℂ) t ⊆ ball (a : ℂ) r := fun z hz => hUr (htU hz)
  let D : ℂ → ℂ := fun z => PrincipalLog (q z) - PrincipalLog (z - (a : ℂ)) - L z
  have hdD : ∀ z ∈ ball (a : ℂ) t ∩ halfPlane, HasDerivAt D 0 z := by
    intro z hz
    have hqslit : q z ∈ PrincipalSlitPlane :=
      (PrincipalLogarithm.mem_principalSlitPlane_iff _).mpr
        (Or.inr (ne_of_gt (hpos z ⟨htR hz.1, hz.2⟩)))
    have hwslit : z - (a : ℂ) ∈ PrincipalSlitPlane :=
      (PrincipalLogarithm.mem_principalSlitPlane_iff _).mpr (Or.inr (by
        simpa using ne_of_gt hz.2))
    have hw := upper_ne_prevertex a hz.2
    have hbz := hbn z (htr hz.1)
    have hqz : q z ≠ 0 := PrincipalLogarithm.principalSlitPlane_ne_zero _ hqslit
    have hqf : q =ᶠ[𝓝 z] (fun w => (w - (a : ℂ)) * b w) :=
      eventually_of_mem (isOpen_ball.mem_nhds (htr hz.1)) (fun w hw => hfactor w hw)
    have hqd : deriv q z = b z + (z - (a : ℂ)) * deriv b z := by
      have hdd := ((hasDerivAt_id z).sub_const (a : ℂ)).mul (hb.2 z (htr hz.1)).hasDerivAt
      have hdd' : HasDerivAt (fun w => (w - (a : ℂ)) * b w)
          (b z + (z - (a : ℂ)) * deriv b z) z := by
        convert hdd using 1 <;> first | rfl | simp
      rw [hqf.deriv_eq, hdd'.deriv]
    have hd := (((PrincipalLogarithm.hasDerivAt_principalLog _ hqslit).comp z
      (hq.2 z (htR hz.1)).hasDerivAt).sub
        ((PrincipalLogarithm.hasDerivAt_principalLog _ hwslit).comp z
          ((hasDerivAt_id z).sub_const (a : ℂ)))).sub (hdL z (htU hz.1))
    have hv : 1 / q z * deriv q z - 1 / (z - (a : ℂ)) * 1 - deriv b z / b z = 0 := by
      rw [hqd, hfactor z (htr hz.1)]
      field_simp
      ring
    convert hd using 1 <;> first | rfl | exact hv.symm
  have hopen : IsOpen (ball (a : ℂ) t ∩ halfPlane) :=
    isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  obtain ⟨d, hd⟩ := hopen.exists_is_const_of_deriv_eq_zero
    (((convex_ball (a : ℂ) t).inter (convex_halfSpace_im_gt 0)).isPreconnected)
    (fun z hz => (hdD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hdD z hz).deriv)
  let u : ℂ → ℂ := fun z => E (α * (L z + d))
  refine ⟨t, u, ht, min_le_right s R, ⟨isOpen_ball, ?_⟩, ?_, ?_⟩
  · intro z hz
    exact (Exponential.hasDerivAt_E _).differentiableAt.comp z
      (((hL.2 z (htU hz)).add_const d).const_mul α)
  · intro z _
    exact Exponential.E_ne_zero _
  · intro z hz
    have hlog : PrincipalLog (q z) = PrincipalLog (z - (a : ℂ)) + (L z + d) := by
      have h := hd z hz
      dsimp [D] at h
      linear_combination h
    change E (α * PrincipalLog (q z)) = E (α * PrincipalLog (z - (a : ℂ))) * E (α * (L z + d))
    rw [hlog, mul_add, Exponential.E_add]

/-- Extract the finite continuous boundary values and their injectivity from
the actual compactified homeomorphism, rather than assuming a boundary inverse. -/
theorem boundary_extension_data {P : Set ℂ} {F : ℂ → ℂ}
    (h : HasBoundaryExtension P F) :
    ContinuousOn F closedHalfPlane ∧ InjOn F closedHalfPlane ∧
      MapsTo F closedHalfPlane (closure P) := by
  obtain ⟨e, he⟩ := h
  let j : closedHalfPlane → compactifiedClosedHalfPlane :=
    fun z => ⟨sphereFinite z, Or.inr ⟨z, z.property, rfl⟩⟩
  have hj : Continuous j :=
    (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _
  have hc : Continuous (fun z : closedHalfPlane => (e (j z) : ℂ)) :=
    continuous_subtype_val.comp (e.continuous.comp hj)
  refine ⟨?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    convert hc using 1
    funext z
    exact (he z z.property).symm
  · intro z hz w hw hzw
    have heq : e (j ⟨z, hz⟩) = e (j ⟨w, hw⟩) := by
      apply Subtype.ext
      exact (he z hz).trans (hzw.trans (he w hw).symm)
    have hj := congrArg Subtype.val (e.injective heq)
    exact OnePoint.coe_injective hj
  · intro z hz
    rw [← he z hz]
    exact (e (j ⟨z, hz⟩)).property

/-- Boundary points cannot map to the interior, by the interior inverse and
injectivity of the homeomorphic extension. -/
theorem boundary_real_frontier {P : Set ℂ} {F G : ℂ → ℂ}
    (hp : BiholomorphicPair halfPlane P F G) (he : HasBoundaryExtension P F)
    {z : ℂ} (hz : z.im = 0) : F z ∈ frontier P := by
  obtain ⟨_, hi, hm⟩ := boundary_extension_data he
  have hzC : z ∈ closedHalfPlane := by change 0 ≤ z.im; rw [hz]
  rw [hp.2.1.1.frontier_eq]
  refine ⟨hm hzC, ?_⟩
  intro hF
  have hg : G (F z) ∈ halfPlane := hp.2.2.2.1 hF
  have hgC : G (F z) ∈ closedHalfPlane := by
    change 0 ≤ (G (F z)).im
    exact le_of_lt (show 0 < (G (F z)).im from hg)
  have hid : G (F z) = z := hi hgC hzC (hp.2.2.2.2.2 hF)
  rw [hid] at hg
  simp [halfPlane, hz] at hg

/-- A straight angle is exactly a rotated upper half-plane. -/
theorem mem_wedge_one_iff {v c w : ℂ} (hc : c ≠ 0) :
    w ∈ wedge v c 1 ↔ 0 < ((w - v) / c).im := by
  constructor
  · rintro ⟨ρ, θ, hρ, hθ, hθπ, rfl⟩
    have he : (v + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) - v) / c =
        (ρ : ℂ) * exp ((θ : ℂ) * I) := by field_simp; ring
    rw [he]
    simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
      exp_ofReal_mul_I_im] using mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi hθ (by simpa using hθπ))
  · intro hw
    let ζ := (w - v) / c
    have hζ : ζ ≠ 0 := by intro hz; change 0 < ζ.im at hw; simp [hz] at hw
    have ha : 0 < arg ζ := by
      have hnonneg : 0 ≤ arg ζ := arg_nonneg_iff.mpr hw.le
      have hne : arg ζ ≠ 0 := by
        intro hz
        exact (ne_of_gt hw) (arg_eq_zero_iff.mp hz).2
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    refine ⟨‖ζ‖, arg ζ, norm_pos_iff.mpr hζ, ha, ?_, ?_⟩
    · simpa using arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hw))
    · rw [norm_mul_exp_arg_mul_I]
      dsimp [ζ]
      field_simp
      ring

private theorem side_frontier_real {P : Set ℂ} {v c : ℂ} {R : ℝ}
    (hP : IsOpen P) (hc : c ≠ 0)
    (he : P ∩ ball v R = wedge v c 1 ∩ ball v R)
    {w : ℂ} (hw : w ∈ frontier P) (hwR : w ∈ ball v R) :
    ((w - v) / c).im = 0 := by
  rw [hP.frontier_eq] at hw
  have hle : ((w - v) / c).im ≤ 0 := by
    by_contra hn
    have hwm : w ∈ wedge v c 1 := mem_wedge_one_iff hc |>.mpr (lt_of_not_ge hn)
    have hwP : w ∈ P ∩ ball v R := he.symm ▸ ⟨hwm, hwR⟩
    exact hw.2 hwP.1
  have hge : 0 ≤ ((w - v) / c).im := by
    by_contra hn
    let A := ball v R ∩ {ζ : ℂ | ((ζ - v) / c).im < 0}
    have hA : IsOpen A := isOpen_ball.inter
      (isOpen_lt (continuous_im.comp ((continuous_id.sub continuous_const).div_const c)) continuous_const)
    obtain ⟨ζ, hζ, hζP⟩ := mem_closure_iff.mp hw.1 A hA ⟨hwR, lt_of_not_ge hn⟩
    have hwedge : ζ ∈ wedge v c 1 := (he ▸ (show ζ ∈ P ∩ ball v R from ⟨hζP, hζ.1⟩)).1
    exact (not_lt_of_gt (mem_wedge_one_iff hc |>.mp hwedge)) hζ.2
  exact le_antisymm hle hge

/-- At an open side the target line is straightened by an affine map. The
reflected extension has nonzero derivative, derived from the actual interior
inverse and boundary injection. -/
theorem polygon_side : Specs.D12Complex.Ch12.PolygonVertex.polygon_side_type := by
  intro P F G _ _ hp he a hcorner
  obtain ⟨c, R, hc, hR, hgeom⟩ := hcorner
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  obtain ⟨hcont, hi, _⟩ := boundary_extension_data he
  have haC : (a : ℂ) ∈ closedHalfPlane := by simp [closedHalfPlane]
  have hpre : F ⁻¹' ball (F a) R ∈ 𝓝[closedHalfPlane] (a : ℂ) :=
    (hcont a haC).preimage_mem_nhdsWithin (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨r, hr, hval⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let q : ℂ → ℂ := fun z => (F z - F a) / c
  have hqh : HolomorphicOn (Reflection.upper (a : ℂ) r) q := by
    refine ⟨isOpen_ball.inter (isOpen_lt continuous_const continuous_im), ?_⟩
    intro z hz
    exact ((hp.1.2 z hz.2).sub_const (F a)).div_const c
  have hqc : ContinuousOn q (Reflection.upperClosure (a : ℂ) r) :=
    ((hcont.mono (fun z (hz : z ∈ Reflection.upperClosure (a : ℂ) r) => hz.2)).sub continuousOn_const).div_const c
  have hreal : ∀ z ∈ Reflection.diameter (a : ℂ) r, (q z).im = 0 := by
    intro z hz
    exact side_frontier_real hp.2.1.1 hc0 hgeom
      (boundary_real_frontier hp he hz.2) (hval ⟨hz.1, le_of_eq hz.2.symm⟩)
  have hqi : InjOn q (Reflection.upperClosure (a : ℂ) r) := by
    intro z hz w hw hqw
    apply hi hz.2 hw.2
    have hsub : F z - F a = F w - F a :=
      (div_left_inj' hc0).mp hqw
    linear_combination hsub
  have hqnc : ∀ z ∈ Reflection.upper (a : ℂ) r, deriv q z ≠ 0 := by
    intro z hz
    have hd := ((hp.1.2 z hz.2).hasDerivAt.sub_const (F a)).div_const c
    have hd' : HasDerivAt q (deriv F z / c) z := hd
    rw [hd'.deriv]
    exact div_ne_zero (AnalyticArcs.biholomorphic_deriv_ne_zero hp hz.2).1 hc0
  have hpos : ∀ z ∈ Reflection.upper (a : ℂ) r, 0 < (q z).im := by
    intro z hz
    have hmem : F z ∈ P ∩ ball (F a) R :=
      ⟨hp.2.2.1 hz.2, hval ⟨hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩⟩
    exact mem_wedge_one_iff hc0 |>.mp (hgeom ▸ hmem).1
  obtain ⟨hQ, hagree, _, _⟩ := Reflection.schwarz_reflection a r q (by simp) hr hqh hqc hreal
  have hn := AnalyticArcs.reflection_deriv_ne_zero (by simp) hr hqh hqc hreal hqi hqnc hpos
  let f : ℂ → ℂ := fun z => F a + c * Reflection.extension q z
  refine ⟨r, f, hr, ⟨isOpen_ball, fun z hz =>
    ((hQ.2 z hz).const_mul c).const_add (F a)⟩, ?_, ?_⟩
  · have hd := ((hQ.2 a (mem_ball_self hr)).hasDerivAt.const_mul c).const_add (F a)
    have hd' : HasDerivAt f (c * deriv (Reflection.extension q) a) a := hd
    rw [hd'.deriv]
    exact mul_ne_zero hc0 hn
  · intro z hz
    change F a + c * Reflection.extension q z = F z
    rw [hagree hz]
    dsimp [q]
    field_simp
    ring

/-- All analytic steps of the vertex argument, starting with a straightening
on the given upper side and diameter. In particular, neither the reflected
simple zero nor the holomorphic factor is an input certificate. -/
theorem corner_factor_of_straightening :
    Specs.D12Complex.Ch12.PolygonVertex.corner_factor_of_straightening_type := by
  intro F q a v c α r hr hc hq hcont hreal hi hnc hpos hzero hF
  obtain ⟨hQ, hagree, _, _⟩ :=
    Reflection.schwarz_reflection a r q (by simp) hr hq hcont hreal
  have hQzero : Reflection.extension q a = 0 := by
    rw [hagree ⟨mem_ball_self hr, by simp⟩, hzero]
  have hQnc := AnalyticArcs.reflection_deriv_ne_zero (by simp) hr hq hcont hreal hi hnc hpos
  have hQpos : ∀ z ∈ ball (a : ℂ) r ∩ halfPlane,
      0 < (Reflection.extension q z).im := by
    intro z hz
    rw [hagree ⟨hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩]
    exact hpos z hz
  obtain ⟨s, b, hs, hsr, hb, hbn, hpower⟩ :=
    power_simple_zero_factor (Reflection.extension q) a r α hr hQ hQzero hQnc hQpos
  refine ⟨s, fun z => c * b z, hs,
    ⟨isOpen_ball, fun z hz => (hb.2 z hz).const_mul c⟩,
    fun z hz => mul_ne_zero hc (hbn z hz), ?_⟩
  intro z hz
  have hzr : z ∈ ball (a : ℂ) r := ball_subset_ball hsr hz.1
  rw [hF z ⟨hzr, hz.2⟩, ← hagree ⟨hzr, (show 0 ≤ z.im from le_of_lt hz.2)⟩,
    hpower z hz]
  ring

/-- The full vertex conclusion at a straight angle, as a specialization of
the proved side reflection. The general-angle proof appears below. -/
theorem polygon_vertex_angle_one :
    Specs.D12Complex.Ch12.PolygonVertex.polygon_vertex_angle_one_type := by
  intro P F G hP hbound hp he a hcorner
  obtain ⟨r, f, hr, hf, hfn, hagree⟩ := polygon_side P F G hP hbound hp he a hcorner
  have haC : (a : ℂ) ∈ ball (a : ℂ) r ∩ closedHalfPlane :=
    ⟨mem_ball_self hr, by simp [closedHalfPlane]⟩
  have hq : HolomorphicOn (ball (a : ℂ) r) (fun z => f z - F a) :=
    ⟨isOpen_ball, fun z hz => (hf.2 z hz).sub_const (F a)⟩
  have hqn : deriv (fun z => f z - F a) a ≠ 0 := by
    rw [((hf.2 a (mem_ball_self hr)).hasDerivAt.sub_const (F a)).deriv]
    exact hfn
  obtain ⟨s, b, hs, hb, hbn, _, hfac⟩ := simple_zero_factor (fun z => f z - F a) a
    (analyticAt_of_holomorphic hq (mem_ball_self hr)) (by rw [hagree haC, sub_self]) hqn
  let t := min s r
  have ht : 0 < t := lt_min hs hr
  have hts : ball (a : ℂ) t ⊆ ball (a : ℂ) s := ball_subset_ball (min_le_left s r)
  have htr : ball (a : ℂ) t ⊆ ball (a : ℂ) r := ball_subset_ball (min_le_right s r)
  have hfactor : HasCornerFactor F a (F a) 1 := by
    refine ⟨t, b, ht, ⟨isOpen_ball, fun z hz => hb.2 z (hts hz)⟩,
      fun z hz => hbn z (hts hz), ?_⟩
    intro z hz
    have hwslit : z - (a : ℂ) ∈ PrincipalSlitPlane :=
      (PrincipalLogarithm.mem_principalSlitPlane_iff _).mpr
        (Or.inr (by simpa using ne_of_gt hz.2))
    have hpower : upperPower 1 a z = z - (a : ℂ) := by
      change E (1 * PrincipalLog (z - (a : ℂ))) = _
      rw [one_mul, PrincipalLogarithm.E_principalLog _ hwslit]
    rw [hpower, ← hfac z (hts hz.1), hagree ⟨htr hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩]
  exact ⟨hfactor, logDeriv_of_cornerFactor F a (F a) 1 one_ne_zero hfactor⟩

/-- The closure of a geometric wedge has closed polar coordinates.  The
radial parameter is controlled by the distance to the vertex, so a compact
rectangle suffices even though the whole wedge is unbounded. -/
theorem wedge_closure_polar {v c w : ℂ} {α : ℝ} (hc : ‖c‖ = 1)
    (hw : w ∈ closure (wedge v c α)) :
    ∃ ρ θ : ℝ, 0 ≤ ρ ∧ 0 ≤ θ ∧ θ ≤ Real.pi * α ∧
      w = v + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by
  let B := ‖w - v‖ + 1
  let K : Set (ℝ × ℝ) := Icc 0 B ×ˢ Icc 0 (Real.pi * α)
  let f : ℝ × ℝ → ℂ := fun p => v + c * ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))
  have hf : Continuous f := by fun_prop
  have hK : IsClosed (f '' K) := ((isCompact_Icc.prod isCompact_Icc).image hf).isClosed
  have hwB : w ∈ ball v B := by simp [mem_ball, dist_eq_norm, B]
  have hcl : w ∈ closure (wedge v c α ∩ ball v B) := by
    apply _root_.mem_closure_iff.mpr
    intro U hU hwU
    obtain ⟨z, hz, hzW⟩ := _root_.mem_closure_iff.mp hw (U ∩ ball v B)
      (hU.inter isOpen_ball) ⟨hwU, hwB⟩
    exact ⟨z, hz.1, hzW, hz.2⟩
  have hsub : wedge v c α ∩ ball v B ⊆ f '' K := by
    rintro z ⟨⟨ρ, θ, hρ, hθ, hθα, rfl⟩, hzB⟩
    have hn : ‖v + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) - v‖ = ρ := by
      simp [hc, norm_exp_ofReal_mul_I, abs_of_pos hρ]
    have hρB : ρ ≤ B := by
      have := hzB
      rw [mem_ball, dist_eq_norm, hn] at this
      exact this.le
    exact ⟨(ρ, θ), ⟨⟨hρ.le, hρB⟩, hθ.le, hθα.le⟩, rfl⟩
  obtain ⟨⟨ρ, θ⟩, hρθ, heq⟩ := hK.closure_subset (closure_mono hsub hcl)
  exact ⟨ρ, θ, hρθ.1.1, hρθ.2.1, hρθ.2.2, heq.symm⟩

/-- Rotate the logarithm cut away from both edges before taking the root.
The value at the vertex is the continuous zero value of complex `cpow`. -/
def wedgeStraightening (α : ℝ) (w : ℂ) : ℂ :=
  exp (((Real.pi / 2 : ℝ) : ℂ) * I) *
    (exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) * w) ^ (α : ℂ)⁻¹


@[simp] theorem wedgeStraightening_zero (α : ℝ) (hα : α ≠ 0) :
    wedgeStraightening α 0 = 0 := by
  simp [wedgeStraightening, zero_cpow (inv_ne_zero (ofReal_ne_zero.mpr hα))]

/-- On a closed angular interval of width less than two pi, the rotated
root has the literal angle θ/α. This calculation fixes all branch choices. -/
theorem wedgeStraightening_polar {α ρ θ : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α) :
    wedgeStraightening α ((ρ : ℂ) * exp ((θ : ℂ) * I)) =
      exp (((Real.log ρ / α : ℝ) : ℂ) + ((θ / α : ℝ) : ℂ) * I) := by
  have hα0 : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  have hrot : exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) *
      ((ρ : ℂ) * exp ((θ : ℂ) * I)) =
      exp ((Real.log ρ : ℂ) + ((θ - Real.pi * α / 2 : ℝ) : ℂ) * I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hρ]
    rw [ofReal_sub, sub_mul, exp_sub]
    rw [exp_neg]
    ring
  have hlo : -Real.pi < θ - Real.pi * α / 2 := by
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_left hα2 Real.pi_pos]
  have hhi : θ - Real.pi * α / 2 < Real.pi := by
    nlinarith [Real.pi_pos, mul_lt_mul_of_pos_left hα2 Real.pi_pos]
  unfold wedgeStraightening
  rw [hrot, cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by simpa using hlo) (by simpa using hhi.le)]
  rw [← exp_add]
  congr 1
  push_cast
  field_simp
  ring


private theorem rotated_polar_exp {α ρ θ : ℝ} (hρ : 0 < ρ) :
    exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) *
      ((ρ : ℂ) * exp ((θ : ℂ) * I)) =
      exp ((Real.log ρ : ℂ) + ((θ - Real.pi * α / 2 : ℝ) : ℂ) * I) := by
  rw [exp_add, ← ofReal_exp, Real.exp_log hρ]
  rw [ofReal_sub, sub_mul, exp_sub, exp_neg]
  ring

private theorem rotated_polar_slit {α ρ θ : ℝ} (hα2 : α < 2)
    (hρ : 0 < ρ) (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α) :
    exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) *
      ((ρ : ℂ) * exp ((θ : ℂ) * I)) ∈ slitPlane := by
  rw [rotated_polar_exp hρ]
  apply expOpenPartialHomeomorph.map_source
  change -Real.pi < _ ∧ _ < Real.pi
  simp only [add_im, ofReal_im, mul_im, I_im, ofReal_re,
    mul_one, I_re, mul_zero, add_zero, zero_add]
  constructor <;> nlinarith [Real.pi_pos, mul_lt_mul_of_pos_left hα2 Real.pi_pos]

/-- The fractional root maps every interior polar point to the upper half-plane. -/
theorem wedgeStraightening_im_pos {α ρ θ : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθα : θ < Real.pi * α) :
    0 < (wedgeStraightening α ((ρ : ℂ) * exp ((θ : ℂ) * I))).im := by
  rw [wedgeStraightening_polar hα hα2 hρ hθ.le hθα.le]
  simp only [exp_im, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero,
    I_im, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
    (div_pos hθ hα) ((div_lt_iff₀ hα).mpr hθα))

/-- The upper principal power is a left inverse on the entire closed sector,
using the continuous zero value for the power at the vertex. -/
theorem wedgeStraightening_cpow {α ρ θ : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α) :
    (wedgeStraightening α ((ρ : ℂ) * exp ((θ : ℂ) * I))) ^ (α : ℂ) =
      (ρ : ℂ) * exp ((θ : ℂ) * I) := by
  have hα0 : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
  rcases hρ.eq_or_lt with hρ | hρ
  · subst ρ
    simp [wedgeStraightening_zero α hα.ne', zero_cpow hα0]
  rw [wedgeStraightening_polar hα hα2 hρ hθ hθα,
    cpow_def_of_ne_zero (exp_ne_zero _)]
  rw [log_exp (by simpa using (lt_of_lt_of_le (neg_neg_of_pos Real.pi_pos)
    (div_nonneg hθ hα.le))) (by simpa using (div_le_iff₀ hα).mpr hθα)]
  have hexp : (((Real.log ρ / α : ℝ) : ℂ) + ((θ / α : ℝ) : ℂ) * I) * (α : ℂ) =
      (Real.log ρ : ℂ) + (θ : ℂ) * I := by
    push_cast
    field_simp
  rw [hexp, exp_add, ← ofReal_exp, Real.exp_log hρ]

/-- The rotated root is continuous at both edges and at the vertex. -/
theorem continuousAt_wedgeStraightening_polar {α ρ θ : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hρ : 0 ≤ ρ)
    (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α) :
    ContinuousAt (wedgeStraightening α) ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by
  have hc : ContinuousAt (fun w : ℂ => exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) * w)
      ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by fun_prop
  have hpow : ContinuousAt (fun w : ℂ => w ^ (α : ℂ)⁻¹)
      (exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I)) * ((ρ : ℂ) * exp ((θ : ℂ) * I))) := by
    rcases hρ.eq_or_lt with hρ | hρ
    · subst ρ
      simp only [ofReal_zero, zero_mul, mul_zero]
      apply continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
      simpa [← ofReal_inv] using inv_pos.mpr hα
    · exact continuousAt_cpow_const (rotated_polar_slit hα2 hρ hθ hθα)
  exact (hpow.comp hc).const_mul _


/-- The root is holomorphic and noncritical off the vertex on the geometric
sector; its derivative is obtained on the actual rotated slit plane. -/
theorem wedgeStraightening_differentiable_noncritical {α ρ θ : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hρ : 0 < ρ)
    (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α) :
    DifferentiableAt ℂ (wedgeStraightening α) ((ρ : ℂ) * exp ((θ : ℂ) * I)) ∧
      deriv (wedgeStraightening α) ((ρ : ℂ) * exp ((θ : ℂ) * I)) ≠ 0 := by
  let k : ℂ := exp (-(((Real.pi * α / 2 : ℝ) : ℂ) * I))
  let w : ℂ := (ρ : ℂ) * exp ((θ : ℂ) * I)
  have hslit : k * w ∈ slitPlane := rotated_polar_slit hα2 hρ hθ hθα
  have hd := (((hasDerivAt_id w).const_mul k).cpow_const (c := (α : ℂ)⁻¹)
    hslit).const_mul (exp (((Real.pi / 2 : ℝ) : ℂ) * I))
  change HasDerivAt (wedgeStraightening α) _ w at hd
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  exact mul_ne_zero (exp_ne_zero _) (mul_ne_zero
    (mul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr hα.ne'))
      (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero hslit))))
    (mul_ne_zero (exp_ne_zero _) one_ne_zero))

/-- An interior point of a geometric corner's closure has a closed polar
representation; the localization disk is retained when taking closures. -/
theorem corner_closure_polar {P : Set ℂ} {v c w : ℂ} {α R : ℝ}
    (hc : ‖c‖ = 1) (hgeom : P ∩ ball v R = wedge v c α ∩ ball v R)
    (hw : w ∈ closure P) (hwR : w ∈ ball v R) :
    ∃ ρ θ : ℝ, 0 ≤ ρ ∧ 0 ≤ θ ∧ θ ≤ Real.pi * α ∧
      w = v + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by
  apply wedge_closure_polar hc
  apply _root_.mem_closure_iff.mpr
  intro U hU hwU
  obtain ⟨z, hz, hzP⟩ := _root_.mem_closure_iff.mp hw (U ∩ ball v R)
    (hU.inter isOpen_ball) ⟨hwU, hwR⟩
  exact ⟨z, hz.1, (hgeom ▸ (show z ∈ P ∩ ball v R from ⟨hzP, hz.2⟩)).1⟩


/-- Both closed sector edges are taken to the real axis. -/
theorem wedgeStraightening_edge_real {α ρ θ : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (hθα : θ ≤ Real.pi * α)
    (hedge : ρ = 0 ∨ θ = 0 ∨ θ = Real.pi * α) :
    (wedgeStraightening α ((ρ : ℂ) * exp ((θ : ℂ) * I))).im = 0 := by
  rcases hedge with rfl | rfl | rfl
  · simp [wedgeStraightening_zero α hα.ne']
  all_goals
    rcases hρ.eq_or_lt with hρ | hρ
    · subst ρ; simp [wedgeStraightening_zero α hα.ne']
    · rw [wedgeStraightening_polar hα hα2 hρ hθ hθα]
      simp [exp_im, hα.ne']

/-- The original geometric and boundary hypotheses produce the fractional
straightening on an upper half-disk. Reflection, the simple zero, the
holomorphic unit and the logarithmic derivative are then proved by the
analytic lemmas above. -/
theorem polygon_vertex : Specs.D12Complex.Ch12.PolygonVertex.polygon_vertex_type := by
  intro P F G _ _ hp he a α hα hα2 hcorner
  obtain ⟨c, R, hc, hR, hgeom⟩ := hcorner
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  obtain ⟨hcont, hi, hmap⟩ := boundary_extension_data he
  have haC : (a : ℂ) ∈ closedHalfPlane := by simp [closedHalfPlane]
  have hpre : F ⁻¹' ball (F a) R ∈ 𝓝[closedHalfPlane] (a : ℂ) :=
    (hcont a haC).preimage_mem_nhdsWithin (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨r, hr, hval⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let n : ℂ → ℂ := fun z => (F z - F a) / c
  let q : ℂ → ℂ := fun z => wedgeStraightening α (n z)
  have hnormalize : ∀ (z : ℂ) (ρ θ : ℝ),
      F z = F a + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) →
      n z = (ρ : ℂ) * exp ((θ : ℂ) * I) := by
    intro z ρ θ hz
    dsimp [n]
    rw [hz]
    field_simp
    ring
  have hpolC : ∀ z ∈ Reflection.upperClosure (a : ℂ) r,
      ∃ ρ θ : ℝ, 0 ≤ ρ ∧ 0 ≤ θ ∧ θ ≤ Real.pi * α ∧
        F z = F a + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by
    intro z hz
    exact corner_closure_polar hc hgeom (hmap hz.2) (hval hz)
  have hpolU : ∀ z ∈ Reflection.upper (a : ℂ) r,
      ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < Real.pi * α ∧
        F z = F a + c * ((ρ : ℂ) * exp ((θ : ℂ) * I)) := by
    intro z hz
    exact (hgeom ▸ (show F z ∈ P ∩ ball (F a) R from
      ⟨hp.2.2.1 hz.2, hval ⟨hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩⟩)).1
  have hn : ∀ z ∈ Reflection.upper (a : ℂ) r, DifferentiableAt ℂ n z := by
    intro z hz
    exact ((hp.1.2 z hz.2).sub_const (F a)).div_const c
  have hqh : HolomorphicOn (Reflection.upper (a : ℂ) r) q := by
    refine ⟨isOpen_ball.inter (isOpen_lt continuous_const continuous_im), ?_⟩
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolU z hz
    have hd := (wedgeStraightening_differentiable_noncritical hα hα2 hρ hθ.le hθα.le).1
    rw [← hnormalize z ρ θ hzF] at hd
    exact hd.comp z (hn z hz)
  have hnc : ContinuousOn n (Reflection.upperClosure (a : ℂ) r) :=
    ((hcont.mono (fun z (hz : z ∈ Reflection.upperClosure (a : ℂ) r) => hz.2)).sub
      continuousOn_const).div_const c
  have hqc : ContinuousOn q (Reflection.upperClosure (a : ℂ) r) := by
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolC z hz
    have hd := continuousAt_wedgeStraightening_polar hα hα2 hρ hθ hθα
    rw [← hnormalize z ρ θ hzF] at hd
    exact hd.comp_continuousWithinAt (hnc z hz)
  have hreal : ∀ z ∈ Reflection.diameter (a : ℂ) r, (q z).im = 0 := by
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolC z ⟨hz.1, le_of_eq hz.2.symm⟩
    have hnot : F z ∉ P := by
      have hf := boundary_real_frontier hp he hz.2
      rw [hp.2.1.1.frontier_eq] at hf
      exact hf.2
    have hedge : ρ = 0 ∨ θ = 0 ∨ θ = Real.pi * α := by
      by_contra h
      push Not at h
      have hw : F z ∈ wedge (F a) c α :=
        ⟨ρ, θ, lt_of_le_of_ne hρ (Ne.symm h.1),
          lt_of_le_of_ne hθ (Ne.symm h.2.1), lt_of_le_of_ne hθα h.2.2, hzF⟩
      exact hnot ((hgeom.symm ▸ (show F z ∈ wedge (F a) c α ∩ ball (F a) R from
        ⟨hw, hval ⟨hz.1, le_of_eq hz.2.symm⟩⟩)).1)
    change (wedgeStraightening α (n z)).im = 0
    rw [hnormalize z ρ θ hzF]
    exact wedgeStraightening_edge_real hα hα2 hρ hθ hθα hedge
  have hinverse : ∀ z ∈ Reflection.upperClosure (a : ℂ) r,
      q z ^ (α : ℂ) = n z := by
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolC z hz
    change (wedgeStraightening α (n z)) ^ (α : ℂ) = n z
    rw [hnormalize z ρ θ hzF]
    exact wedgeStraightening_cpow hα hα2 hρ hθ hθα
  have hqi : InjOn q (Reflection.upperClosure (a : ℂ) r) := by
    intro z hz w hw hqw
    apply hi hz.2 hw.2
    have hne : n z = n w := by rw [← hinverse z hz, ← hinverse w hw, hqw]
    exact sub_left_injective ((div_left_inj' hc0).mp hne)
  have hqnc : ∀ z ∈ Reflection.upper (a : ℂ) r, deriv q z ≠ 0 := by
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolU z hz
    have hd := wedgeStraightening_differentiable_noncritical hα hα2 hρ hθ.le hθα.le
    rw [← hnormalize z ρ θ hzF] at hd
    have hdn : HasDerivAt n (deriv F z / c) z :=
      ((hp.1.2 z hz.2).hasDerivAt.sub_const (F a)).div_const c
    have hdq : HasDerivAt q (deriv (wedgeStraightening α) (n z) * (deriv F z / c)) z :=
      hd.1.hasDerivAt.comp z hdn
    rw [hdq.deriv]
    exact mul_ne_zero hd.2 (div_ne_zero
      (AnalyticArcs.biholomorphic_deriv_ne_zero hp hz.2).1 hc0)
  have hpos : ∀ z ∈ Reflection.upper (a : ℂ) r, 0 < (q z).im := by
    intro z hz
    obtain ⟨ρ, θ, hρ, hθ, hθα, hzF⟩ := hpolU z hz
    change 0 < (wedgeStraightening α (n z)).im
    rw [hnormalize z ρ θ hzF]
    exact wedgeStraightening_im_pos hα hα2 hρ hθ hθα
  have hzero : q a = 0 := by simp [q, n, wedgeStraightening_zero α hα.ne']
  have hF : ∀ z ∈ Reflection.upper (a : ℂ) r,
      F z - F a = c * principalPower (α : ℂ) (q z) := by
    intro z hz
    have hq0 : q z ≠ 0 := by
      intro h
      have := hpos z hz
      simp [h] at this
    have hpower : principalPower (α : ℂ) (q z) = q z ^ (α : ℂ) := by
      rw [cpow_def_of_ne_zero hq0]
      change E ((α : ℂ) * PrincipalLog (q z)) = exp (log (q z) * (α : ℂ))
      rw [Exponential.E_eq_exp]
      congr 1
      exact mul_comm _ _
    rw [hpower, hinverse z ⟨hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩]
    dsimp [n]
    field_simp
  have hfac := corner_factor_of_straightening F q a (F a) c (α : ℂ) r hr hc0
    hqh hqc hreal hqi hqnc hpos hzero hF
  exact ⟨hfac, logDeriv_of_cornerFactor F a (F a) (α : ℂ)
    (ofReal_ne_zero.mpr hα.ne') hfac⟩

end D12Complex.PolygonVertex
