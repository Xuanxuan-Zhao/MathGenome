import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MoserMembership
import MathGenome.Internal.FourierSobolev.P102.Sobolev.TrudingerMoserBound
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Construction tools for the source Moser profiles. No pending profile or
parent implementation is imported. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology Pointwise ContDiff

namespace P102.Sobolev.MoserMembership
open P102.U4 TrudingerMoser

/-- A whole-space Sobolev function supported in a compact subset of an open
set restricts to the actual closure of smooth compactly supported tests there.
The proof uses support-controlled mollification in the full derivative norm. -/
theorem sobolevRestrict_mem_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (Ω : Opens (Space d)) (u : Sobolev (d := d) 𝕜 ⊤ m p)
    (K : Compacts (Space d)) (hKΩ : (K : Set (Space d)) ⊆ Ω)
    (hK : ∀ᵐ x ∂volume, x ∉ K → sobolevUnderlying u x = 0) :
    sobolevRestrict Ω u ∈ sobolevZeroSubmodule 𝕜 Ω m p := by
  change sobolevRestrict Ω u ∈ closure
    (smoothSobolevSubmodule 𝕜 Ω m p : Set (Sobolev 𝕜 Ω m p))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, _, hsub⟩ := exists_supportRadius K hKΩ (r := 1) zero_lt_one
  obtain ⟨φ, v, hv, herr, hs⟩ := exists_mollified_approximation hp u K hK hδ hε
  let ψ : TestSpace 𝕜 Ω := ⟨φ, φ.contDiff, φ.hasCompactSupport, hs.trans hsub⟩
  refine ⟨sobolevRestrict Ω v, ?_, ?_⟩
  · change sobolevUnderlying (sobolevRestrict Ω v) ∈ LinearMap.range (testToDomainLp Ω p)
    refine ⟨ψ, ?_⟩
    apply Lp.ext
    have hrep := hv (zeroSobolevIndex d m)
    simp only [zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord] at hrep
    have hr : (sobolevUnderlying (sobolevRestrict Ω v) : Space d → 𝕜)
        =ᵐ[volume.restrict (Ω : Set (Space d))] ψ :=
      (domainLpRestrict_ae Ω (sobolevUnderlying v)).trans (ae_restrict_of_ae hrep)
    exact (ψ.continuous.memLp_of_hasCompactSupport (p := p) ψ.hasCompactSupport).coeFn_toLp.trans hr.symm
  · rw [dist_comm, dist_eq_norm]
    calc
      ‖sobolevRestrict Ω v - sobolevRestrict Ω u‖ =
          ‖sobolevRestrict Ω (v - u)‖ := by
        exact congrArg norm ((sobolevRestrictCLM Ω).map_sub v u).symm
      _ ≤ ‖v - u‖ := sobolevRestrict_norm_le Ω _
      _ < ε := herr

/-- Compactly supported Lipschitz functions have genuine distributional
Sobolev coordinates, represented by their a.e. Fréchet derivatives. -/
theorem exists_sobolev_of_lipschitz_compactSupport {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Space d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (hcomp : HasCompactSupport f) :
    ∃ u : Sobolev (d := d) ℝ ⊤ 1 p,
      (sobolevUnderlying u : Space d → ℝ) =ᵐ[volume] f ∧
      ∀ j : Fin d, (Truncations.sobolevFirstDerivative u j : Space d → ℝ)
        =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector d j)) := by
  let Ω : Opens (Space d) := ⊤
  have hfm : MemLp f p (volume.restrict (Ω : Set (Space d))) := by
    simpa [Ω] using hf.continuous.memLp_of_hasCompactSupport (p := p) hcomp
  have hgm (j : Fin d) : MemLp (fun x => fderiv ℝ f x (coordinateVector d j)) p
      (volume.restrict (Ω : Set (Space d))) := by
    apply (hcomp.fderiv_apply (𝕜 := ℝ) (coordinateVector d j)).memLp_of_bound
      (((ContinuousLinearMap.apply ℝ ℝ (coordinateVector d j)).continuous.measurable.comp
        (measurable_fderiv ℝ f)).aestronglyMeasurable) C
    filter_upwards [] with x
    calc
      ‖fderiv ℝ f x (coordinateVector d j)‖ ≤
          ‖fderiv ℝ f x‖ * ‖coordinateVector d j‖ :=
        (fderiv ℝ f x).le_opNorm _
      _ ≤ C := by
        have hn : ‖coordinateVector d j‖ = 1 := by
          simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
            PiLp.norm_single]
        rw [hn, mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ hf
  let a : DomainLp ℝ Ω p := hfm.toLp f
  let g (j : Fin d) : DomainLp ℝ Ω p := (hgm j).toLp _
  have hweak (j : Fin d) : distributionPartial {j} (regularDistribution Ω a) =
      regularDistribution Ω (g j) := by
    apply acl_converse d (Truncations.dimension_pos j) ℝ Ω j a (g j)
      (domainLp_locallyIntegrable Ω p _) (domainLp_locallyIntegrable Ω p _)
    refine ⟨f, hfm.coeFn_toLp, ?_⟩
    have hd : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), DifferentiableAt ℝ f x := by
      simpa [Ω] using hf.ae_differentiableAt
    filter_upwards [ACL.ae_on_fibers j hd,
      ACL.ae_on_fibers j (hgm j).coeFn_toLp] with z hz hgz
    refine ⟨?_, ?_⟩
    · intro a b _hab
      exact ((hf.comp (acl_line_lipschitz j z)).lipschitzOnWith).absolutelyContinuousOnInterval
    · filter_upwards [hz, hgz] with t ht hgt
      change HasDerivAt (fun s => f (ACL.line j z s)) (g j (ACL.line j z t)) t
      rw [show g j (ACL.line j z t) =
        fderiv ℝ f (ACL.line j z t) (coordinateVector d j) from hgt]
      exact ht.hasFDerivAt.comp_hasDerivAt t (acl_line_hasDerivAt j z t)
  obtain ⟨u, hu, hdu⟩ := Truncations.exists_sobolev_of_coordinates a g hweak
  refine ⟨u, ?_, fun j => ?_⟩
  · simpa only [hu, a, Ω, Opens.coe_top, Measure.restrict_univ] using hfm.coeFn_toLp
  · simpa only [hdu, g, Ω, Opens.coe_top, Measure.restrict_univ] using (hgm j).coeFn_toLp


/-- The inner radius has logarithmic length exactly L/d. -/
lemma log_inner_radius {d : ℕ} {R : ℝ} (hR : 0 < R) (L : ℝ) :
    Real.log (logarithmicRadius d R L) = Real.log R - L / d := by
  rw [logarithmicRadius, Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

lemma profile_on_core {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hx : ‖x - c‖ ≤ logarithmicRadius d R L) :
    moserFunction c R L x = moserHeight d L := by
  by_cases hxc : x = c
  · simp [moserFunction, hxc]
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog : L / d ≤ Real.log (R / ‖x - c‖) := by
    rw [Real.log_div hR.ne' hn.ne', ← sub_le_sub_iff_left (Real.log R),
      sub_sub_cancel]
    exact Real.log_le_log hn hx |>.trans_eq (log_inner_radius hR L)
  have hcut : 1 ≤ (d : ℝ) * Real.log (R / ‖x - c‖) / L := by
    apply (le_div_iff₀ hL).mpr
    have := (div_le_iff₀ hd0).mp hlog
    nlinarith
  simp only [moserFunction, ite_eq_right hxc]
  rw [min_eq_left (hcut.trans (le_max_right _ _)), mul_one]

lemma profile_zero_outside {d : ℕ} (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hx : R ≤ ‖x - c‖) : moserFunction c R L x = 0 := by
  have hn : 0 < ‖x - c‖ := hR.trans_le hx
  have hxc : x ≠ c := sub_ne_zero.mp (norm_ne_zero_iff.mp hn.ne')
  have hlog : Real.log (R / ‖x - c‖) ≤ 0 :=
    Real.log_nonpos (div_nonneg hR.le hn.le) ((div_le_one hn).mpr hx)
  have hcut : (d : ℝ) * Real.log (R / ‖x - c‖) / L ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hlog) hL.le
  simp [moserFunction, hxc, max_eq_left hcut]

/-- An expression with the radius clipped away from zero. This identity also
checks the values on both joining spheres and at the center. -/
lemma profile_eq_clipped_log {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) (x : Space d) :
    moserFunction c R L x = (moserHeight d L * d / L) *
      (Real.log R - Real.log (max (logarithmicRadius d R L) (min R ‖x - c‖))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hρR := logarithmicRadius_lt (by omega : 0 < d) hR hL
  have hρ := logarithmicRadius_pos (d := d) hR L
  by_cases hcore : ‖x - c‖ ≤ logarithmicRadius d R L
  · rw [profile_on_core hd c hR hL hcore,
      min_eq_right (hcore.trans hρR.le), max_eq_left hcore, log_inner_radius hR L]
    field_simp
    ring
  by_cases hout : R ≤ ‖x - c‖
  · rw [profile_zero_outside c hR hL hout, min_eq_left hout, max_eq_right hρR.le]
    ring
  have hr : 0 < ‖x - c‖ := hρ.trans (lt_of_not_ge hcore)
  have hxc : x ≠ c := sub_ne_zero.mp (norm_ne_zero_iff.mp hr.ne')
  have hl0 : 0 ≤ Real.log (R / ‖x - c‖) :=
    Real.log_nonneg ((one_le_div hr).mpr (le_of_not_ge hout))
  have hl1 : Real.log (R / ‖x - c‖) ≤ L / d := by
    rw [Real.log_div hR.ne' hr.ne']
    have hh := Real.log_le_log hρ (le_of_not_ge hcore)
    rw [log_inner_radius hR L] at hh
    linarith
  have ht0 : 0 ≤ (d : ℝ) * Real.log (R / ‖x - c‖) / L := by positivity
  have ht1 : (d : ℝ) * Real.log (R / ‖x - c‖) / L ≤ 1 := by
    apply (div_le_one hL).mpr
    have := (le_div_iff₀ hd0).mp hl1
    nlinarith
  rw [moserFunction, ite_eq_right hxc, max_eq_right ht0, min_eq_right ht1,
    min_eq_right (le_of_not_ge hout), max_eq_right (le_of_not_ge hcore),
    Real.log_div hR.ne' hr.ne']
  ring

/-- Logarithm is Lipschitz when its argument is bounded away from zero. -/
lemma log_lipschitz_on_Ici {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzOnWith ⟨ρ⁻¹, inv_nonneg.mpr hρ.le⟩ Real.log (Ici ρ) := by
  apply (convex_Ici ρ).lipschitzOnWith_of_nnnorm_deriv_le
  · intro r hr
    exact Real.differentiableAt_log (ne_of_gt (hρ.trans_le hr))
  · intro r hr
    rw [Real.deriv_log]
    change |r⁻¹| ≤ ρ⁻¹
    rw [abs_of_pos (inv_pos.mpr (hρ.trans_le hr))]
    exact inv_anti₀ hρ hr

/-- Each source profile is globally Lipschitz, with a finite constant depending
on its parameters. No boundary property of the ambient domain enters. -/
theorem profile_lipschitz {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ∃ C : ℝ≥0, LipschitzWith C (moserFunction c R L) := by
  let ρ := logarithmicRadius d R L
  have hρ : 0 < ρ := logarithmicRadius_pos hR L
  have hdist : LipschitzWith 1 (fun x : Space d => ‖x - c‖) := by
    simpa only [dist_eq_norm] using (LipschitzWith.dist_left c)
  have hclip : LipschitzWith 1 (fun x : Space d => max ρ (min R ‖x - c‖)) :=
    (hdist.const_min R).const_max ρ
  have hlog := lipschitzOnWith_univ.mp ((log_lipschitz_on_Ici hρ).comp
    (s := univ) hclip.lipschitzOnWith (fun x _ => le_max_left ρ _))
  have hlin := ((moserHeight d L * d / L) • ContinuousLinearMap.id ℝ ℝ).lipschitzWith
  have hlip := hlin.comp ((LipschitzWith.const (Real.log R)).sub hlog)
  have he : moserFunction c R L =
      ((moserHeight d L * d / L) • ContinuousLinearMap.id ℝ ℝ) ∘
        (fun x => Real.log R - Real.log (max ρ (min R ‖x - c‖))) := by
    funext x
    exact profile_eq_clipped_log hd c hR hL x
  rw [he]
  exact ⟨_, hlip⟩

/-- The closed ball contains the topological support, so the profile is
compactly supported on the whole Euclidean space. -/
theorem profile_tsupport_subset {d : ℕ} (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    tsupport (moserFunction c R L) ⊆ Metric.closedBall c R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  exact hx (profile_zero_outside c hR hL (by
    have hh : ¬ ‖x - c‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hn
    exact (lt_of_not_ge hh).le))

/-- Sobolev realization of the canonical function, without yet claiming its
energy normalization. The derivatives here are the canonical distribution
coordinates and their a.e. Fréchet descriptions, not assumed certificates. -/
theorem exists_profile_sobolevZero {d : ℕ} (hd : 2 ≤ d)
    (Ω : Opens (Space d)) (c : Space d) {R L : ℝ}
    (hR : 0 < R) (hsub : Metric.closedBall c R ⊆ (Ω : Set (Space d)))
    (hL : 0 < L) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ u : SobolevZero ℝ Ω 1 p,
      (sobolevUnderlying u.val : Space d → ℝ) =ᵐ[volume.restrict (Ω : Set (Space d))]
        moserFunction c R L ∧
      ∀ j : Fin d, (firstWeakDerivative u.val j : Space d → ℝ)
        =ᵐ[volume.restrict (Ω : Set (Space d))]
          (fun x => fderiv ℝ (moserFunction c R L) x (coordinateVector d j)) := by
  obtain ⟨C, hC⟩ := profile_lipschitz hd c hR hL
  have hsupport := profile_tsupport_subset c hR hL
  have hcomp : HasCompactSupport (moserFunction c R L) :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport _) hsupport
  obtain ⟨w, hw, hdw⟩ := exists_sobolev_of_lipschitz_compactSupport (p := p) hC hcomp
  let K : Compacts (Space d) := ⟨Metric.closedBall c R, isCompact_closedBall c R⟩
  have hK : ∀ᵐ x ∂volume, x ∉ K → sobolevUnderlying w x = 0 := by
    filter_upwards [hw] with x hx hnot
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun ht => hnot (hsupport ht))
  refine ⟨⟨sobolevRestrict Ω w, sobolevRestrict_mem_zero hp Ω w K hsub hK⟩, ?_, ?_⟩
  · exact (domainLpRestrict_ae Ω (sobolevUnderlying w)).trans (ae_restrict_of_ae hw)
  · intro j
    exact (domainLpRestrict_ae Ω (firstWeakDerivative w j)).trans (ae_restrict_of_ae (hdw j))

/-- Euclidean norm derivative after translation, away from the center. -/
lemma norm_sub_hasFDerivAt {d : ℕ} (c x : Space d) (hx : x ≠ c) :
    HasFDerivAt (fun y => ‖y - c‖)
      (‖x - c‖⁻¹ • innerSL ℝ (x - c)) x := by
  have hn : ‖x - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hs := ((hasFDerivAt_id x).sub_const c).norm_sq.sqrt (pow_ne_zero 2 hn)
  have he : (fun y : Space d => Real.sqrt (‖y - c‖ ^ 2)) = (fun y => ‖y - c‖) := by
    funext y
    exact Real.sqrt_sq (norm_nonneg _)
  simp only [id_eq] at hs
  rw [he] at hs
  convert hs using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg _)]
  field_simp
  ring

/-- Ordinary derivative on the logarithmic annulus, with the explicit radial
coefficient. The joining spheres are excluded only from this local formula. -/
lemma profile_hasFDerivAt_annulus {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hin : logarithmicRadius d R L < ‖x - c‖) (hout : ‖x - c‖ < R) :
    HasFDerivAt (moserFunction c R L)
      ((-(moserHeight d L * d / L) / ‖x - c‖ ^ 2) • innerSL ℝ (x - c)) x := by
  have hn : 0 < ‖x - c‖ := (logarithmicRadius_pos hR L).trans hin
  have hx : x ≠ c := sub_ne_zero.mp (norm_ne_zero_iff.mp hn.ne')
  have hs := (((norm_sub_hasFDerivAt c x hx).log hn.ne').const_sub
    (Real.log R)).const_mul (moserHeight d L * d / L)
  have he : moserFunction c R L =ᶠ[𝓝 x]
      (fun y => (moserHeight d L * d / L) * (Real.log R - Real.log ‖y - c‖)) := by
    have hc : Continuous (fun y : Space d => ‖y - c‖) := continuous_id.sub continuous_const |>.norm
    filter_upwards [hc.continuousAt.eventually (Ioo_mem_nhds hin hout)] with y hy
    rw [profile_eq_clipped_log hd c hR hL y, min_eq_right hy.2.le, max_eq_right hy.1.le]
  have hs' := hs.congr_of_eventuallyEq he
  convert hs' using 1
  ext v
  simp only [smul_apply, neg_apply,
    smul_eq_mul]
  field_simp

lemma profile_hasFDerivAt_core {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hx : ‖x - c‖ < logarithmicRadius d R L) :
    HasFDerivAt (moserFunction c R L) (0 : Space d →L[ℝ] ℝ) x := by
  have he : moserFunction c R L =ᶠ[𝓝 x] (fun _ => moserHeight d L) := by
    have hc : Continuous (fun y : Space d => ‖y - c‖) := (continuous_id.sub continuous_const).norm
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact profile_on_core hd c hR hL hy.le
  exact (hasFDerivAt_const (moserHeight d L) x).congr_of_eventuallyEq he

lemma profile_hasFDerivAt_exterior {d : ℕ} (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) {x : Space d}
    (hx : R < ‖x - c‖) : HasFDerivAt (moserFunction c R L) (0 : Space d →L[ℝ] ℝ) x := by
  have he : moserFunction c R L =ᶠ[𝓝 x] (fun _ => 0) := by
    have hc : Continuous (fun y : Space d => ‖y - c‖) := (continuous_id.sub continuous_const).norm
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hx)] with y hy
    exact profile_zero_outside c hR hL hy.le
  exact (hasFDerivAt_const 0 x).congr_of_eventuallyEq he

/-- The ordinary derivative has precisely the source annular formula a.e.;
only the two joining spheres are discarded. -/
lemma profile_fderiv_ae {d : ℕ} (hd : 2 ≤ d) (c : Space d)
    {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ∀ᵐ x : Space d ∂volume,
      fderiv ℝ (moserFunction c R L) x =
        if logarithmicRadius d R L < ‖x - c‖ ∧ ‖x - c‖ < R then
          (-(moserHeight d L * d / L) / ‖x - c‖ ^ 2) • innerSL ℝ (x - c)
        else 0 := by
  let : NeZero d := ⟨by omega⟩
  have hs (r : ℝ) : ∀ᵐ x : Space d ∂volume, ‖x - c‖ ≠ r := by
    have hh : ∀ᵐ x : Space d ∂volume, x ∉ Metric.sphere c r :=
      measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere (volume : Measure (Space d)) c r)
    simpa only [Metric.mem_sphere, dist_eq_norm] using hh
  filter_upwards [hs (logarithmicRadius d R L), hs R] with x hinner houter
  by_cases hin : logarithmicRadius d R L < ‖x - c‖
  · by_cases hout : ‖x - c‖ < R
    · rw [ite_eq_left ⟨hin, hout⟩]
      exact (profile_hasFDerivAt_annulus hd c hR hL hin hout).fderiv
    · rw [ite_eq_right (by simp [hout])]
      exact (profile_hasFDerivAt_exterior c hR hL (lt_of_le_of_ne (le_of_not_gt hout) houter.symm)).fderiv
  · rw [ite_eq_right (by simp [hin])]
    exact (profile_hasFDerivAt_core hd c hR hL (lt_of_le_of_ne (le_of_not_gt hin) hinner)).fderiv

/-- For the actual Sobolev realization the Euclidean weak gradient has size
h*d/(L*r) on the annulus and zero elsewhere. -/
theorem profile_weakGradient_norm {d : ℕ} (hd : 2 ≤ d)
    (Ω : Opens (Space d)) (c : Space d) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev ℝ Ω 1 p)
    (hdu : ∀ j : Fin d, (firstWeakDerivative u j : Space d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => fderiv ℝ (moserFunction c R L) x (coordinateVector d j))) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), ‖weakGradient u x‖ =
      if logarithmicRadius d R L < ‖x - c‖ ∧ ‖x - c‖ < R then
        (moserHeight d L * d / L) / ‖x - c‖ else 0 := by
  filter_upwards [ae_all_iff.mpr hdu, ae_restrict_of_ae (profile_fderiv_ae hd c hR hL)] with x hx hfx
  by_cases ha : logarithmicRadius d R L < ‖x - c‖ ∧ ‖x - c‖ < R
  · have hn : 0 < ‖x - c‖ := (logarithmicRadius_pos hR L).trans ha.1
    have hg : weakGradient u x = (-(moserHeight d L * d / L) / ‖x - c‖ ^ 2) • (x - c) := by
      apply PiLp.ext
      intro j
      change firstWeakDerivative u j x = _
      rw [hx j, hfx, ite_eq_left ha]
      simp [coordinateVector, EuclideanSpace.inner_single_right]
    have hA : 0 ≤ moserHeight d L * d / L := by
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hL.le (sharpCoefficient_pos hd).le) _) (Nat.cast_nonneg _)) hL.le
    rw [hg, norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hA,
      abs_of_nonneg (sq_nonneg _), ite_eq_left ha]
    field_simp
  · have hg : weakGradient u x = 0 := by
      apply PiLp.ext
      intro j
      change firstWeakDerivative u j x = 0
      rw [hx j, hfx, ite_eq_right ha]
      rfl
    rw [hg, norm_zero, ite_eq_right ha]

/-- The radial annular energy, including translation of the center. -/
lemma annular_energy {d : ℕ} (hd : 0 < d) (c : Space d)
    {ρ R A : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hA : 0 ≤ A) :
    (∫⁻ x : Space d, ENNReal.ofReal
      ((if ρ < ‖x - c‖ ∧ ‖x - c‖ < R then A / ‖x - c‖ else 0) ^ d)) =
      ENNReal.ofReal (sphereArea d * A ^ d * Real.log (R / ρ)) := by
  let F : ℝ → ℝ≥0∞ := (Ioo ρ R).indicator (fun r => ENNReal.ofReal ((A / r) ^ d))
  have hF : Measurable F := by
    exact Measurable.indicator (by fun_prop) measurableSet_Ioo
  have he (x : Space d) : ENNReal.ofReal
      ((if ρ < ‖x - c‖ ∧ ‖x - c‖ < R then A / ‖x - c‖ else 0) ^ d) = F ‖x - c‖ := by
    by_cases ha : ρ < ‖x - c‖ ∧ ‖x - c‖ < R
    · simp [F, ha]
    · simp [F, ha, Nat.ne_of_gt hd]
  simp_rw [he]
  rw [lintegral_sub_right_eq_self (fun x : Space d => F ‖x‖) c, radial_lintegral hd F hF]
  have hg : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (d - 1)) * F r) =
      ENNReal.ofReal (A ^ d) * ∫⁻ r in Ioo ρ R, ENNReal.ofReal r⁻¹ := by
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), (Ioo ρ R).indicator
          (fun r => ENNReal.ofReal (A ^ d) * ENNReal.ofReal r⁻¹) r := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        by_cases ha : r ∈ Ioo ρ R
        · simp only [F, Set.indicator_of_mem ha]
          rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _),
            ← ENNReal.ofReal_mul (pow_nonneg hA _)]
          congr 1
          have hp : r ^ d = r ^ (d - 1) * r := by
            rw [← pow_succ]
            congr 1
            omega
          rw [div_pow, hp]
          have hr0 : 0 < r := hr
          field_simp [hr0.ne']
        · simp [F, Set.indicator_of_notMem ha]
      _ = ∫⁻ r in Ioo ρ R, ENNReal.ofReal (A ^ d) * ENNReal.ofReal r⁻¹ := by
        rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
          Set.inter_eq_left.mpr (show Ioo ρ R ⊆ Ioi (0 : ℝ) from fun r hr => hρ.trans hr.1)]
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hg]
  have hi : IntegrableOn (fun r : ℝ => r⁻¹) (Ioo ρ R) := by
    apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
    exact (continuousOn_id.inv₀ (fun r hr => (hρ.trans_le hr.1).ne')).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo ρ R)] (fun r : ℝ => r⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact inv_nonneg.mpr (hρ.trans hr.1).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  have hI : (∫ r : ℝ in Ioo ρ R, r⁻¹) = Real.log (R / ρ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hρR.le, integral_inv_of_pos hρ (hρ.trans hρR)]
  rw [hI, ← mul_assoc, ← ENNReal.ofReal_mul (sphereArea_pos hd).le,
    ← ENNReal.ofReal_mul (mul_nonneg (sphereArea_pos hd).le (pow_nonneg hA _))]

/-- The canonical height agrees with the w_L normalization in the source. -/
lemma height_source_coordinates {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 0 ≤ L) :
    moserHeight d L = L ^ (((d : ℝ) - 1) / d) / profileScale d := by
  have hk : 1 / criticalPower d = ((d : ℝ) - 1) / d := by
    simp [criticalPower, one_div, inv_div]
  unfold moserHeight
  rw [Real.div_rpow hL (sharpCoefficient_pos hd).le]
  congr 1
  · rw [hk]
  · rw [← profileScale_criticalPower hd, one_div,
      Real.rpow_rpow_inv (profileScale_pos hd).le (criticalPower_pos hd).ne']

/-- Exact scalar energy identity, with the accepted Euclidean sphere area. -/
lemma profile_energy_scalar {d : ℕ} (hd : 2 ≤ d) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    sphereArea d * (moserHeight d L * d / L) ^ d *
      Real.log (R / logarithmicRadius d R L) = 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs0 := sphereArea_pos (d := d) (by omega)
  have hheight : moserHeight d L ^ d = L ^ (d - 1) /
      (sphereArea d * (d : ℝ) ^ (d - 1)) := by
    rw [height_source_coordinates hd hL.le, div_pow,
      ← Real.rpow_mul_natCast hL.le, profileScale_pow hd]
    have he : (((d : ℝ) - 1) / d) * d = ((d - 1 : ℕ) : ℝ) := by
      rw [div_mul_cancel₀ _ hd0.ne', Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [he, Real.rpow_natCast]
  have hlog : Real.log (R / logarithmicRadius d R L) = L / d := by
    rw [Real.log_div hR.ne' (logarithmicRadius_pos hR L).ne', log_inner_radius hR L]
    ring
  have hdPow : (d : ℝ) ^ d = (d : ℝ) ^ (d - 1) * d := by
    rw [← pow_succ]
    congr 1
    omega
  have hLPow : L ^ d = L ^ (d - 1) * L := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hlog, div_pow, mul_pow, hheight, hdPow, hLPow]
  field_simp

end P102.Sobolev.MoserMembership

namespace P102.Sobolev
open P102.U4 TrudingerMoser MoserMembership

/-- The source profiles belong to the actual zero-boundary Sobolev space
and have Euclidean weak-gradient norm exactly one. -/
theorem moser_profiles_membership :
    MoserMembershipExpected.ProfileMembership := by
  intro d hd
  let : Fact (1 ≤ (d : ℝ≥0∞)) :=
    ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
  intro Ω c R hR hsub L hL
  have hdpos : 0 < d := by omega
  obtain ⟨u, hu, hdu⟩ := exists_profile_sobolevZero hd Ω c hR hsub hL
    (p := (d : ℝ≥0∞)) (by simp)
  refine ⟨u, hu, ?_⟩
  have hg := profile_weakGradient_norm hd Ω c hR hL u.val hdu
  let G : Space d → ℝ≥0∞ := fun x => ENNReal.ofReal
    ((if logarithmicRadius d R L < ‖x - c‖ ∧ ‖x - c‖ < R then
      (moserHeight d L * d / L) / ‖x - c‖ else 0) ^ d)
  have hsupp : Function.support G ⊆ (Ω : Set (Space d)) := by
    intro x hx
    by_cases ha : logarithmicRadius d R L < ‖x - c‖ ∧ ‖x - c‖ < R
    · apply hsub
      simpa only [Metric.mem_closedBall, dist_eq_norm] using ha.2.le
    · exact False.elim (hx (by simp [G, ha, Nat.ne_of_gt hdpos]))
  have hA : 0 ≤ moserHeight d L * d / L :=
    div_nonneg (mul_nonneg
      (Real.rpow_nonneg (div_nonneg hL.le (sharpCoefficient_pos hd).le) _)
      (Nat.cast_nonneg _)) hL.le
  have henergy : (∫⁻ x in (Ω : Set (Space d)), ENNReal.ofReal (‖weakGradient u.val x‖ ^ d)) = 1 := by
    calc
      _ = ∫⁻ x in (Ω : Set (Space d)), G x := by
        apply lintegral_congr_ae
        filter_upwards [hg] with x hx
        simp only [G, hx]
      _ = ∫⁻ x, G x := setLIntegral_eq_of_support_subset hsupp
      _ = 1 := by
        dsimp only [G]
        rw [annular_energy hdpos c (logarithmicRadius_pos hR L)
          (logarithmicRadius_lt hdpos hR hL) hA,
          profile_energy_scalar hd hR hL, ENNReal.ofReal_one]
  have hpower : (eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
      (volume.restrict (Ω : Set (Space d)))) ^ d = 1 :=
    (naturalEnergy_eq_eLpNorm_pow hdpos
      (weakGradient_aestronglyMeasurable Ω (d : ℝ≥0∞) u.val)).symm.trans henergy
  apply ENNReal.rpow_left_injective (x := (d : ℝ)) (by exact_mod_cast hdpos.ne')
  simpa only [ENNReal.rpow_natCast, ENNReal.one_rpow, one_pow] using hpower

end P102.Sobolev
