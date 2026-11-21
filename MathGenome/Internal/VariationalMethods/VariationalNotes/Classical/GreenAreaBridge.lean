import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.GreenAreaBridge
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.SmoothJordan
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Dulac
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import MathGenome.Internal.MultivariableAnalysis.D04.C09.ArcLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.ParametrizedBoundaryDisplay

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace VariationalNotes.Classical.GreenAreaBridge
open Specs.VariationalNotes.Classical.GreenAreaBridge
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan

/-- Jordan separation, the C¹ local graph boundary, positive finite Lebesgue
area, and precisely the regular-domain hypotheses needed by Green. -/
theorem jordan_area : jordan_areaType := by
  intro c hc
  obtain ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl, hC1,
    _hindexE, _hindexΩ⟩ := D13Unified.Ch21.SmoothJordan.smooth_jordan c hc
  have hpos : 0 < volume Ω := hΩo.measure_pos volume hcomp.1
  have hfin : volume Ω < ⊤ := hΩb.measure_lt_top
  exact ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl, hC1,
    hpos, hfin, ENNReal.toReal_pos hpos.ne' hfin.ne,
    D13Unified.Ch13.Dulac.regular_domain_of_graph_boundary Ω hΩo hΩb hC1⟩

/-- Subtracting a constant changes the integrand by the derivative of the
linear function t ↦ ⟨J₀m,γ(t)⟩; the endpoint term is zero. -/
theorem translation_invariance : translation_invarianceType := by
  intro T γ v hT hC1 hclosed m
  obtain ⟨hγ, hv, hd⟩ := hC1
  have hJ : Continuous (J0 : ℂ → ℂ) := by unfold J0; fun_prop
  have hf : ContinuousOn (boundaryIntegrand γ v) (Icc 0 T) :=
    (hJ.comp_continuousOn hγ).inner hv
  have hg : ContinuousOn (fun t => inner ℝ (J0 m) (v t)) (Icc 0 T) :=
    continuousOn_const.inner hv
  have hi : IntervalIntegrable (boundaryIntegrand γ v) volume 0 T :=
    hf.intervalIntegrable_of_Icc hT
  have hj : IntervalIntegrable (fun t => inner ℝ (J0 m) (v t)) volume 0 T :=
    hg.intervalIntegrable_of_Icc hT
  have hzero : (∫ t in (0 : ℝ)..T, inner ℝ (J0 m) (v t)) = 0 := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (continuousOn_const.inner hγ)
      (fun t ht => (innerSL ℝ (J0 m)).hasFDerivAt.comp_hasDerivAt t
        ((hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))) hj
    simpa only [Function.comp_apply, innerSL_apply_apply, hclosed, sub_self] using he
  have heq : boundaryIntegrand (fun t => γ t - m) v =
      fun t => boundaryIntegrand γ v t - inner ℝ (J0 m) (v t) := by
    funext t
    simp [boundaryIntegrand, J0, mul_sub, inner_sub_left]
  rw [heq, intervalIntegral.integral_sub hi hj, hzero, sub_zero]

/-- Change of parameters for the boundary integrand, including closed-interval
one-sided endpoint derivatives. No monotonicity or global extension is assumed. -/
lemma boundary_integral_reparametrization {T L : ℝ} {γ v : ℝ → ℂ}
    {r α : ℝ → ℝ} (hL : 0 ≤ L) (hcurve : C1Curve γ v T)
    (hr : ContinuousOn r (Icc 0 L)) (hα : ContinuousOn α (Icc 0 L))
    (hmap : MapsTo r (Icc 0 L) (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 L, HasDerivWithinAt r (α t) (Icc 0 L) t) :
    (∫ t in (0 : ℝ)..L, boundaryIntegrand (fun t => γ (r t))
      (fun t => α t • v (r t)) t) =
      ∫ t in r 0..r L, boundaryIntegrand γ v t := by
  have hg : ContinuousOn (boundaryIntegrand γ v) (Icc 0 T) := by
    have hJ : Continuous (J0 : ℂ → ℂ) := by unfold J0; fun_prop
    exact (hJ.comp_continuousOn hcurve.1).inner hcurve.2.1
  have hsub : r '' uIcc 0 L ⊆ Icc 0 T := by
    rw [uIcc_of_le hL]
    exact image_subset_iff.mpr hmap
  have hrd : ∀ t ∈ Ioo (min 0 L) (max 0 L), HasDerivWithinAt r (α t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left hL, max_eq_right hL] at ht
    exact ((hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := L) (f := r) (f' := α) (g := boundaryIntegrand γ v)
    (by simpa only [uIcc_of_le hL] using hr) hrd
    (by simpa only [uIcc_of_le hL] using hα) (hg.mono hsub)
  simpa only [boundaryIntegrand, Function.comp_apply, real_inner_smul_right, mul_comm] using he

/-- A defining covector vanishing on the tangent evaluates positively on
its left normal when it evaluates to one on a positive transverse vector. -/
lemma left_normal_covector_pos (D : ℂ →L[ℝ] ℝ) (a b : ℂ)
    (hab : 0 < det a b) (ha : D a = 0) (hb : D b = 1) : 0 < D (J0 a) := by
  have hD (z : ℂ) : D z = z.re * D 1 + z.im * D Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
    rfl
  have hzero : a ≠ 0 := by
    intro he
    simp [he, det] at hab
  have hsq : 0 < Complex.normSq a := Complex.normSq_pos.mpr hzero
  have heq : det a b * D (J0 a) = Complex.normSq a := by
    rw [hD] at ha hb
    rw [hD]
    simp only [J0, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add]
    dsimp [det]
    rw [Complex.normSq_apply]
    linear_combination (a.re ^ 2 + a.im ^ 2) * hb -
      (a.re * b.re + a.im * b.im) * ha
  exact (mul_pos_iff_of_pos_left hab).mp (heq ▸ hsq)

/-- Positive derivative of a defining function gives the actual signs on
both sufficiently short normal rays; no differentiability of the normal
field as a function of the boundary point is needed. -/
lemma defining_function_rays (F : ℂ → ℝ) (p n : ℂ)
    (hF : DifferentiableAt ℝ F p) (hzero : F p = 0)
    (hpos : 0 < fderiv ℝ F p n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
      0 < F (p + s • n) ∧ F (p - s • n) < 0 := by
  let f : ℝ → ℝ := fun s => F (p + s • n)
  have hf : HasDerivAt f (fderiv ℝ F p n) 0 := by
    have hd : HasDerivAt (fun s : ℝ => p + s • n) n 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add p
    have hF' : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • n) := by
      simpa using hF.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hd
  have he : ∀ᶠ s in 𝓝[≠] (0 : ℝ), 0 < s⁻¹ * f s := by
    simpa [f, hzero] using hf.tendsto_slope_zero.eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp he)
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hp := hεprop (by simpa [Real.dist_eq, abs_of_pos hs.1] using hs.2)
    (show s ∈ ({0} : Set ℝ)ᶜ from hs.1.ne' )
  have hm := hεprop (by simpa [Real.dist_eq, abs_of_pos hs.1] using hs.2)
    (show -s ∈ ({0} : Set ℝ)ᶜ from neg_ne_zero.mpr hs.1.ne')
  constructor
  · exact (mul_pos_iff_of_pos_left (inv_pos.mpr hs.1)).mp hp
  · have hm' : (-s)⁻¹ * F (p - s • n) > 0 := by
      simpa [f, sub_eq_add_neg] using hm
    by_contra hn
    have hle := mul_nonpos_of_nonpos_of_nonneg
      (inv_lt_zero.mpr (neg_neg_of_pos hs.1)).le (le_of_not_gt hn)
    exact (not_lt_of_ge hle) hm'

/-- Each left/right tangent normal ray lies in its corresponding collar
side. The argument uses the derivative of the scalar collar coordinate. -/
lemma collar_normal_rays {c w : Specs.D13Unified.Ch21.Collar.Circle → ℂ} {a : ℝ}
    (hc : RegularEmbeddedLoop c) (hcol : IsCollar c w a) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
      realLift c t + s • J0 (deriv (realLift c) t) ∈ positiveSide c w a ∧
      realLift c t - s • J0 (deriv (realLift c) t) ∈ negativeSide c w a := by
  obtain ⟨F, hF, hzero, hw, hlocal⟩ :=
    D13Unified.Ch21.SmoothJordan.collar_defining_function hcol (q t)
  have hdiff : DifferentiableAt ℝ F (realLift c t) :=
    hF.differentiableAt (by norm_num)
  have hconst : (fun u => F (realLift c u)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    have hh := hc.1.continuous.continuousAt.eventually hlocal
    filter_upwards [hh] with u hu
    exact hu.1.mp ⟨q u, rfl⟩
  have htan : fderiv ℝ F (realLift c t) (deriv (realLift c) t) = 0 := by
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t
      (hc.1.differentiable (by norm_num) t).hasDerivAt
    exact hcomp.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hconst)
  have hpos : 0 < fderiv ℝ F (realLift c t) (J0 (deriv (realLift c) t)) :=
    left_normal_covector_pos _ _ _ (hcol.2.2.1 t) htan hw
  obtain ⟨ε, hε, hray⟩ := defining_function_rays F (realLift c t)
    (J0 (deriv (realLift c) t)) hdiff hzero hpos
  have hp : ∀ᶠ s in 𝓝 (0 : ℝ),
      (realLift c t + s • J0 (deriv (realLift c) t) ∈ range c ↔
        F (realLift c t + s • J0 (deriv (realLift c) t)) = 0) ∧
      (realLift c t + s • J0 (deriv (realLift c) t) ∈ positiveSide c w a ↔
        0 < F (realLift c t + s • J0 (deriv (realLift c) t))) ∧
      (realLift c t + s • J0 (deriv (realLift c) t) ∈ negativeSide c w a ↔
        F (realLift c t + s • J0 (deriv (realLift c) t)) < 0) := by
    have hh : Continuous (fun s : ℝ => realLift c t + s • J0 (deriv (realLift c) t)) := by
      fun_prop
    have ht : Tendsto (fun s : ℝ => realLift c t + s • J0 (deriv (realLift c) t))
        (𝓝 (0 : ℝ)) (𝓝 (c (q t))) := by
      simpa only [ContinuousAt, zero_smul, add_zero, sub_zero, realLift] using
        hh.continuousAt (x := 0)
    exact ht.eventually hlocal
  have hm : ∀ᶠ s in 𝓝 (0 : ℝ),
      (realLift c t - s • J0 (deriv (realLift c) t) ∈ range c ↔
        F (realLift c t - s • J0 (deriv (realLift c) t)) = 0) ∧
      (realLift c t - s • J0 (deriv (realLift c) t) ∈ positiveSide c w a ↔
        0 < F (realLift c t - s • J0 (deriv (realLift c) t))) ∧
      (realLift c t - s • J0 (deriv (realLift c) t) ∈ negativeSide c w a ↔
        F (realLift c t - s • J0 (deriv (realLift c) t)) < 0) := by
    have hh : Continuous (fun s : ℝ => realLift c t - s • J0 (deriv (realLift c) t)) := by
      fun_prop
    have ht : Tendsto (fun s : ℝ => realLift c t - s • J0 (deriv (realLift c) t))
        (𝓝 (0 : ℝ)) (𝓝 (c (q t))) := by
      simpa only [ContinuousAt, zero_smul, add_zero, sub_zero, realLift] using
        hh.continuousAt (x := 0)
    exact ht.eventually hlocal
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp (hp.and hm)
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro s hs
  obtain ⟨hplus, hminus⟩ := hray s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hdist : dist s 0 < δ := by
    simpa [Real.dist_eq, abs_of_pos hs.1] using (hs.2.trans_le (min_le_right ε δ))
  have hl := hδprop hdist
  exact ⟨hl.1.2.1.mpr hplus, hl.2.2.2.mpr hminus⟩

/-- Invert cumulative speed on one turn, preserving the endpoint tangent and
single traversal after passing back from orthonormal real coordinates. -/
theorem arc_length_parametrization_with_tangent (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ)
    (hc : RegularEmbeddedLoop c) :
    ∃ (T : ℝ) (γ v : ℝ → ℂ), ArcLengthParametrization c T γ v ∧
      (∀ u ∈ Icc 0 T, ∃ (t α : ℝ), 0 < α ∧
        γ u = realLift c t ∧ v u = α • deriv (realLift c) t) ∧
      (∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) =
        ∫ t in (0 : ℝ)..1, boundaryIntegrand (realLift c) (deriv (realLift c)) t := by
  let G : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => planeCoordinates (realLift c t)
  let V : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
    planeCoordinates (deriv (realLift c) t)
  have hnorm (z : ℂ) : ‖planeCoordinates z‖ = ‖z‖ :=
    Complex.orthonormalBasisOneI.repr.norm_map z
  have hG : Continuous G := planeCoordinates.continuous.comp hc.1.continuous
  let path : Specs.D04.C09.PathsLength.Model.IntervalPath 2 0 1 :=
    ⟨by norm_num, G, hG.continuousOn⟩
  have hV : Specs.D04.C09.PathsLength.Model.C1Piece path V 0 1 := by
    refine ⟨planeCoordinates.continuous.comp_continuousOn
      hc.1.continuous_deriv_one.continuousOn, ?_⟩
    intro t ht
    exact (planeCoordinates.hasFDerivAt.comp_hasDerivAt t
      ((hc.1.differentiable (by norm_num) t).hasDerivAt)).hasDerivWithinAt
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, V t ≠ 0 := by
    intro t ht hz
    exact hc.2.2 t (planeCoordinates.injective (by simpa [V] using hz))
  obtain ⟨s, hs⟩ := D04.C09.arc_length_accumulation_exists path V hV
  obtain ⟨hs0, hT, hlen, hmono, hbij, hsc, hsd, r, hr, hrc, hrd,
    hgr, hvr, hunit⟩ := D04.C09.regular_arc_length path V (by norm_num) hV hne s hs
  have hr0 : r 0 = 0 := by simpa only [hs0] using hr.2.1 0 (by norm_num)
  have hrT : r (s 1) = 1 := hr.2.1 1 (by norm_num)
  let γ : ℝ → ℂ := fun u => realLift c (r u)
  let v : ℝ → ℂ := fun u => ‖V (r u)‖⁻¹ • deriv (realLift c) (r u)
  have hγeq : γ = fun u => planeCoordinates.symm ((path ∘ r) u) := by
    funext u
    simp [γ, path, G]
  have hveq : v = fun u => planeCoordinates.symm (‖V (r u)‖⁻¹ • V (r u)) := by
    funext u
    simp [v, V]
  have hc1 : C1Curve γ v (s 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hγeq]
      exact planeCoordinates.symm.continuous.comp_continuousOn hgr
    · rw [hveq]
      exact planeCoordinates.symm.continuous.comp_continuousOn hvr.1
    · intro u hu
      rw [hγeq, hveq]
      exact planeCoordinates.symm.hasFDerivAt.comp_hasDerivWithinAt u (hvr.2 u hu)
  have hclosed : γ 0 = γ (s 1) := by
    change realLift c (r 0) = realLift c (r (s 1))
    rw [hr0, hrT]
    simpa using (D13Unified.Ch21.Collar.lift_periodic c 0).symm
  have hvclosed : v 0 = v (s 1) := by
    have hd : deriv (realLift c) 1 = deriv (realLift c) 0 := by
      simpa using D13Unified.Ch21.Collar.derivative_periodic c 0
    simp [v, V, hr0, hrT, hd]
  have hri : MapsTo r (Ico 0 (s 1)) (Ico 0 1) := by
    intro u hu
    have hru := hr.1 (Ico_subset_Icc_self hu)
    refine ⟨hru.1, lt_of_le_of_ne hru.2 ?_⟩
    intro he
    have heq := hr.2.2.1 u (Ico_subset_Icc_self hu)
    rw [he] at heq
    exact hu.2.ne heq.symm
  have hinj : InjOn γ (Ico 0 (s 1)) := by
    intro u hu w hw he
    have hq : q (r u) = q (r w) := hc.2.1 he
    have hre : r u = r w :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
        (by simpa using hri hu) (by simpa using hri hw)).mp hq
    rw [← hr.2.2.1 u (Ico_subset_Icc_self hu),
      ← hr.2.2.1 w (Ico_subset_Icc_self hw), hre]
  have htrace : γ '' Icc 0 (s 1) = range c := by
    apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact ⟨q (r u), rfl⟩
    · rintro z ⟨a, rfl⟩
      let t : ℝ := AddCircle.equivIco (1 : ℝ) 0 a
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        exact ⟨(AddCircle.equivIco (1 : ℝ) 0 a).property.1,
          (by simpa using (AddCircle.equivIco (1 : ℝ) 0 a).property.2.le)⟩
      refine ⟨s t, hbij.1 ht, ?_⟩
      change c (q (r (s t))) = c a
      rw [hr.2.1 t ht]
      exact congrArg c (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0))
  refine ⟨s 1, γ, v, ⟨hT, hlen, hc1, hclosed, hvclosed, hinj, htrace, ?_⟩, ?_, ?_⟩
  · intro u hu
    rw [← hnorm (v u)]
    change ‖planeCoordinates (‖V (r u)‖⁻¹ • deriv (realLift c) (r u))‖ = 1
    rw [map_smul]
    exact hunit u hu
  · intro u hu
    exact ⟨r u, ‖V (r u)‖⁻¹,
      inv_pos.mpr (norm_pos_iff.mpr (hne _ (hr.1 hu))), rfl, rfl⟩
  · have hcurve : C1Curve (realLift c) (deriv (realLift c)) 1 := by
      refine ⟨hc.1.continuous.continuousOn, hc.1.continuous_deriv_one.continuousOn, ?_⟩
      intro t ht
      exact (hc.1.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt
    have hh := boundary_integral_reparametrization hT.le hcurve hr.2.2.2 hrc hr.1 hrd
    simpa only [hr0, hrT] using hh

/-- Existence of the closed unit-speed traversal with its geometric length. -/
theorem arc_length_parametrization : arc_length_parametrizationType := by
  intro c hc
  obtain ⟨T, γ, v, hparam, _⟩ := arc_length_parametrization_with_tangent c hc
  exact ⟨T, γ, v, hparam⟩

/-- A closed interval traversal injective before its final endpoint is also
injective after its initial endpoint. -/
lemma closed_injOn_Ioc {T : ℝ} {γ : ℝ → ℂ} (hT : 0 < T)
    (hclosed : γ 0 = γ T) (hinj : InjOn γ (Ico 0 T)) : InjOn γ (Ioc 0 T) := by
  intro u hu w hw he
  by_cases huT : u = T
  · subst u
    by_cases hwT : w = T
    · exact hwT.symm
    · have h0w : γ 0 = γ w := hclosed.trans he
      have hwe := hinj ⟨le_rfl, hT⟩ ⟨hw.1.le, lt_of_le_of_ne hw.2 hwT⟩ h0w
      exact False.elim (hw.1.ne' hwe.symm)
  · by_cases hwT : w = T
    · subst w
      have hu0 : γ u = γ 0 := he.trans hclosed.symm
      have hue := hinj ⟨hu.1.le, lt_of_le_of_ne hu.2 huT⟩ ⟨le_rfl, hT⟩ hu0
      exact False.elim (hu.1.ne' hue)
    · exact hinj ⟨hu.1.le, lt_of_le_of_ne hu.2 huT⟩
        ⟨hw.1.le, lt_of_le_of_ne hw.2 hwT⟩ he

/-- Reversing a closed unit-speed traversal preserves all geometric and C¹
properties and negates its velocity, including at the two endpoints. -/
lemma arc_length_reverse {c : Specs.D13Unified.Ch21.Collar.Circle → ℂ} {T : ℝ} {γ v : ℝ → ℂ}
    (h : ArcLengthParametrization c T γ v) :
    ArcLengthParametrization c T (fun t => γ (T - t)) (fun t => -v (T - t)) := by
  obtain ⟨hT, hlen, ⟨hγ, hv, hd⟩, hclosed, hvclosed, hinj, htrace, hnorm⟩ := h
  have hmap : MapsTo (fun t => T - t) (Icc 0 T) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hr : Continuous (fun t : ℝ => T - t) := by fun_prop
  refine ⟨hT, hlen, ⟨hγ.comp hr.continuousOn hmap,
    (hv.comp hr.continuousOn hmap).neg, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hh := (hd _ (hmap ht)).scomp t
      (((hasDerivAt_id t).const_sub T).hasDerivWithinAt) hmap
    convert hh using 1 <;> simp [Function.comp_def]
  · simpa using hclosed.symm
  · simpa using congrArg Neg.neg hvclosed.symm
  · intro u hu w hw he
    have hui : T - u ∈ Ioc 0 T := by constructor <;> linarith [hu.1, hu.2]
    have hwi : T - w ∈ Ioc 0 T := by constructor <;> linarith [hw.1, hw.2]
    have hh := closed_injOn_Ioc hT hclosed hinj hui hwi he
    linarith
  · apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      rw [← htrace]
      exact ⟨T - t, hmap ht, rfl⟩
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := htrace.symm ▸ hz
      exact ⟨T - t, hmap ht, by simp⟩
  · intro t ht
    simpa using hnorm _ (hmap ht)

/-- The normal ray assertion is unchanged by positive scaling of the
velocity. -/
lemma normal_rays_smul {Ω E : Set ℂ} {p n : ℂ} {α : ℝ} (hα : 0 < α)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε, p + s • J0 n ∈ Ω ∧ p - s • J0 n ∈ E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
      p + s • J0 (α • n) ∈ Ω ∧ p - s • J0 (α • n) ∈ E := by
  obtain ⟨ε, hε, hprop⟩ := h
  refine ⟨ε / α, div_pos hε hα, ?_⟩
  intro s hs
  have hh := hprop (s * α) ⟨mul_pos hs.1 hα, (lt_div_iff₀ hα).mp hs.2⟩
  have hJ : J0 (α • n) = α • J0 n := by
    simp [J0, mul_comm, mul_left_comm]
  rw [hJ, smul_smul]
  exact hh

/-- Choose the collar side belonging to the bounded Jordan component and,
when necessary, reverse the unit-speed traversal to put that side on the left. -/
theorem positive_arc_length_jordan : positive_arc_length_jordanType := by
  intro c hc
  obtain ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl,
    _hiE, _hiΩ, w, a, hcol, hside⟩ :=
    D13Unified.Ch21.SmoothJordan.topological_jordan c hc
  have hC1 := D13Unified.Ch21.SmoothJordan.hasC1Boundary_of_collar
    hcol hcomp hΩf hside
  have hpos : 0 < MeasureTheory.volume Ω := hΩo.measure_pos _ hcomp.1
  have hfin : MeasureTheory.volume Ω < ⊤ := hΩb.measure_lt_top
  have harea : 0 < area Ω := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hEoff : ∀ z ∈ E, z ∉ closure Ω := by
    intro z hz hzc
    rw [hcl] at hzc
    rcases hzc with hΩ | hc'
    · exact Set.disjoint_left.mp hcomp.2.2.1 hΩ hz
    · have hzoff : z ∈ (range c)ᶜ := hcomp.2.2.2.1 ▸ Or.inr hz
      exact hzoff hc'
  obtain ⟨T, γ, v, hparam, htangent, _hintegral⟩ := arc_length_parametrization_with_tangent c hc
  have hnormal : ∀ u ∈ Icc 0 T, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
      γ u + s • J0 (v u) ∈ positiveSide c w a ∧
      γ u - s • J0 (v u) ∈ negativeSide c w a := by
    intro u hu
    obtain ⟨t, α, hα, hγ, hv⟩ := htangent u hu
    rw [hγ, hv]
    exact normal_rays_smul hα (collar_normal_rays hc hcol t)
  rcases hside with ⟨hplus, hminus⟩ | ⟨hplus, hminus⟩
  · have horient : PositivelyOriented Ω γ v T := by
      intro u hu
      obtain ⟨ε, hε, hprop⟩ := hnormal u hu
      refine ⟨ε, hε, ?_⟩
      intro s hs
      obtain ⟨hp, hm⟩ := hprop s hs
      exact ⟨hplus hp, hEoff _ (hminus hm)⟩
    exact ⟨Ω, E, T, γ, v, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb,
      hΩf, hEf, hcl, hC1, hpos, hfin, harea, hparam, horient⟩
  · have horient : PositivelyOriented Ω (fun t => γ (T - t)) (fun t => -v (T - t)) T := by
      intro u hu
      have hu' : T - u ∈ Icc 0 T := by constructor <;> linarith [hu.1, hu.2]
      obtain ⟨ε, hε, hprop⟩ := hnormal (T - u) hu'
      refine ⟨ε, hε, ?_⟩
      intro s hs
      obtain ⟨hp, hm⟩ := hprop s hs
      simpa only [J0, mul_neg, smul_neg, sub_eq_add_neg, neg_neg] using
        And.intro (hminus hm) (hEoff _ (hplus hp))
    exact ⟨Ω, E, T, (fun t => γ (T - t)), (fun t => -v (T - t)), hcomp,
      hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl, hC1, hpos, hfin, harea,
      arc_length_reverse hparam, horient⟩

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C06.JordanRegions.Model

/-- The orthonormal real coordinate on a one-dimensional parameter space. -/
abbrev scalarCoordinates : ℝ ≃ₗᵢ[ℝ] E 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- A genuine one-dimensional Jordan patch integral on a closed interval
is its ordinary Lebesgue interval integral, with the canonical coefficient.
This proves the Riemann/Lebesgue and E¹/ℝ changes of convention explicitly. -/
lemma patch_interval_integral {n : ℕ} {O : Set (E n)}
    (P : Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.Patch 1 O)
    (omega : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField n 1)
    (hform : Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O omega)
    {T : ℝ} (hT : 0 ≤ T)
    (hregion : P.region = {u | u 0 ∈ Icc 0 T}) :
    Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.patchIntegral P (fun _ => 1) omega =
      ∫ t in (0 : ℝ)..T,
        Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient P omega
          (scalarCoordinates t) := by
  let f := Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.coefficient P omega
  have hreg : MeasurableSet P.region := by
    rw [hregion]
    exact measurableSet_Icc.preimage (by fun_prop)
  have hint : RegionIntegrable (fun u : P.region => f u) := by
    simpa only [Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.weightedCoefficient,
      one_mul] using D04.GeometricPatches.weighted_integrable P omega hform
        (fun _ => 1) continuousOn_const
  have hbridge := (D04.MeasureBridge.region_bridge_ambient f hreg hint).2
  have hcoord := scalarCoordinates.measurePreserving.integral_comp
    scalarCoordinates.toHomeomorph.isClosedEmbedding.measurableEmbedding (P.region.indicator f)
  have hind : (fun t : ℝ => P.region.indicator f (scalarCoordinates t)) =
      (Icc 0 T).indicator (fun t => f (scalarCoordinates t)) := by
    funext t
    have ht : scalarCoordinates t ∈ P.region ↔ t ∈ Icc 0 T := by
      rw [hregion]
      change (OrthonormalBasis.singleton (Fin 1) ℝ).repr t 0 ∈ Icc 0 T ↔
        t ∈ Icc 0 T
      rw [OrthonormalBasis.singleton_repr]
    by_cases h : t ∈ Icc 0 T
    · simp only [indicator_of_mem h, indicator_of_mem (ht.mpr h)]
    · simp only [indicator_of_notMem h, indicator_of_notMem (mt ht.mp h)]
  change (∫ t : ℝ, P.region.indicator f (scalarCoordinates t)) =
    ∫ x : E 1, P.region.indicator f x at hcoord
  rw [hind, integral_indicator measurableSet_Icc, integral_indicator hreg,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT] at hcoord
  calc
    _ = regionIntegral (fun u : P.region => f u) := by
      simp only [Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.patchIntegral,
        Specs.D04.C15.FiniteGeometricPatchIntegrals.Model.weightedCoefficient, one_mul]
      rfl
    _ = ∫ x in P.region, f x := hbridge
    _ = _ := hcoord.symm

/-- The coordinate line integrand of Green's area field is exactly one half
of the real Euclidean pairing used by the manuscript. -/
lemma area_line_integrand (z v : ℂ) :
    -(planeCoordinates z 1) / 2 * planeCoordinates v 0 +
      planeCoordinates z 0 / 2 * planeCoordinates v 1 =
        (1 / 2 : ℝ) * inner ℝ (J0 z) v := by
  change -z.im / 2 * v.re + z.re / 2 * v.im = _
  rw [Complex.inner]
  simp only [J0, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  ring

/-- The actual coefficient in any embedded boundary chart, expressed in
complex Euclidean coordinates. The global assembly of chart coefficients
into a full traversal is a separate obligation. -/
lemma area_chart_coefficient {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (u : c.source) :
    Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.topCoefficient
      (Specs.D04.C15.GeneralizedStokes.Model.tangentRestriction 1 1 M
        (circulationForm (fun x => -(x 1) / 2) (fun x => x 0 / 2))) c u =
      (1 / 2 : ℝ) * inner ℝ (J0 (planeCoordinates.symm (c.toFun u)))
        (planeCoordinates.symm
          (Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u
            (standardBasis 1 0))) := by
  rw [D04.Green.line_coefficient]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    area_line_integrand (planeCoordinates.symm (c.toFun u))
      (planeCoordinates.symm
        (Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c u
          (standardBasis 1 0)))

private lemma area_density (x : E 2) :
    circulationDensity (fun x => -(x 1) / 2) (fun x => x 0 / 2) x = 1 := by
  have hQ : scalarPartialDerivative (fun x : E 2 => x 0 / 2) x 0 = 1 / 2 := by
    change deriv (fun t : ℝ => (x + t • standardBasis 2 0) 0 / 2) 0 = 1 / 2
    have he : (fun t : ℝ => (x + t • standardBasis 2 0) 0 / 2) =
        fun t : ℝ => (x 0 + t) / 2 := by
      funext t
      simp [standardBasis]
    rw [he]
    exact (((hasDerivAt_id 0).const_add (x 0)).div_const 2).deriv
  have hP : scalarPartialDerivative (fun x : E 2 => -(x 1) / 2) x 1 = -(1 / 2) := by
    change deriv (fun t : ℝ => -((x + t • standardBasis 2 1) 1) / 2) 0 = -(1 / 2)
    have he : (fun t : ℝ => -((x + t • standardBasis 2 1) 1) / 2) =
        fun t : ℝ => -(x 1 + t) / 2 := by
      funext t
      simp [standardBasis]
    rw [he]
    convert (((hasDerivAt_id 0).const_add (x 1)).neg.div_const 2).deriv using 1 <;> norm_num
  unfold circulationDensity
  rw [hQ, hP]
  norm_num

/-- Green's actual manifold integral for (-y/2,x/2), with its Riemann bulk
value identified with Lebesgue area by the measure bridge and the standard
orthonormal coordinates. No curve-integral conversion is assumed here. -/
theorem green_boundary_area : green_boundary_areaType := by
  intro Ω hΩo hΩb hC1
  let W := planeCoordinates.symm ⁻¹' Ω
  have hW : IsClassicalRegularDomain W :=
    D13Unified.Ch13.Dulac.regular_domain_of_graph_boundary Ω hΩo hΩb hC1
  have hP : CrOn 1 (univ : Set (E 2)) (fun x => -(x 1) / 2) := by
    apply (D04.crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
    fun_prop
  have hQ : CrOn 1 (univ : Set (E 2)) (fun x => x 0 / 2) := by
    apply (D04.crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
    fun_prop
  obtain ⟨hb, o, bO, ho, hbo, hcirc, _hdiv, hboundary, _hflux, _hnormal⟩ :=
    D04.Green.green hW univ (fun x => -(x 1) / 2) (fun x => x 0 / 2)
      isOpen_univ (subset_univ _) hP hQ
  have hvol : MeasureTheory.volume W = MeasureTheory.volume Ω := by
    exact Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
      hΩo.measurableSet.nullMeasurableSet
  have hbulk : regionIntegral (fun x : W =>
      circulationDensity (fun x => -(x 1) / 2) (fun x => x 0 / 2) x) = area Ω := by
    calc
      _ = ∫ x in W, circulationDensity (fun x => -(x 1) / 2) (fun x => x 0 / 2) x :=
        (D04.MeasureBridge.region_bridge_ambient _ hW.isOpen.measurableSet hcirc).2
      _ = area Ω := by
        simp_rw [area_density]
        simp [area, measureReal_def, hvol]
  exact ⟨hW, hb, o, bO, ho, hbo, hbulk ▸ hboundary⟩

/-- A tangent covector points negatively along the left normal of a
positively oriented tangent relative to the outward transverse vector. -/
lemma left_normal_covector_neg (D : ℂ →L[ℝ] ℝ) (n v : ℂ)
    (hdet : 0 < det n v) (hv : D v = 0) (hn : 0 < D n) : D (J0 v) < 0 := by
  let b : ℂ := -(D n)⁻¹ • n
  have hbn : (-D) b = 1 := by
    change -(D (-(D n)⁻¹ • n)) = 1
    rw [map_smul]
    change -(-(D n)⁻¹ * D n) = 1
    field_simp
  have hdet' : 0 < det v b := by
    have he : det v b = (D n)⁻¹ * det n v := by
      simp [b, det]
      ring
    rw [he]
    exact mul_pos (inv_pos.mpr hn) hdet
  have hh := left_normal_covector_pos (-D) v b hdet' (by simp [hv]) hbn
  simpa using hh

/-- A regular-domain defining function turns an outward-oriented tangent
into actual short inward left-normal and outward right-normal rays. -/
lemma outward_tangent_normal_rays {Ω : Set ℂ}
    (hD : IsClassicalRegularDomain (planeCoordinates.symm ⁻¹' Ω))
    (p v : ℂ) (hp : planeCoordinates p ∈ frontier (planeCoordinates.symm ⁻¹' Ω))
    (ρ : E 2 → ℝ) (U : Set (E 2))
    (hρ : IsDefiningFunction (planeCoordinates.symm ⁻¹' Ω) U ρ)
    (hpU : planeCoordinates p ∈ U)
    (htan : fderiv ℝ (ρ ∘ planeCoordinates) p v = 0)
    (hdet : 0 < det
      (planeCoordinates.symm (outwardNormal hD ⟨planeCoordinates p, hp⟩)) v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Ioo 0 ε,
      p + s • J0 v ∈ Ω ∧ p - s • J0 v ∉ closure Ω := by
  let F : ℂ → ℝ := ρ ∘ planeCoordinates
  let n : ℂ := planeCoordinates.symm (outwardNormal hD ⟨planeCoordinates p, hp⟩)
  have hρdiff : DifferentiableAt ℝ ρ (planeCoordinates p) :=
    (hρ.regular.contDiffAt (hρ.isOpen.mem_nhds hpU)).differentiableAt (by norm_num)
  have hFD := hρdiff.hasFDerivAt.comp p planeCoordinates.hasFDerivAt
  have hFdiff : DifferentiableAt ℝ F p := hFD.differentiableAt
  have hzero : F p = 0 := (hρ.zero_level _ hpU).mp hp
  have hn : 0 < fderiv ℝ F p n := by
    rw [hFD.fderiv]
    change 0 < fderiv ℝ ρ (planeCoordinates p)
      (planeCoordinates (planeCoordinates.symm (outwardNormal hD ⟨planeCoordinates p,hp⟩)))
    rw [ContinuousLinearEquiv.apply_symm_apply,
      D04.ClassicalRegularDomains.outwardNormal_formula hD _ hρ hpU]
    exact (D04.ClassicalRegularDomains.normal_properties hρ hpU hp).2.2.2
  have hneg : fderiv ℝ F p (J0 v) < 0 :=
    left_normal_covector_neg _ n v hdet htan hn
  obtain ⟨ε, hε, hray⟩ := defining_function_rays (fun z => -F z) p (J0 v)
    hFdiff.neg (by simp [hzero]) (by
      change 0 < fderiv ℝ (-F) p (J0 v)
      rw [fderiv_neg]
      simpa using hneg)
  have hneigh : ∀ᶠ s in 𝓝 (0 : ℝ),
      planeCoordinates (p + s • J0 v) ∈ U ∧ planeCoordinates (p - s • J0 v) ∈ U := by
    have hplus : Continuous (fun s : ℝ => planeCoordinates (p + s • J0 v)) := by fun_prop
    have hminus : Continuous (fun s : ℝ => planeCoordinates (p - s • J0 v)) := by fun_prop
    have hp' : Tendsto (fun s : ℝ => planeCoordinates (p + s • J0 v))
        (𝓝 0) (𝓝 (planeCoordinates p)) := by
      simpa only [ContinuousAt, zero_smul, add_zero] using hplus.continuousAt (x := 0)
    have hm' : Tendsto (fun s : ℝ => planeCoordinates (p - s • J0 v))
        (𝓝 0) (𝓝 (planeCoordinates p)) := by
      simpa only [ContinuousAt, zero_smul, sub_zero] using hminus.continuousAt (x := 0)
    exact (hp'.eventually (hρ.isOpen.mem_nhds hpU)).and
      (hm'.eventually (hρ.isOpen.mem_nhds hpU))
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.mp hneigh
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro s hs
  obtain ⟨hleft, hright⟩ := hray s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hdist : dist s 0 < δ := by
    simpa [Real.dist_eq, abs_of_pos hs.1] using hs.2.trans_le (min_le_right ε δ)
  obtain ⟨hplusU, hminusU⟩ := hδprop hdist
  constructor
  · have hh := (hρ.negative _ hplusU).mpr (show F (p + s • J0 v) < 0 by linarith)
    simpa using hh
  · intro hcl
    have hcl' : planeCoordinates (p - s • J0 v) ∈
        closure (planeCoordinates.symm ⁻¹' Ω) := by
      change planeCoordinates (p - s • J0 v) ∈
        closure (planeCoordinates.symm.toHomeomorph ⁻¹' Ω)
      rw [← planeCoordinates.symm.toHomeomorph.preimage_closure]
      simpa using hcl
    rw [closure_eq_self_union_frontier] at hcl'
    rcases hcl' with hin | hbd
    · have hh := (hρ.negative _ hminusU).mp hin
      change F (p - s • J0 v) < 0 at hh
      linarith
    · have hh := (hρ.zero_level _ hminusU).mp hbd
      change F (p - s • J0 v) = 0 at hh
      linarith

open Specs.VariationalNotes.Classical.GreenAreaBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

lemma map_derivative_in_parameter {O : Set (E 2)} (P : Patch 1 O)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hmap : ∀ u, P.map u = planeCoordinates (γ (u 0))) (t : ℝ) :
    fderiv ℝ P.map (scalarCoordinates t) (standardBasis 1 0) =
      planeCoordinates (deriv γ t) := by
  have hd := hγ.differentiable (by norm_num)
  have hcomp := planeCoordinates.hasFDerivAt.comp_hasDerivAt t ((hd t).hasDerivAt)
  have hp : DifferentiableAt ℝ P.map (scalarCoordinates t) := by
    have hm : P.map = fun u => planeCoordinates (γ (u 0)) := funext hmap
    rw [hm]
    exact planeCoordinates.differentiableAt.comp _ ((hd _).comp _ (by fun_prop))
  have hc := hp.hasFDerivAt.comp_hasDerivAt t scalarCoordinates.hasFDerivAt.hasDerivAt
  have hfun : (fun s : ℝ => P.map (scalarCoordinates s)) = fun s => planeCoordinates (γ s) := by
    funext s
    rw [hmap]
    congr 2
    change (OrthonormalBasis.singleton (Fin 1) ℝ).repr s 0 = s
    rw [OrthonormalBasis.singleton_repr]
  change HasDerivAt (fun s => P.map (scalarCoordinates s)) _ t at hc
  rw [hfun] at hc
  have he := hc.unique hcomp
  have hb : scalarCoordinates (1 : ℝ) = standardBasis 1 0 :=
    D12Complex.ComplexGreenBridge.interval_basis
  change (fderiv ℝ P.map (scalarCoordinates t)) (scalarCoordinates 1) = _ at he
  rwa [hb] at he

lemma parametrized_patch_area_integral {O : Set (E 2)} (P : Patch 1 O)
    (hform : IsCrForm (some 0) O
      (circulationForm (fun x => -(x 1) / 2) (fun x => x 0 / 2)))
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hmap : ∀ u, P.map u = planeCoordinates (γ (u 0)))
    {T : ℝ} (hT : 0 ≤ T) (hregion : P.region = {u | u 0 ∈ Icc 0 T}) :
    patchIntegral P (fun _ => 1)
      (circulationForm (fun x => -(x 1) / 2) (fun x => x 0 / 2)) =
        (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ (deriv γ) t := by
  rw [patch_interval_integral P _ hform hT hregion]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [(D04.Green.patch_line_coefficients P (fun x => -(x 1) / 2)
    (fun x => x 0 / 2) (scalarCoordinates t)).1,
    map_derivative_in_parameter P γ hγ hmap t, hmap]
  have hcoord : (scalarCoordinates t) 0 = t := by
    change (OrthonormalBasis.singleton (Fin 1) ℝ).repr t 0 = t
    rw [OrthonormalBasis.singleton_repr]
  rw [hcoord]
  exact area_line_integrand _ _

open D12Complex.ComplexGreenBridge
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C15.GeneralizedStokes.Model

lemma display_area_formula {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hD : IsClassicalRegularDomain (planeIsometry '' Ω))
    (B : BoundaryDisplay hD (univ : Set (E 2))) (hc : B.count = 1)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hmap : ∀ u, (B.patch (Fin.cast hc.symm 0)).map u = planeCoordinates (γ (u 0)))
    {T : ℝ} (hT : 0 ≤ T)
    (hregion : (B.patch (Fin.cast hc.symm 0)).region = {u | u 0 ∈ Icc 0 T}) :
    area Ω = (B.sign (Fin.cast hc.symm 0)).val *
      ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ (deriv γ) t) := by
  let η := circulationForm (fun x => -(x 1) / 2) (fun x => x 0 / 2)
  have hP : Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 (univ : Set (E 2))
      (fun x => -(x 1) / 2) := by
    apply (D04.crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
    fun_prop
  have hQ : Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1 (univ : Set (E 2))
      (fun x => x 0 / 2) := by
    apply (D04.crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
    fun_prop
  have hη := D04.Green.circulation_regular univ _ _ isOpen_univ hP hQ
  have hη0 := D04.LocalStokes.form_C0 univ _ hη
  have hgreen := D04.Green.green_for_form hD B.orientation B.ambient
    B.boundaryOrientation B.outward univ (subset_univ _) η hη
    (fun _ => 1) continuousOn_const (by
      intro x hx
      rw [D04.Green.exterior_circulation_all]
      change circulationDensity _ _ x • _ = _
      rw [area_density])
  have hbulk : Specs.D04.C06.JordanRegions.Model.regionIntegral
      (fun _ : (planeIsometry '' Ω) => (1 : ℝ)) = area Ω := by
    calc
      _ = ∫ _x in (planeIsometry '' Ω), (1 : ℝ) :=
        (D04.MeasureBridge.region_bridge_ambient _ hD.isOpen.measurableSet hgreen.1).2
      _ = area Ω := by
        have hv : MeasureTheory.volume (planeIsometry '' Ω) = MeasureTheory.volume Ω := by
          rw [show planeIsometry '' Ω = planeCoordinates.symm ⁻¹' Ω from
            Equiv.image_eq_preimage_symm planeIsometry.toEquiv Ω]
          exact
          Complex.orthonormalBasisOneI.measurePreserving_repr_symm.measure_preimage
            hΩo.measurableSet.nullMeasurableSet
        simp [area, measureReal_def, hv]
  have hcompact : IsCompact (intrinsicBoundary 1 2 (closure (planeIsometry '' Ω))) := by
    rw [B.boundary_eq]
    exact (D04.RegularDomainGeometry.closure_manifold hD).1.of_isClosed_subset
      isClosed_frontier frontier_subset_closure
  have hdisplay := D04.ManifoldBoundaryAssembly.regular_display_integral
    B.boundaryOrientation hcompact (subset_univ _) B.patch B.sign B.regular
    B.seams B.seam_dimension B.self_intersections B.intersections B.cover η hη0
  have he := D04Stokes.positive_integral_unique B.boundaryOrientation _ hgreen.2 hdisplay
  rw [hbulk] at he
  calc
    area Ω = ∑ j, (B.sign j).val * patchIntegral (B.patch j) (fun _ => 1) η := he
    _ = (B.sign (Fin.cast hc.symm 0)).val *
        patchIntegral (B.patch (Fin.cast hc.symm 0)) (fun _ => 1) η := by
      have hs := Fintype.sum_equiv (Fin.castOrderIso hc).toEquiv
        (fun j => (B.sign j).val * patchIntegral (B.patch j) (fun _ => 1) η)
        (fun j : Fin 1 => (B.sign (Fin.cast hc.symm j)).val *
          patchIntegral (B.patch (Fin.cast hc.symm j)) (fun _ => 1) η) (by intro j; simp)
      simpa only [Fin.sum_univ_one] using hs
    _ = _ := by rw [parametrized_patch_area_integral _ hη0 γ hγ hmap hT hregion]

lemma display_area_formula_literal {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hD : IsClassicalRegularDomain (planeIsometry '' Ω))
    (B : BoundaryDisplay hD (univ : Set (E 2))) (hc : B.count = 1)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hmap : ∀ u, (B.patch (Fin.cast hc.symm 0)).map u =
      planeIsometry (γ (intervalIsometry.symm u)))
    {T : ℝ} (hT : 0 ≤ T)
    (hregion : (B.patch (Fin.cast hc.symm 0)).region = intervalIsometry '' Icc 0 T) :
    area Ω = (B.sign (Fin.cast hc.symm 0)).val *
      ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ (deriv γ) t) := by
  refine display_area_formula hΩo hD B hc γ hγ ?_ hT ?_
  · intro u
    rw [hmap]
    congr 2
  · rw [hregion]
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      change intervalIsometry t 0 ∈ Icc 0 T
      rwa [D12Complex.ParametrizedBoundaryDisplay.interval_coordinate]
    · intro ht
      refine ⟨u 0, ht, ?_⟩
      apply intervalIsometry.symm.injective
      rw [LinearIsometryEquiv.symm_apply_apply]
      have h := D12Complex.ParametrizedBoundaryDisplay.interval_coordinate (intervalIsometry.symm u)
      simpa only [LinearIsometryEquiv.apply_symm_apply] using h


open Function Topology
open D12Complex.ParametrizedBoundaryDisplay
lemma lift_local_extension (Ω : Set ℂ) (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ)
    (hc : RegularEmbeddedLoop c) (hfront : frontier Ω = range c) (a b : ℝ) :
    LocalRegularExtension Ω (realLift c) a b := by
  classical
  intro t ht
  let e : OpenPartialHomeomorph ℝ Specs.D13Unified.Ch21.Collar.Circle :=
    AddCircle.openPartialHomeomorphCoe (1 : ℝ) (t - 1/2)
  have heq : (e : ℝ → Specs.D13Unified.Ch21.Collar.Circle) = q := rfl
  have hesource : e.source = Ioo (t - 1/2) (t + 1/2) := by
    change Ioo (t - 1/2) (t - 1/2 + 1) = _
    congr 1; ring
  have htI : t ∈ e.source := by rw [hesource]; constructor <;> linarith
  have hcEmb := (D13Unified.Ch21.Collar.circleC1_continuous hc.1).isClosedEmbedding hc.2.1
  obtain ⟨W, hW, hWeq⟩ := hcEmb.isEmbedding.isInducing.image_eq_isOpen_inter_range e.open_target
  let f : e.source → ℂ := fun x => realLift c x
  have hfEmb : Topology.IsEmbedding f := by
    have hh := hcEmb.isEmbedding.comp e.isOpenEmbedding_restrict.isEmbedding
    change Topology.IsEmbedding (fun x : e.source => c (e x)) at hh
    simpa only [heq, f, realLift] using hh
  have hfimage : range f = W ∩ frontier Ω := by
    rw [hfront, ← hWeq, ← e.image_source_eq_target]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨q x, ⟨x, x.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let : Nonempty e.source := ⟨⟨t, htI⟩⟩
  let κ : ℂ → ℝ := fun z => (invFun f z).val
  have hκleft (s : ℝ) (hs : s ∈ e.source) : κ (realLift c s) = s := by
    have h := Function.leftInverse_invFun hfEmb.injective ⟨s, hs⟩
    exact congrArg Subtype.val h
  have hκright (z : ℂ) (hz : z ∈ range f) : realLift c (κ z) = z := by
    exact Function.invFun_eq hz
  have hκcont : ContinuousOn κ (range f) := by
    let F : range f → e.source := fun z => invFun f z
    have hFc : Continuous F := hfEmb.continuous_iff.mpr (by
      have heqF : f ∘ F = Subtype.val := by
        funext z
        exact Function.invFun_eq z.property
      rw [heqF]
      exact continuous_subtype_val)
    exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hFc)
  refine ⟨1/2, W, realLift c, κ, by norm_num, hW, ?_, hc.1.contDiffOn,
    fun s _ => hc.2.2 s, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hmem : realLift c t ∈ range f := ⟨⟨t, htI⟩, rfl⟩
    rw [hfimage] at hmem
    exact hmem.1
  · intro s hs
    have hmem : realLift c s ∈ range f := ⟨⟨s, hesource ▸ hs⟩, rfl⟩
    rw [hfimage] at hmem
    exact ⟨hmem.2, hmem.1⟩
  · intro z hz
    exact hesource ▸ (invFun f z).property
  · intro s hs
    exact hκleft s (hesource ▸ hs)
  · intro z hz
    apply hκright
    rw [hfimage]
    exact ⟨hz.2, hz.1⟩
  · rw [hfimage] at hκcont
    simpa only [inter_comm] using hκcont

lemma lifted_boundary_curves (Ω : Set ℂ)
    (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ)
    (hc : RegularEmbeddedLoop c) (hfront : frontier Ω = range c) :
    RegularBoundaryCurves Ω 1 (fun _ => realLift c)
      (fun _ => 0) (fun _ => 1) (fun _ => univ) := by
  constructor
  · intro _; norm_num
  · intro _; exact isOpen_univ
  · intro _; exact subset_univ _
  · intro _; exact hc.1.contDiffOn
  · intro _ t _; exact hc.2.2 t
  · simp only [iUnion_const]
    rw [hfront]
    apply Subset.antisymm
    · rintro z ⟨u, rfl⟩
      obtain ⟨s, hs, hsu⟩ := AddCircle.eq_coe_Ico u
      exact ⟨s, ⟨hs.1, hs.2.le⟩, congrArg c hsu⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨q t, rfl⟩
  · intro _ u hu v hv he
    have hq : q u = q v := hc.2.1 he
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using (show u ∈ Ico (0:ℝ) 1 from ⟨hu.1.le, hu.2⟩))
      (by simpa using (show v ∈ Ico (0:ℝ) 1 from ⟨hv.1.le, hv.2⟩))).mp hq
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro _
    exact lift_local_extension Ω c hc hfront 0 1

open D12Complex.ComplexGreenBridge
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C01.EuclideanInterfaces.Model
set_option backward.isDefEq.respectTransparency false in
lemma omega_complex_det (n v : ℂ) :
    omega 2 (Fin.cons (planeIsometry n) (fun _ : Fin 1 => planeIsometry v)) = det n v := by
  change Matrix.det (fun i j : Fin 2 =>
    (![planeIsometry n, planeIsometry v] j) i) = _
  rw [Matrix.det_fin_two]
  simp [planeIsometry, Complex.orthonormalBasisOneI, det, mul_comm]

lemma signed_normal_det_all (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ)
    (N : ℂ → ℂ) (s : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < s * det (N (realLift c t)) (deriv (realLift c) t)) :
    ∀ t : ℝ, 0 < s * det (N (realLift c t)) (deriv (realLift c) t) := by
  intro t
  obtain ⟨r, hr, hq⟩ := AddCircle.eq_coe_Ico (q t)
  have heq : realLift c r = realLift c t := congrArg c hq
  have hdeq : deriv (realLift c) r = deriv (realLift c) t := by
    change D13Unified.Ch21.Collar.tangent c (q r) =
      D13Unified.Ch21.Collar.tangent c (q t)
    rw [show q r = q t from hq]
  simpa only [heq, hdeq] using h r ⟨hr.1, hr.2.le⟩

open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
lemma interval_frame_signed_det_all {Ω : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' Ω))
    (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ) (hc : RegularEmbeddedLoop c)
    {O : Set (E 2)} (P : Patch 1 O) (s : PointSign)
    (hregion : P.region = intervalIsometry '' Icc (0 : ℝ) 1)
    (hmap : ∀ x, P.map x = planeIsometry (realLift c (intervalIsometry.symm x)))
    (hframe : PatchFrame hD P s) :
    ∀ t : ℝ, 0 < s.val * det (normalAt hD (realLift c t)) (deriv (realLift c) t) := by
  apply signed_normal_det_all
  intro t ht
  have hmem : intervalIsometry t ∈ P.region := by
    rw [hregion]
    exact mem_image_of_mem _ ht
  have h := (hframe _ hmem).2.2
  have hcol : (fun i : Fin 1 => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i)) =
      fun _ : Fin 1 => planeIsometry (deriv (realLift c) t) := by
    funext i
    exact interval_patch_column P _ hmap (hc.1.differentiable (by norm_num) t) i
  rw [interval_patch_normal hD P _ hmap t, hcol, omega_complex_det] at h
  exact h


/-- The whole lifted loop lies in the zero set of any local defining
function, so each signed tangent is annihilated by its differential. -/
lemma boundary_trace_normal_rays {Ω : Set ℂ}
    (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ) (hc : RegularEmbeddedLoop c)
    (hfront : frontier Ω = range c)
    (hD : IsClassicalRegularDomain (planeCoordinates.symm ⁻¹' Ω))
    (s : ℝ)
    (hdet : ∀ t : ℝ, ∀ hp : planeCoordinates (realLift c t) ∈
      frontier (planeCoordinates.symm ⁻¹' Ω),
      0 < det (planeCoordinates.symm (outwardNormal hD
        ⟨planeCoordinates (realLift c t), hp⟩)) (s • deriv (realLift c) t)) :
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo 0 ε,
      realLift c t + r • J0 (s • deriv (realLift c) t) ∈ Ω ∧
      realLift c t - r • J0 (s • deriv (realLift c) t) ∉ closure Ω := by
  have htrace (t : ℝ) : planeCoordinates (realLift c t) ∈
      frontier (planeCoordinates.symm ⁻¹' Ω) := by
    have hfr := planeCoordinates.symm.toHomeomorph.preimage_frontier Ω
    change planeCoordinates.symm ⁻¹' frontier Ω = frontier (planeCoordinates.symm ⁻¹' Ω) at hfr
    rw [← hfr]
    change planeCoordinates.symm (planeCoordinates (realLift c t)) ∈ frontier Ω
    rw [ContinuousLinearEquiv.symm_apply_apply, hfront]
    exact ⟨q t, rfl⟩
  intro t
  obtain ⟨U, ρ, hpU, hρ⟩ := hD.defining _ (htrace t)
  have hρdiff : DifferentiableAt ℝ ρ (planeCoordinates (realLift c t)) :=
    (hρ.regular.contDiffAt (hρ.isOpen.mem_nhds hpU)).differentiableAt (by norm_num)
  have hFdiff : DifferentiableAt ℝ (ρ ∘ planeCoordinates) (realLift c t) :=
    hρdiff.comp _ planeCoordinates.differentiableAt
  have hconst : (fun u => ρ (planeCoordinates (realLift c u))) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    have hcont := planeCoordinates.continuous.comp hc.1.continuous
    have hh := hcont.continuousAt (x := t) |>.eventually (hρ.isOpen.mem_nhds hpU)
    filter_upwards [hh] with u hu
    exact (hρ.zero_level _ hu).mp (htrace u)
  have htan : fderiv ℝ (ρ ∘ planeCoordinates) (realLift c t)
      (deriv (realLift c) t) = 0 := by
    have hcomp := hFdiff.hasFDerivAt.comp_hasDerivAt t
      (hc.1.differentiable (by norm_num) t).hasDerivAt
    exact hcomp.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hconst)
  apply outward_tangent_normal_rays hD _ _ (htrace t) ρ U hρ hpU _ (hdet t (htrace t))
  rw [map_smul, htan, smul_zero]

lemma boundary_integral_reverse {T : ℝ} {γ v : ℝ → ℂ}
    (hT : 0 ≤ T) (hcurve : C1Curve γ v T) :
    (∫ t in (0 : ℝ)..T, boundaryIntegrand (fun t => γ (T - t))
      (fun t => -v (T - t)) t) =
        -(∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t) := by
  have hmap : MapsTo (fun t => T - t) (Icc 0 T) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have he := boundary_integral_reparametrization (r := fun t => T - t)
    (α := fun _ => -1) hT hcurve (by fun_prop) continuousOn_const hmap
    (fun t ht => ((hasDerivAt_id t).const_sub T).hasDerivWithinAt)
  simp only [neg_one_smul, sub_zero, sub_self] at he
  exact he.trans (intervalIntegral.integral_symm 0 T)

lemma signed_arc_length_parametrization (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ)
    (hc : RegularEmbeddedLoop c) (Ω : Set ℂ) (A s : ℝ)
    (hs : s = 1 ∨ s = -1)
    (hnormal : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo 0 ε,
      realLift c t + r • J0 (s • deriv (realLift c) t) ∈ Ω ∧
      realLift c t - r • J0 (s • deriv (realLift c) t) ∉ closure Ω)
    (hA : A = s * (1 / 2 : ℝ) *
      ∫ t in (0 : ℝ)..1, boundaryIntegrand (realLift c) (deriv (realLift c)) t) :
    ∃ (T : ℝ) (γ v : ℝ → ℂ),
      ArcLengthParametrization c T γ v ∧ PositivelyOriented Ω γ v T ∧
      A = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ v t := by
  obtain ⟨T, γ, v, hparam, htangent, hint⟩ :=
    arc_length_parametrization_with_tangent c hc
  rcases hs with rfl | rfl
  · refine ⟨T, γ, v, hparam, ?_, ?_⟩
    · intro u hu
      obtain ⟨t, α, hα, hγ, hv⟩ := htangent u hu
      rw [hγ, hv]
      simpa only [one_smul, mem_compl_iff] using normal_rays_smul (Ω := Ω) (E := (closure Ω)ᶜ)
        hα (hnormal t)
    · rw [hint]
      simpa only [one_mul] using hA
  · refine ⟨T, (fun t => γ (T - t)), (fun t => -v (T - t)),
      arc_length_reverse hparam, ?_, ?_⟩
    · intro u hu
      have hu' : T - u ∈ Icc 0 T := by constructor <;> linarith [hu.1, hu.2]
      obtain ⟨t, α, hα, hγ, hv⟩ := htangent (T - u) hu'
      dsimp only
      rw [hγ, hv]
      simpa only [neg_one_smul, smul_neg, mem_compl_iff] using normal_rays_smul
        (Ω := Ω) (E := (closure Ω)ᶜ) hα (hnormal t)
    · rw [boundary_integral_reverse hparam.1.le hparam.2.2.1, hint]
      nlinarith [hA]



/-- The sign supplied by a genuine finite boundary display fixes the side
of every normal ray of the original covering-coordinate traversal. -/
lemma display_normal_rays {Ω : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' Ω))
    (c : Specs.D13Unified.Ch21.Collar.Circle → ℂ) (hc : RegularEmbeddedLoop c) (hfront : frontier Ω = range c)
    {O : Set (E 2)} (P : Patch 1 O) (s : PointSign)
    (hregion : P.region = intervalIsometry '' Icc (0 : ℝ) 1)
    (hmap : ∀ x, P.map x = planeIsometry (realLift c (intervalIsometry.symm x)))
    (hframe : PatchFrame hD P s) :
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Ioo 0 ε,
      realLift c t + r • J0 (s.val • deriv (realLift c) t) ∈ Ω ∧
      realLift c t - r • J0 (s.val • deriv (realLift c) t) ∉ closure Ω := by
  have hW : planeIsometry '' Ω = planeCoordinates.symm ⁻¹' Ω := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change planeCoordinates.symm (planeCoordinates z) ∈ Ω
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
    · intro hx
      exact ⟨planeCoordinates.symm x, hx, planeCoordinates.apply_symm_apply x⟩
  have hD' : IsClassicalRegularDomain (planeCoordinates.symm ⁻¹' Ω) := by
    rw [← hW]
    exact hD
  have hsign := interval_frame_signed_det_all hD c hc P s hregion hmap hframe
  apply boundary_trace_normal_rays c hc hfront hD' s.val
  intro t hp
  have hp' : planeIsometry (realLift c t) ∈ frontier (planeIsometry '' Ω) := by
    rw [hW]
    exact hp
  have hnormal : normalAt hD (realLift c t) =
      planeCoordinates.symm (outwardNormal hD' ⟨planeCoordinates (realLift c t), hp⟩) := by
    rw [normalAt_eq_actual hD _ hp']
    change planeCoordinates.symm (outwardNormal hD ⟨planeCoordinates (realLift c t), hp'⟩) = _
    congr 1
    have hncongr : ∀ (D D' : Set (E 2)) (h : D = D')
        (h₁ : IsClassicalRegularDomain D) (h₂ : IsClassicalRegularDomain D')
        (x : E 2) (hx : x ∈ frontier D) (hx' : x ∈ frontier D'),
        outwardNormal h₁ ⟨x, hx⟩ = outwardNormal h₂ ⟨x, hx'⟩ := by
      intro D D' h h₁ h₂ x hx hx'
      subst D'
      rfl
    exact hncongr _ _ hW hD hD' _ hp' hp
  have hh := hsign t
  rw [hnormal] at hh
  convert hh using 1
  simp [det]
  ring

/-- Changing the displayed ambient domain by an equality preserves the
literal interval formula, including all dependent patch indices. -/
lemma display_area_formula_full_domain {Ω : Set ℂ} {U : Set (E 2)}
    (hΩo : IsOpen Ω) (hD : IsClassicalRegularDomain (planeIsometry '' Ω))
    (hU : U = univ) (B : BoundaryDisplay hD U) (hc : B.count = 1)
    (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hmap : ∀ u, (B.patch (Fin.cast hc.symm 0)).map u =
      planeIsometry (γ (intervalIsometry.symm u)))
    {T : ℝ} (hT : 0 ≤ T)
    (hregion : (B.patch (Fin.cast hc.symm 0)).region = intervalIsometry '' Icc 0 T) :
    area Ω = (B.sign (Fin.cast hc.symm 0)).val *
      ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..T, boundaryIntegrand γ (deriv γ) t) := by
  subst U
  exact display_area_formula_literal hΩo hD B hc γ hγ hmap hT hregion

/-- The complete C¹ Jordan/Green bridge, constructed from the regular
embedding alone. The boundary display supplies its actual outward-first sign;
the traversal is reversed exactly when that sign is negative. -/
theorem green_area_bridge : green_area_bridgeType := by
  intro c hc
  obtain ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl, hC1,
    hpos, hfin, harea, hD⟩ := jordan_area c hc
  have hcoord : planeIsometry '' Ω = planeCoordinates.symm ⁻¹' Ω :=
    Equiv.image_eq_preimage_symm planeIsometry.toEquiv Ω
  have hDi : IsClassicalRegularDomain (planeIsometry '' Ω) := hcoord.symm ▸ hD
  have hdisp := D12Complex.ParametrizedBoundaryDisplay.boundary_display Ω univ hDi
    isOpen_univ (subset_univ _) 1 (fun _ => realLift c) (fun _ => 0) (fun _ => 1)
    (fun _ => univ) (lifted_boundary_curves Ω c hc hΩf)
  have hU : planeIsometry '' (univ : Set ℂ) = univ := by
    rw [image_univ, Set.range_eq_univ.mpr planeIsometry.surjective]
  obtain ⟨B, hcount, hregion, hmap, _hdomain, hframe, _hseams⟩ := hdisp
  let j : Fin B.count := Fin.cast hcount.symm 0
  have hA := display_area_formula_full_domain hΩo hDi hU B hcount (realLift c) hc.1
    (hmap 0) (show (0 : ℝ) ≤ 1 by norm_num) (hregion 0)
  have hnormal := display_normal_rays hDi c hc hΩf (B.patch j) (B.sign j)
    (hregion 0) (hmap 0) (hframe j)
  obtain ⟨T, γ, v, hparam, horient, hAcurve⟩ := signed_arc_length_parametrization
    c hc Ω (area Ω) (B.sign j).val (B.sign j).property hnormal (by
      simpa only [mul_assoc] using hA)
  refine ⟨Ω, E, T, γ, v, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl,
    hC1, hpos, hfin, harea, hparam, horient, green_boundary_area Ω hΩo hΩb hC1,
    hAcurve, ?_⟩
  exact translation_invariance T γ v hparam.1.le hparam.2.2.1 hparam.2.2.2.1

end VariationalNotes.Classical.GreenAreaBridge
