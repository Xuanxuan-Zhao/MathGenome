import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.ManifoldBoundaryDensity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.SignedCurveMultiplicity
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteManifoldBoundaryAssembly
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.TietzeExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal
namespace D12Complex.ManifoldBoundaryDensity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C06.JordanRegions.Model hiding volume
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

@[simp] theorem scalarCoordinates_apply (t : ℝ) (i : Fin 1) :
    scalarCoordinates t i = t := by
  exact OrthonormalBasis.singleton_repr t i

@[simp] theorem scalarCoordinates_symm_apply (u : E 1) :
    scalarCoordinates.symm u = u 0 := by
  have := scalarCoordinates_apply (scalarCoordinates.symm u) 0
  simpa only [LinearIsometryEquiv.apply_symm_apply] using this.symm

lemma scalarCoordinates_one : scalarCoordinates 1 = standardBasis 1 0 := by
  ext i
  fin_cases i
  simp [standardBasis, EuclideanSpace.basisFun_apply]

lemma patchCurve_contDiffOn {O : Set (E 2)} (P : Patch 1 O) :
    ContDiffOn ℝ 1 (patchCurve P) (scalarCoordinates ⁻¹' P.domain) := by
  exact complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (P.regular.comp scalarCoordinates.contDiff.contDiffOn (fun _ hx => hx))

lemma patch_scalar_compact {O : Set (E 2)} (P : Patch 1 O) :
    IsCompact (scalarCoordinates ⁻¹' closure P.region) :=
  scalarCoordinates.toHomeomorph.isCompact_preimage.mpr (D04.GeometricPatches.region_compact P)

lemma patch_parameters_nullMeasurable {O : Set (E 2)} (P : Patch 1 O) :
    NullMeasurableSet (patchParameters P) volume := by
  exact (D04.MeasureBridge.jordan_measure P.jordan).1.preimage
    scalarCoordinates.measurePreserving.quasiMeasurePreserving


@[simp] lemma complexCoordinates_symm_re (v : E 2) :
    (complexCoordinates.symm v).re = v 0 := rfl

@[simp] lemma complexCoordinates_symm_im (v : E 2) :
    (complexCoordinates.symm v).im = v 1 := rfl

lemma patch_curve_deriv {O : Set (E 2)} (P : Patch 1 O) {t : ℝ}
    (ht : scalarCoordinates t ∈ P.domain) :
    deriv (patchCurve P) t = complexCoordinates.symm
      (fderiv ℝ P.map (scalarCoordinates t) (standardBasis 1 0)) := by
  have hd := (P.regular.differentiableOn (by norm_num) _ ht).differentiableAt
    (P.open_domain.mem_nhds ht)
  have h := (complexCoordinates.symm.toContinuousLinearEquiv.hasFDerivAt.comp t
    (hd.hasFDerivAt.comp t scalarCoordinates.hasFDerivAt)).hasDerivAt
  unfold patchCurve
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
    scalarCoordinates_one, LinearEquiv.coe_toContinuousLinearEquiv'] using h.deriv

lemma patch_parameter_frontier_null {O : Set (E 2)} (P : Patch 1 O) :
    volume (scalarCoordinates ⁻¹' frontier P.region) = 0 := by
  have hz : volume (frontier P.region) = 0 :=
    D04.MeasureBridge.null_measure_zero (D04.NullCovers.contentZero_null
      ((D04.JordanRegions.jordan_iff_boundary (by norm_num) P.region
        (D04.JordanRegions.jordan_bounded P.jordan)).mp P.jordan))
  rw [scalarCoordinates.measurePreserving.measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet, hz]

lemma patch_parameter_pushforward {O : Set (E 2)} (P : Patch 1 O) (q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates.symm '' (P.map '' closure P.region))) :
    IntegrableOn (fun t => q (patchCurve P t) * deriv (patchCurve P) t) (patchParameters P) volume ∧
    Integrable (fun z => q z * patchDensity P z) μH[1] ∧
    (∫ t in patchParameters P, q (patchCurve P t) * deriv (patchCurve P) t) =
      ∫ z, q z * patchDensity P z ∂μH[1] := by
  have h := SignedCurveMultiplicity.measurable_restriction_pushforward
    (patchCurve P) (scalarCoordinates ⁻¹' P.domain)
    (scalarCoordinates ⁻¹' closure P.region) (patchParameters P)
    (P.open_domain.preimage scalarCoordinates.continuous) (patchCurve_contDiffOn P)
    (patch_scalar_compact P) (fun _ ht => P.contains ht)
    (fun _ ht => subset_closure ht) (patch_parameters_nullMeasurable P) q
    (hq.mono (by
      rintro z ⟨t, ht, rfl⟩
      exact ⟨P.map (scalarCoordinates t), ⟨scalarCoordinates t, ht, rfl⟩, rfl⟩))
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

lemma patch_density_integrable {O : Set (E 2)} (P : Patch 1 O) :
    Integrable (patchDensity P) μH[1] := by
  simpa using (patch_parameter_pushforward P (fun _ => 1) continuousOn_const).2.1

lemma complex_patch_parameter_integral {O : Set (E 2)} (P : Patch 1 O) (q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates.symm '' (P.map '' closure P.region))) :
    complexPatchIntegral P q =
      ∫ t in patchParameters P, q (patchCurve P t) * deriv (patchCurve P) t := by
  let H : E 1 → ℂ := fun u => q (complexCoordinates.symm (P.map u)) *
    complexCoordinates.symm (fderiv ℝ P.map u (standardBasis 1 0))
  have hcq : ContinuousOn (fun u => q (complexCoordinates.symm (P.map u)))
      (closure P.region) :=
    hq.comp (complexCoordinates.symm.toContinuousLinearEquiv.continuous.comp_continuousOn
      (P.regular.continuousOn.mono P.contains))
      (fun u hu => ⟨P.map u, ⟨u,hu,rfl⟩,rfl⟩)
  have hcd := (P.regular.continuousOn_fderiv_of_isOpen P.open_domain le_rfl).clm_apply
    (continuousOn_const (c := standardBasis 1 0))
  have hcH : ContinuousOn H (closure P.region) :=
    hcq.mul (complexCoordinates.symm.toContinuousLinearEquiv.continuous.comp_continuousOn
      (hcd.mono P.contains))
  have hr := D04.GeometricPatches.continuous_integrable P.jordan (Complex.continuous_re.comp_continuousOn hcH)
  have hi := D04.GeometricPatches.continuous_integrable P.jordan (Complex.continuous_im.comp_continuousOn hcH)
  have hR := D04.MeasureBridge.region_bridge (fun u : P.region => (H u).re) hr
  have hI := D04.MeasureBridge.region_bridge (fun u : P.region => (H u).im) hi
  have hs := (D04.MeasureBridge.jordan_measure P.jordan).1
  have hc_re (u : E 1) :
      weightedCoefficient P (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) u = (H u).re := by
    dsimp only [weightedCoefficient]
    rw [one_mul, (D04.Green.patch_line_coefficients P _ _ u).1]
    simp only [H, Complex.mul_re, complexCoordinates_symm_re, complexCoordinates_symm_im, neg_mul]
    rw [sub_eq_add_neg]

  have hc_im (u : E 1) :
      weightedCoefficient P (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) u = (H u).im := by
    dsimp only [weightedCoefficient]
    rw [one_mul, (D04.Green.patch_line_coefficients P _ _ u).1]
    simp only [H, Complex.mul_im, complexCoordinates_symm_re, complexCoordinates_symm_im]
    ring
  have hHr : zeroExtension (fun u : P.region => (H u).re) = P.region.indicator (fun u => (H u).re) :=
    by
    classical
    ext x
    by_cases hx : x ∈ P.region <;> simp [zeroExtension, hx]
  have hHi : zeroExtension (fun u : P.region => (H u).im) = P.region.indicator (fun u => (H u).im) :=
    by
    classical
    ext x
    by_cases hx : x ∈ P.region <;> simp [zeroExtension, hx]
  dsimp only [D04.JordanRegions.zeroExtension, D04.JordanRegions.regionIntegral] at hR hI
  rw [hHr] at hR
  rw [hHi] at hI
  have hir : IntegrableOn (fun u => (H u).re) P.region volume :=
    (integrable_indicator_iff₀ hs).mp hR.2.1
  have hii : IntegrableOn (fun u => (H u).im) P.region volume :=
    (integrable_indicator_iff₀ hs).mp hI.2.1
  have hH : IntegrableOn H P.region volume := Integrable.re_im_iff.mp ⟨hir, hii⟩
  have hvalue : complexPatchIntegral P q = ∫ u in P.region, H u := by
    unfold complexPatchIntegral patchIntegral
    simp_rw [hc_re, hc_im]
    rw [hR.2.2, hI.2.2, integral_indicator₀ hs, integral_indicator₀ hs]
    rw [mul_comm Complex.I]
    exact integral_re_add_im hH
  rw [hvalue, ← scalarCoordinates.measurePreserving.setIntegral_preimage_emb
    scalarCoordinates.toHomeomorph.measurableEmbedding H P.region]
  apply setIntegral_congr_fun₀ (patch_parameters_nullMeasurable P)
  intro t ht
  dsimp only
  rw [patch_curve_deriv P (P.contains (subset_closure ht))]
  rfl

theorem patch_pushforward :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.patch_pushforward_type := by
  intro O P q hq
  exact ⟨(patch_parameter_pushforward P q hq).2.1,
    (complex_patch_parameter_integral P q hq).trans (patch_parameter_pushforward P q hq).2.2⟩

theorem patch_frontier_null :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.patch_frontier_null_type := by
  intro O P
  have hz := SignedCurveMultiplicity.hausdorff_c1_null_image (patchCurve P)
    (scalarCoordinates ⁻¹' P.domain) (P.open_domain.preimage scalarCoordinates.continuous)
    (patchCurve_contDiffOn P) (scalarCoordinates ⁻¹' frontier P.region)
    (fun t ht => P.contains (frontier_subset_closure ht)) (patch_parameter_frontier_null P)
  convert hz using 2
  ext z
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨scalarCoordinates.symm u, ?_, ?_⟩
    · change scalarCoordinates (scalarCoordinates.symm u) ∈ frontier P.region
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hu
    · dsimp only [patchCurve]
      rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨P.map (scalarCoordinates t), ⟨scalarCoordinates t, ht, rfl⟩, rfl⟩

theorem regular_piece_differential :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.regular_piece_differential_type := by
  intro O M o P s hP u hu
  obtain ⟨U, c, hU, huU, hsource, he, hsign⟩ := hP u (subset_closure (interior_subset hu))
  have huc := hsource ⟨subset_closure (interior_subset hu), huU⟩
  have hV : IsOpen (interior P.region ∩ U) := isOpen_interior.inter hU
  have hdu : DifferentiableAt ℝ P.map u :=
    (P.regular.differentiableOn (by norm_num) _ (P.contains (subset_closure (interior_subset hu)))).differentiableAt
      (P.open_domain.mem_nhds (P.contains (subset_closure (interior_subset hu))))
  have hd : chartDifferential c u = fderiv ℝ P.map u :=
    D04.EmbeddedChart.differential_extension c huc hV ⟨hu, huU⟩
      (fun v hv => he ⟨subset_closure (interior_subset hv.2.1), hv.2.2⟩) hdu
  refine ⟨c, huc, he ⟨subset_closure (interior_subset hu), huU⟩, hd.symm, ?_, hsign ⟨u,huc⟩⟩
  rw [← hd]
  exact D04.EmbeddedChart.differential_injective c ⟨le_rfl, by norm_num⟩ huc

theorem display_pushforward :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.display_pushforward_type := by
  intro O l P s b q hq
  have hp (t : Fin l) := patch_pushforward (P t) q (hq t)
  have hi (t : Fin l) : Integrable
      (fun z => ((b t : ℂ) * ((s t).val : ℂ)) * (q z * patchDensity (P t) z)) μH[1] :=
    (hp t).1.const_mul _
  have heq : (fun z => q z * displayDensity P s b z) =
      fun z => ∑ t, ((b t : ℂ) * ((s t).val : ℂ)) * (q z * patchDensity (P t) z) := by
    funext z
    simp only [displayDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact integrable_finsetSum _ (fun t _ => hi t)
  · rw [heq, integral_finsetSum _ (fun t _ => hi t)]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_const_mul, (hp t).2]


lemma normalized_real_mul (a : ℝ) (v : ℂ) :
    ((a : ℂ) * v) / (‖(a : ℂ) * v‖ : ℂ) =
      (Real.sign a : ℂ) * (v / (‖v‖ : ℂ)) := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases ha : a = 0
  · simp [ha]
  have hav : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hvn : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  rcases lt_or_gt_of_ne ha with ha | ha
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha, Complex.ofReal_mul,
      Complex.ofReal_neg, Real.sign_of_neg ha, Complex.ofReal_neg, Complex.ofReal_one]
    field_simp
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, Complex.ofReal_mul,
      Real.sign_of_pos ha, Complex.ofReal_one, one_mul]
    field_simp

/-- A bijection of actual occurrence sets transports the actual unit tangent
sum. The velocity equation is a local proof premise here, derived from the
supplied local diffeomorphisms in the geometric specialization. -/
lemma signed_density_transport (γ η : ℝ → ℂ) (s t : Set ℝ) (φ a : ℝ → ℝ)
    (δ : ℝ) (hφ : BijOn φ s t) (he : EqOn γ (η ∘ φ) s)
    (z : ℂ)
    (hd : ∀ x ∈ s, γ x = z →
      deriv γ x = (a x : ℂ) * deriv η (φ x) ∧ a x ≠ 0 ∧ Real.sign (a x) = δ) :
    SignedCurveMultiplicity.signedDensity γ s z =
      (δ : ℂ) * SignedCurveMultiplicity.signedDensity η t z := by
  classical
  let f : SignedCurveMultiplicity.regularFiber γ s z →
      SignedCurveMultiplicity.regularFiber η t z := fun x =>
    ⟨φ x, hφ.mapsTo x.property.1,
      (he x.property.1).symm.trans x.property.2.1,
      by
        intro hzero
        exact x.property.2.2 (by rw [(hd x x.property.1 x.property.2.1).1, hzero, mul_zero])⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hφ.injOn x.property.1 y.property.1 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := hφ.surjOn y.property.1
      have hxz : γ x = z := (he hx).trans (by simpa only [Function.comp_apply, hxy] using y.property.2.1)
      have hnx : deriv γ x ≠ 0 := by
        rw [(hd x hx hxz).1, hxy]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hd x hx hxz).2.1) y.property.2.2
      exact ⟨⟨x, hx, hxz, hnx⟩, Subtype.ext hxy⟩
  let e := Equiv.ofBijective f hf
  have hu (x : SignedCurveMultiplicity.regularFiber γ s z) :
      SignedCurveMultiplicity.unitVelocity γ x =
        (δ : ℂ) * SignedCurveMultiplicity.unitVelocity η (e x) := by
    dsimp only [SignedCurveMultiplicity.unitVelocity]
    rw [(hd x x.property.1 x.property.2.1).1]
    rw [normalized_real_mul, (hd x x.property.1 x.property.2.1).2.2]
    rfl
  unfold SignedCurveMultiplicity.signedDensity
  simp_rw [hu]
  rw [tsum_mul_left]
  exact congrArg (fun w : ℂ => (δ : ℂ) * w)
    (e.tsum_eq (fun y => SignedCurveMultiplicity.unitVelocity η y))

lemma scalar_det (A : E 1 →L[ℝ] E 1) :
    A.det = (A (standardBasis 1 0)) 0 := by
  change A.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (standardBasis 1) A.toLinearMap, Matrix.det_fin_one,
    LinearMap.toMatrix_apply]
  change (standardBasis 1).repr (A (standardBasis 1 0)) 0 = _
  rfl


/-- The actual scalar parameter bijection recovered from the supplied local
reparametrization. Its derivative, not an assumed direction certificate,
determines the change of sign. -/
lemma reparam_velocity {O : Set (E 2)} (P Q : Patch 1 O) (δ : ℝ)
    (hδ : δ = 1 ∨ δ = -1)
    (h : LocalReparametrization P.region Q.region δ)
    (hmap : EqOn P.map (Q.map ∘ h.map) P.region)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region) :
    let φ : ℝ → ℝ := fun x => scalarCoordinates.symm (h.map (scalarCoordinates x))
    deriv φ t ≠ 0 ∧ Real.sign (deriv φ t) = δ ∧
      deriv (patchCurve P) t = ((deriv φ t : ℝ) : ℂ) * deriv (patchCurve Q) (φ t) := by
  let φ : ℝ → ℝ := fun x => scalarCoordinates.symm (h.map (scalarCoordinates x))
  change deriv φ t ≠ 0 ∧ _
  obtain ⟨e, hte, he, hei, heq, hsign⟩ := h.localCharts (scalarCoordinates t)
    (subset_closure (interior_subset ht))
  have hd := ((he _ hte).contDiffAt (e.open_source.mem_nhds hte)).differentiableAt (by norm_num)
  let a : ℝ := (fderiv ℝ e (scalarCoordinates t) (standardBasis 1 0)) 0
  have hder : HasDerivAt φ a t := by
    have hD := (scalarCoordinates.symm.hasFDerivAt.comp t
      (hd.hasFDerivAt.comp t scalarCoordinates.hasFDerivAt)).hasDerivAt
    have hN : ∀ᶠ x in 𝓝 t,
        scalarCoordinates x ∈ interior P.region ∩ e.source :=
      ((isOpen_interior.inter e.open_source).preimage scalarCoordinates.continuous).mem_nhds ⟨ht, hte⟩
    have hE : φ =ᶠ[𝓝 t] fun x => scalarCoordinates.symm (e (scalarCoordinates x)) := by
      filter_upwards [hN] with x hx
      exact congrArg scalarCoordinates.symm (heq ⟨subset_closure (interior_subset hx.1), hx.2⟩).symm
    apply HasDerivAt.congr_of_eventuallyEq _ hE
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, scalarCoordinates_one,
      LinearIsometryEquiv.coe_coe, LinearIsometryEquiv.coe_coe'', scalarCoordinates_symm_apply, a] using hD
  have ha : Real.sign a = δ := by
    have := hsign _ hte
    rwa [scalar_det] at this
  have hane : a ≠ 0 := by
    intro hzero
    rw [hzero, Real.sign_zero] at ha
    rcases hδ with hδ | hδ <;> norm_num [hδ] at ha
  refine ⟨hder.deriv ▸ hane, hder.deriv ▸ ha, ?_⟩
  have hqt : scalarCoordinates (φ t) ∈ Q.domain := by
    dsimp only [φ]
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact Q.contains (subset_closure (h.bijective.mapsTo (interior_subset ht)))
  have hQd := ((patchCurve_contDiffOn Q).differentiableOn (by norm_num) _ hqt).differentiableAt
    ((Q.open_domain.preimage scalarCoordinates.continuous).mem_nhds hqt)
  have hv : patchCurve P =ᶠ[𝓝 t] (patchCurve Q ∘ φ) := by
    filter_upwards [(isOpen_interior.preimage scalarCoordinates.continuous).mem_nhds ht] with x hx
    dsimp only [patchCurve, Function.comp_apply, φ]
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact congrArg complexCoordinates.symm (hmap (interior_subset hx))
  calc
    deriv (patchCurve P) t = a • deriv (patchCurve Q) (φ t) :=
      hv.deriv_eq.trans (hQd.hasDerivAt.scomp t hder).deriv
    _ = ((deriv φ t : ℝ) : ℂ) * deriv (patchCurve Q) (φ t) := by
      rw [hder.deriv]
      simp [Complex.real_smul]


theorem patch_density_reparam {O : Set (E 2)} (P Q : Patch 1 O) (δ : ℝ)
    (hδ : δ = 1 ∨ δ = -1) (h : LocalReparametrization P.region Q.region δ)
    (hmap : EqOn P.map (Q.map ∘ h.map) P.region) :
    patchDensity P =ᵐ[μH[1]] fun z => (δ : ℂ) * patchDensity Q z := by
  let φ : ℝ → ℝ := fun x => scalarCoordinates.symm (h.map (scalarCoordinates x))
  have hφ : BijOn φ (patchParameters P) (patchParameters Q) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change scalarCoordinates (scalarCoordinates.symm (h.map (scalarCoordinates x))) ∈ Q.region
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact h.bijective.mapsTo hx
    · intro x hx y hy hxy
      apply scalarCoordinates.injective
      apply h.bijective.injOn hx hy
      have := congrArg scalarCoordinates hxy
      simpa only [φ, LinearIsometryEquiv.apply_symm_apply] using this
    · intro y hy
      obtain ⟨u, hu, huy⟩ := h.bijective.surjOn hy
      refine ⟨scalarCoordinates.symm u, ?_, ?_⟩
      · change scalarCoordinates (scalarCoordinates.symm u) ∈ P.region
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hu
      · apply scalarCoordinates.injective
        dsimp only [φ]
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, huy]
  have he : EqOn (patchCurve P) (patchCurve Q ∘ φ) (patchParameters P) := by
    intro x hx
    dsimp only [patchCurve, Function.comp_apply, φ]
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact congrArg complexCoordinates.symm (hmap hx)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (patch_frontier_null P)] with z hz
  apply signed_density_transport (patchCurve P) (patchCurve Q)
    (patchParameters P) (patchParameters Q) φ (deriv φ) δ hφ he z
  intro x hx hxz
  have hi : scalarCoordinates x ∈ interior P.region := by
    by_contra hn
    have hf : scalarCoordinates x ∈ frontier P.region :=
      (mem_frontier_iff_notMem_interior (show scalarCoordinates x ∈ P.region from hx)).mpr hn
    exact hz ⟨P.map (scalarCoordinates x), ⟨scalarCoordinates x, hf, rfl⟩, hxz⟩
  have hv := reparam_velocity P Q δ hδ h hmap x hi
  exact ⟨hv.2.2, hv.1, hv.2.1⟩

lemma regular_piece_velocity_ne_zero {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region) :
    deriv (patchCurve P) t ≠ 0 := by
  obtain ⟨c, huc, _, _, hinj, _⟩ := regular_piece_differential o P s hP _ ht
  rw [patch_curve_deriv P (P.contains (subset_closure (interior_subset ht)))]
  intro hh
  have hv : fderiv ℝ P.map (scalarCoordinates t) (standardBasis 1 0) = 0 :=
    complexCoordinates.symm.injective (hh.trans (map_zero _).symm)
  exact (standardBasis 1).ne_zero 0 (hinj (hv.trans (map_zero _).symm))

/-- At any original interior occurrence off its supplied self-intersection
seams, the actual fiber consists of exactly that parameter. -/
lemma regular_piece_fiber {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v →
      P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z) :
    SignedCurveMultiplicity.regularFiber (patchCurve P) (patchParameters P)
      (patchCurve P t) = {t} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply scalarCoordinates.injective
    by_contra hne
    have hval : P.map (scalarCoordinates t) = P.map (scalarCoordinates x) :=
      complexCoordinates.symm.injective hx.2.1.symm
    exact hz (hself _ (interior_subset ht) _ hx.1 (Ne.symm hne) hval)
  · intro hx
    subst x
    exact ⟨(show scalarCoordinates t ∈ P.region from interior_subset ht), rfl, regular_piece_velocity_ne_zero o P s hP t ht⟩

lemma regular_piece_density {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v →
      P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z) :
    patchDensity P (patchCurve P t) = SignedCurveMultiplicity.unitVelocity (patchCurve P) t ∧
      ‖patchDensity P (patchCurve P t)‖ = 1 := by
  have hf := regular_piece_fiber o P s hP Z hself t ht hz
  have heq : patchDensity P (patchCurve P t) = SignedCurveMultiplicity.unitVelocity (patchCurve P) t := by
    unfold patchDensity SignedCurveMultiplicity.signedDensity
    rw [hf]
    simp
  exact ⟨heq, heq ▸ SignedCurveMultiplicity.norm_unitVelocity _ _
    (regular_piece_velocity_ne_zero o P s hP t ht)⟩


lemma regular_piece_closed_image {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) : P.map '' closure P.region ⊆ M := by
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨U,c,hU,huU,hs,he,hsg⟩ := hP u hu
  rw [he ⟨hu,huU⟩]
  exact (c.map_source (hs ⟨hu,huU⟩)).1

lemma patch_reparam_closed_images {O : Set (E 2)} (P Q : Patch 1 O) (δ : ℝ)
    (h : LocalReparametrization P.region Q.region δ)
    (hmap : EqOn P.map (Q.map ∘ h.map) P.region) :
    P.map '' closure P.region = Q.map '' closure Q.region := by
  have htrace : P.map '' P.region = Q.map '' Q.region := by
    rw [hmap.image_eq, image_comp, h.bijective.image_eq]
  rw [image_closure_of_isCompact (D04.GeometricPatches.region_compact P)
      (P.regular.continuousOn.mono P.contains),
    image_closure_of_isCompact (D04.GeometricPatches.region_compact Q)
      (Q.regular.continuousOn.mono Q.contains), htrace]

lemma occurrence_sum {q l p : ℕ} (m : Fin q → ℕ)
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
    (f : ((j : Fin q) × Fin (m j)) → ℂ) :
    (∑ j, ∑ t, f ⟨j,t⟩) = (∑ t, f (e (Sum.inl t))) +
      ∑ i, (f (e (Sum.inr (i,false))) + f (e (Sum.inr (i,true)))) := by
  rw [← Fintype.sum_sigma, ← e.sum_comp f, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, add_comm]

lemma paired_density_cancellation {O : Set (E 2)} (P Q : Patch 1 O)
    (s t : PointSign) (δ : ℝ) (hδ : δ = 1 ∨ δ = -1)
    (h : LocalReparametrization P.region Q.region δ)
    (hmap : EqOn P.map (Q.map ∘ h.map) P.region) (hsign : s.val * δ = -t.val) :
    ∀ᵐ z ∂(μH[1] : Measure ℂ),
      (s.val : ℂ) * patchDensity P z + (t.val : ℂ) * patchDensity Q z = 0 := by
  have hc : (s.val : ℂ) * (δ : ℂ) = -(t.val : ℂ) := by exact_mod_cast hsign
  filter_upwards [patch_density_reparam P Q δ hδ h hmap] with z hz
  rw [hz, ← mul_assoc, hc]
  ring

theorem assembly_density :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.assembly_density_type := by
  intro q l p O A
  have ho (t : Fin l) := patch_density_reparam
    ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)
    (A.outerPatch t) (A.deltaOut t) (A.deltaOut_sign t) (A.outerReparam t) (A.outer_match t).1
  have hi (i : Fin p) := paired_density_cancellation
    ((A.display (A.enumerate (Sum.inr (i,false))).1).patch (A.enumerate (Sum.inr (i,false))).2)
    ((A.display (A.enumerate (Sum.inr (i,true))).1).patch (A.enumerate (Sum.inr (i,true))).2)
    ((A.display (A.enumerate (Sum.inr (i,false))).1).sign (A.enumerate (Sum.inr (i,false))).2)
    ((A.display (A.enumerate (Sum.inr (i,true))).1).sign (A.enumerate (Sum.inr (i,true))).2)
    (A.deltaPair i) (A.deltaPair_sign i) (A.pairReparam i)
    (A.pair_match i).1 (A.pair_match i).2
  filter_upwards [ae_all_iff.mpr ho, ae_all_iff.mpr hi] with z hzo hzi
  change (∑ j, ∑ t, (((A.display j).sign t).val : ℂ) *
    patchDensity ((A.display j).patch t) z) = _
  rw [occurrence_sum (fun j => (A.display j).count) A.enumerate
    (fun k => (((A.display k.1).sign k.2).val : ℂ) * patchDensity ((A.display k.1).patch k.2) z)]
  have hp := Finset.sum_eq_zero (s := Finset.univ) (fun i _ => hzi i)
  rw [hp, add_zero]
  unfold outerDensity displayDensity
  apply Finset.sum_congr rfl
  intro t _
  rw [hzo t, (A.outer_match t).2.2]
  have hc : (((A.display (A.enumerate (Sum.inl t)).1).sign
      (A.enumerate (Sum.inl t)).2).val : ℂ) * (A.deltaOut t : ℂ) = (A.outerSign t).val := by
    exact_mod_cast (A.outer_match t).2.1
  rw [← mul_assoc, hc]
  simp


lemma pointSignInt_cast (s : PointSign) : (pointSignInt s : ℝ) = s.val := by
  rcases s.property with hs | hs
  · norm_num [pointSignInt, hs]
  · norm_num [pointSignInt, hs]

lemma outerPatchChain_integral {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1) :
    patchChainIntegral ω (outerPatchChain A) =
      ∑ t, A.outerMultiplicity t • ((A.outerSign t).val * patchIntegral (A.outerPatch t) (fun _ => 1) ω) := by
  simp only [outerPatchChain, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [patchChainIntegral, Finsupp.liftAddHom_apply_single]
  change (A.outerMultiplicity t * pointSignInt (A.outerSign t)) •
    patchIntegral (A.outerPatch t) (fun _ => 1) ω = _
  simp only [Int.cast_mul, pointSignInt_cast, zsmul_eq_mul]
  ring

lemma complex_outer_chain_integral {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f : ℂ → ℂ) :
    (∑ t, (A.outerMultiplicity t : ℂ) * ((A.outerSign t).val : ℂ) *
      complexPatchIntegral (A.outerPatch t) f) =
    (patchChainIntegral
      (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
        (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
    Complex.I * (patchChainIntegral
      (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
        (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ) := by
  rw [outerPatchChain_integral, outerPatchChain_integral]
  simp only [zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold complexPatchIntegral
  ring

lemma assembly_original_image {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (j : Fin q) (t : Fin (A.display j).count) :
    ((A.display j).patch t).map '' closure ((A.display j).patch t).region ⊆ ⋃ k, (A.piece k).carrier := by
  intro x hx
  exact mem_iUnion.mpr ⟨j, (regular_piece_closed_image _ _ _ ((A.display j).regular t) hx).1⟩

lemma assembly_outer_image {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (t : Fin l) :
    (A.outerPatch t).map '' closure (A.outerPatch t).region ⊆ ⋃ j, (A.piece j).carrier := by
  rw [← patch_reparam_closed_images
    ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)
    (A.outerPatch t) (A.deltaOut t) (A.outerReparam t) (A.outer_match t).1]
  exact assembly_original_image A _ _

lemma original_pushforward {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))) :
    Integrable (fun z => f z * originalDensity A z) μH[1] ∧
    (∫ z, f z * originalDensity A z ∂μH[1]) =
      ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) * complexPatchIntegral ((A.display j).patch t) f := by
  have hp (j : Fin q) (t : Fin (A.display j).count) :=
    patch_pushforward ((A.display j).patch t) f (hf.mono (image_mono (assembly_original_image A j t)))
  have hi (j : Fin q) (t : Fin (A.display j).count) : Integrable
      (fun z => (((A.display j).sign t).val : ℂ) * (f z * patchDensity ((A.display j).patch t) z)) μH[1] :=
    (hp j t).1.const_mul _
  have heq : (fun z => f z * originalDensity A z) =
      fun z => ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) * (f z * patchDensity ((A.display j).patch t) z) := by
    funext z
    simp only [originalDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun t _ => hi j t)), ?_⟩
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun t _ => hi j t))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun t _ => hi j t)]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_const_mul, ← (hp j t).2]

theorem assembly_pushforward :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.assembly_pushforward_type := by
  intro q l p O A f hf
  have ho := display_pushforward A.outerPatch A.outerSign A.outerMultiplicity f
    (fun t => hf.mono (image_mono (assembly_outer_image A t)))
  have hi := original_pushforward A f hf
  have he : (fun z => f z * originalDensity A z) =ᵐ[μH[1]] (fun z => f z * outerDensity A z) :=
    (assembly_density A).mono (fun z hz => congrArg (fun d => f z * d) hz)
  exact ⟨ho.1, (integral_congr_ae he.symm).trans hi.2, ho.2.symm,
    ho.2.symm.trans (complex_outer_chain_integral A f)⟩


theorem assembly_c1 :
    Specs.D12Complex.Ch04.ManifoldBoundaryDensity.assembly_c1_type := by
  intro q l p O A U f hU hKU hf
  exact assembly_pushforward A f (hf.continuousOn.mono hKU)

lemma assembly_density_integrable {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) :
    Integrable (outerDensity A) μH[1] ∧ AEStronglyMeasurable (outerDensity A) μH[1] := by
  have hi : Integrable (outerDensity A) μH[1] := by
    simpa using (assembly_pushforward A (fun _ => 1) continuousOn_const).1
  exact ⟨hi, hi.aestronglyMeasurable⟩

lemma boundary_seams_finite (Z : Seams 2) (hZ : ∀ i, Z.dim i < 1) : Z.carrier.Finite := by
  apply Set.finite_iUnion
  intro i
  have hd : Z.dim i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hZ i))
  haveI : Subsingleton (E (Z.dim i)) := by rw [hd]; infer_instance
  exact (Set.toFinite (Z.parameter i)).image _

lemma regular_display_has_integral {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D : RegularDisplay O M o)
    (hM : IsCompact M) (hMO : M ⊆ O)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hω : Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O ω) :
    Specs.D04.C15.GeneralizedStokes.Model.HasPositiveIntegral o
      (Specs.D04.C15.GeneralizedStokes.Model.tangentRestriction 1 1 M ω)
      (∑ t, (D.sign t).val * patchIntegral (D.patch t) (fun _ => 1) ω) := by
  exact D04.ManifoldBoundaryAssembly.regular_display_integral o hM hMO
    D.patch D.sign D.regular D.seams D.lower D.self_intersection D.intersection D.cover ω hω

lemma regular_display_independent {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D F : RegularDisplay O M o)
    (hM : IsCompact M) (hMO : M ⊆ O)
    (ω : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1)
    (hω : Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O ω) :
    (∑ t, (D.sign t).val * patchIntegral (D.patch t) (fun _ => 1) ω) =
      ∑ t, (F.sign t).val * patchIntegral (F.patch t) (fun _ => 1) ω :=
  D04Stokes.positive_integral_unique o _
    (regular_display_has_integral o D hM hMO ω hω)
    (regular_display_has_integral o F hM hMO ω hω)

lemma circulation_continuous (O : Set (E 2)) (hO : IsOpen O) (P Q : E 2 → ℝ)
    (hP : ContinuousOn P O) (hQ : ContinuousOn Q O) :
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O (circulationForm P Q) := by
  refine ⟨hO, fun I => ?_⟩
  change ContinuousOn (fun x =>
    (circulationForm P Q x) (fun j => standardBasis 2
      (Specs.D04.C13.NormalizedFormsAndWedge.Model.indexTuple I j))) O
  simp only [circulationForm, AlternatingMap.add_apply, AlternatingMap.smul_apply, smul_eq_mul]
  exact (hP.mul continuousOn_const).add (hQ.mul continuousOn_const)

lemma complexPatchIntegral_congr {O : Set (E 2)} (P : Patch 1 O) (f g : ℂ → ℂ)
    (hfg : EqOn f g (complexCoordinates.symm '' (P.map '' P.region))) :
    complexPatchIntegral P f = complexPatchIntegral P g := by
  unfold complexPatchIntegral
  apply congrArg₂ (fun r i : ℝ => (r : ℂ) + Complex.I * (i : ℂ))
  all_goals
    unfold patchIntegral
    apply congrArg (fun H : P.region → ℝ => regionIntegral H)
    funext u
    dsimp only [weightedCoefficient, coefficient, Specs.D04.C13.PullbackCalculus.Model.pullback,
      circulationForm]
    rw [hfg ⟨P.map u, ⟨u, u.property, rfl⟩, rfl⟩]

/-- Arbitrary regular displays are compared through the actual manifold
integral. Tietze extends only the two continuous coefficient values; no
comparison of original cycles is assumed. -/
lemma regular_display_complex_independent {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D F : RegularDisplay O M o)
    (hO : IsOpen O) (hM : IsCompact M) (hMO : M ⊆ O) (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' M)) :
    (∑ t, ((D.sign t).val : ℂ) * complexPatchIntegral (D.patch t) f) =
      ∑ t, ((F.sign t).val : ℂ) * complexPatchIntegral (F.patch t) f := by
  have hc : ContinuousOn (fun x => f (complexCoordinates.symm x)) M :=
    hf.comp complexCoordinates.symm.toContinuousLinearEquiv.continuous.continuousOn
      (mapsTo_image _ _)
  let fr : C(M,ℝ) := ⟨fun x => (f (complexCoordinates.symm x)).re,
    (Complex.continuous_re.comp_continuousOn hc).domRestrict⟩
  let fi : C(M,ℝ) := ⟨fun x => (f (complexCoordinates.symm x)).im,
    (Complex.continuous_im.comp_continuousOn hc).domRestrict⟩
  obtain ⟨R, hR⟩ := fr.exists_restrict_eq hM.isClosed
  obtain ⟨S, hS⟩ := fi.exists_restrict_eq hM.isClosed
  let g : ℂ → ℂ := fun z => ⟨R (complexCoordinates z), S (complexCoordinates z)⟩
  have hfg : EqOn f g (complexCoordinates.symm '' M) := by
    rintro z ⟨x,hx,rfl⟩
    have hr := congrArg (fun H : C(M,ℝ) => H ⟨x,hx⟩) hR
    have hs := congrArg (fun H : C(M,ℝ) => H ⟨x,hx⟩) hS
    apply Complex.ext
    · dsimp only [g]
      rw [LinearEquiv.apply_symm_apply]
      exact hr.symm
    · dsimp only [g]
      rw [LinearEquiv.apply_symm_apply]
      exact hs.symm
  have hD (t : Fin D.count) : complexPatchIntegral (D.patch t) f = complexPatchIntegral (D.patch t) g :=
    complexPatchIntegral_congr _ _ _ (hfg.mono (image_mono
      ((image_mono subset_closure).trans (regular_piece_closed_image o _ _ (D.regular t)))))
  have hF (t : Fin F.count) : complexPatchIntegral (F.patch t) f = complexPatchIntegral (F.patch t) g :=
    complexPatchIntegral_congr _ _ _ (hfg.mono (image_mono
      ((image_mono subset_closure).trans (regular_piece_closed_image o _ _ (F.regular t)))))
  simp_rw [hD, hF]
  have hreal := regular_display_independent o D F hM hMO
    (circulationForm R (fun x => -S x))
    (circulation_continuous O hO R (fun x => -S x) R.continuous.continuousOn S.continuous.neg.continuousOn)
  have himag := regular_display_independent o D F hM hMO
    (circulationForm S R)
    (circulation_continuous O hO S R S.continuous.continuousOn R.continuous.continuousOn)
  have hgre (x : E 2) : (g (complexCoordinates.symm x)).re = R x := by
    dsimp only [g]
    rw [LinearEquiv.apply_symm_apply]
  have hgim (x : E 2) : (g (complexCoordinates.symm x)).im = S x := by
    dsimp only [g]
    rw [LinearEquiv.apply_symm_apply]
  apply Complex.ext
  · simpa [complexPatchIntegral, hgre, hgim] using hreal
  · simpa [complexPatchIntegral, hgre, hgim] using himag


lemma complexCoordinates_symm_norm (v : E 2) : ‖complexCoordinates.symm v‖ = ‖v‖ := by
  rw [Complex.norm_def, D04.norm_coordinates, Fin.sum_univ_two]
  simp only [Complex.normSq_apply, complexCoordinates_symm_re, complexCoordinates_symm_im]
  congr 1 <;> ring

lemma signed_chart_unit_positive {M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (c : EmbeddedChart 1 1 2 M)
    (u : E 1) (hu : u ∈ c.source) (s : PointSign)
    (hs : chartSign o.atPoint c u hu = s.val) :
    0 < (o.atPoint (c.toFun u) (c.map_source hu).1).someVector
      (fun i => (s.val / ‖chartDifferential c u (standardBasis 1 0)‖) •
        tangentChartMap c u hu (standardBasis 1 i)) := by
  have hn : 0 < ‖chartDifferential c u (standardBasis 1 0)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact (standardBasis 1).ne_zero 0
      (D04.EmbeddedChart.differential_injective c o.manifold.1 hu (hz.trans (map_zero _).symm))
  change Real.sign (chartCoefficient o.atPoint c u hu) = s.val at hs
  have hc : chartCoefficient o.atPoint c u hu ≠ 0 := by
    intro hz
    rw [hz, Real.sign_zero] at hs
    rcases s.property with hp | hp <;> norm_num [hp] at hs
  have hp := Real.sign_mul_pos_of_ne_zero (chartCoefficient o.atPoint c u hu) hc
  rw [hs] at hp
  rw [AlternatingMap.map_smul_univ]
  simp only [Fin.prod_univ_one, smul_eq_mul]
  change 0 < (s.val / ‖chartDifferential c u (standardBasis 1 0)‖) *
    chartCoefficient o.atPoint c u hu
  rw [div_mul_eq_mul_div]
  exact div_pos hp hn

/-- The signed actual unit velocity at each interior occurrence is precisely
the induced positive chart tangent, with positivity checked against the actual
chosen tangent orientation. -/
lemma regular_piece_oriented_unit {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region) :
    ∃ (c : EmbeddedChart 1 1 2 M) (hu : scalarCoordinates t ∈ c.source),
      P.map (scalarCoordinates t) = c.toFun (scalarCoordinates t) ∧
      chartSign o.atPoint c (scalarCoordinates t) hu = s.val ∧
      (s.val : ℂ) * SignedCurveMultiplicity.unitVelocity (patchCurve P) t =
        complexCoordinates.symm
          ((s.val / ‖chartDifferential c (scalarCoordinates t) (standardBasis 1 0)‖) •
            chartDifferential c (scalarCoordinates t) (standardBasis 1 0)) ∧
      0 < (o.atPoint (c.toFun (scalarCoordinates t)) (c.map_source hu).1).someVector
        (fun i => (s.val / ‖chartDifferential c (scalarCoordinates t) (standardBasis 1 0)‖) •
          tangentChartMap c (scalarCoordinates t) hu (standardBasis 1 i)) := by
  obtain ⟨c,hu,he,hd,hinj,hs⟩ := regular_piece_differential o P s hP _ ht
  refine ⟨c,hu,he,hs,?_,signed_chart_unit_positive o c _ hu s hs⟩
  unfold SignedCurveMultiplicity.unitVelocity
  rw [patch_curve_deriv P (P.contains (subset_closure (interior_subset ht))), hd,
    complexCoordinates_symm_norm, map_smul]
  simp only [Complex.real_smul, Complex.ofReal_div]
  ring

lemma regular_piece_multiplicity {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Set (E 2))
    (hself : ∀ u ∈ P.region, ∀ v ∈ P.region, u ≠ v → P.map u = P.map v → P.map u ∈ Z)
    (t : ℝ) (ht : scalarCoordinates t ∈ interior P.region)
    (hz : P.map (scalarCoordinates t) ∉ Z) :
    SignedCurveMultiplicity.multiplicity (patchCurve P) (patchParameters P) (patchCurve P t) = 1 := by
  unfold SignedCurveMultiplicity.multiplicity
  rw [regular_piece_fiber o P s hP Z hself t ht hz]
  simp

/-- Off the actual displayed seams, every manifold point has exactly one
original displayed parameter occurrence, including arbitrary Jordan regions. -/
lemma regular_display_occurrence {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (D : RegularDisplay O M o)
    (x : E 2) (hx : x ∈ M) (hz : x ∉ D.seams.carrier) :
    ∃! a : ((t : Fin D.count) × (D.patch t).region), (D.patch a.1).map a.2 = x := by
  obtain hcover | hseam := D.cover hx
  · obtain ⟨t,u,hu,hux⟩ := mem_iUnion.mp hcover
    refine ⟨⟨t,⟨u,hu⟩⟩,hux,?_⟩
    rintro ⟨r,v⟩ hv
    have hrt : r = t := by
      by_contra hne
      exact hz (D.intersection r t hne ⟨⟨v,v.property,hv⟩,⟨u,hu,hux⟩⟩)
    subst r
    have hvu : v.val = u := by
      by_contra hne
      exact hz (hv ▸ D.self_intersection t v v.property u hu hne (hv.trans hux.symm))
    have hvu' : v = (⟨u,hu⟩ : (D.patch t).region) := Subtype.ext hvu
    cases hvu'
    rfl
  · exact (hz hseam).elim

lemma boundary_seams_null (Z : Seams 2) (hZ : ∀ i, Z.dim i < 1) :
    (μH[1] : Measure ℂ) (complexCoordinates.symm '' Z.carrier) = 0 := by
  letI : NullSingletonClass (μH[1] : Measure ℂ) :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff ℂ zero_lt_one
  exact ((boundary_seams_finite Z hZ).image complexCoordinates.symm).countable.measure_zero _


lemma geometric_outer_density {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) :
    geometricOuterDensity A =ᵐ[μH[1]] outerDensity A := by
  have ho (t : Fin l) := patch_density_reparam
    ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)
    (A.outerPatch t) (A.deltaOut t) (A.deltaOut_sign t) (A.outerReparam t) (A.outer_match t).1
  filter_upwards [ae_all_iff.mpr ho] with z hz
  unfold geometricOuterDensity outerDensity displayDensity
  apply Finset.sum_congr rfl
  intro t _
  rw [hz t, (A.outer_match t).2.2]
  have hc : (((A.display (A.enumerate (Sum.inl t)).1).sign
      (A.enumerate (Sum.inl t)).2).val : ℂ) * (A.deltaOut t : ℂ) = (A.outerSign t).val := by
    exact_mod_cast (A.outer_match t).2.1
  rw [← mul_assoc, hc]
  simp

lemma original_geometric_outer_density {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) :
    originalDensity A =ᵐ[μH[1]] geometricOuterDensity A :=
  (assembly_density A).trans (geometric_outer_density A).symm

lemma geometric_assembly_pushforward {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))) :
    GeometricAssemblyDictionary A f := by
  have h := assembly_pushforward A f hf
  have he : (fun z => f z * geometricOuterDensity A z) =ᵐ[μH[1]] (fun z => f z * outerDensity A z) :=
    (geometric_outer_density A).mono (fun z hz => congrArg (fun d => f z * d) hz)
  exact ⟨h.1.congr he.symm, (integral_congr_ae he).trans h.2.1,
    (integral_congr_ae he).trans h.2.2.1, (integral_congr_ae he).trans h.2.2.2⟩

lemma geometric_assembly_c1 {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (U : Set ℂ) (f : ℂ → ℂ) (_hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : GeometricAssemblyDictionary A f :=
  geometric_assembly_pushforward A f (hf.continuousOn.mono hKU)

lemma geometric_outer_integrable {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) :
    Integrable (geometricOuterDensity A) μH[1] ∧ AEStronglyMeasurable (geometricOuterDensity A) μH[1] := by
  have hi := (assembly_density_integrable A).1.congr (geometric_outer_density A).symm
  exact ⟨hi,hi.aestronglyMeasurable⟩

namespace Definitions

abbrev scalarCoordinates := @D12Complex.ManifoldBoundaryDensity.scalarCoordinates
abbrev patchCurve := @D12Complex.ManifoldBoundaryDensity.patchCurve
abbrev patchParameters := @D12Complex.ManifoldBoundaryDensity.patchParameters
abbrev patchDensity := @D12Complex.ManifoldBoundaryDensity.patchDensity
abbrev complexPatchIntegral := @D12Complex.ManifoldBoundaryDensity.complexPatchIntegral
abbrev displayDensity := @D12Complex.ManifoldBoundaryDensity.displayDensity
abbrev RegularDisplay := @D12Complex.ManifoldBoundaryDensity.RegularDisplay
abbrev PlanarAssembly := @D12Complex.ManifoldBoundaryDensity.PlanarAssembly
abbrev originalDensity := @D12Complex.ManifoldBoundaryDensity.originalDensity
abbrev outerDensity := @D12Complex.ManifoldBoundaryDensity.outerDensity
abbrev pointSignInt := @D12Complex.ManifoldBoundaryDensity.pointSignInt
abbrev outerPatchChain := @D12Complex.ManifoldBoundaryDensity.outerPatchChain
abbrev AssemblyDictionary := @D12Complex.ManifoldBoundaryDensity.AssemblyDictionary

abbrev geometricOuterDensity := @D12Complex.ManifoldBoundaryDensity.geometricOuterDensity

abbrev GeometricAssemblyDictionary := @D12Complex.ManifoldBoundaryDensity.GeometricAssemblyDictionary

end Definitions

end D12Complex.ManifoldBoundaryDensity
