import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.ComplexGreenBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C12.IntegrationByPartsAndGreenIdentities
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FiniteManifoldBoundaryAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C06.JordanRegions.Model

lemma symm_basis_zero : planeIsometry.symm (standardBasis 2 0) = 1 := by
  apply planeIsometry.injective
  ext i
  fin_cases i <;> simp [planeIsometry, standardBasis, Complex.orthonormalBasisOneI]

lemma symm_basis_one : planeIsometry.symm (standardBasis 2 1) = Complex.I := by
  apply planeIsometry.injective
  ext i
  fin_cases i <;> simp [planeIsometry, standardBasis, Complex.orthonormalBasisOneI]

lemma partial_zero (u : ℂ → ℝ) (z : ℂ) :
    scalarPartialDerivative (u ∘ planeIsometry.symm) (planeIsometry z) 0 =
      D12Complex.partialX u z := by
  change deriv (fun t : ℝ => u (planeIsometry.symm (planeIsometry z + t • standardBasis 2 0))) 0 = _
  simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply, symm_basis_zero]
  simp [D12Complex.partialX]

lemma partial_one (u : ℂ → ℝ) (z : ℂ) :
    scalarPartialDerivative (u ∘ planeIsometry.symm) (planeIsometry z) 1 =
      D12Complex.partialY u z := by
  change deriv (fun t : ℝ => u (planeIsometry.symm (planeIsometry z + t • standardBasis 2 1))) 0 = _
  simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply, symm_basis_one]
  simp [D12Complex.partialY, Complex.real_smul]

lemma contDiffOn_transport {n : ℕ∞ω} {U : Set ℂ} {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ n u U) :
    ContDiffOn ℝ n (u ∘ planeIsometry.symm) (planeIsometry '' U) := by
  apply hu.comp planeIsometry.symm.toContinuousLinearEquiv.contDiff.contDiffOn
  rintro _ ⟨z, hz, rfl⟩
  simpa using hz

lemma closure_image (D : Set ℂ) :
    closure (planeIsometry '' D) = planeIsometry '' closure D :=
  planeIsometry.toHomeomorph.image_closure D |>.symm

lemma laplacian_transport (U : Set ℂ) (u : ℂ → ℝ) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (z : ℂ) (hz : z ∈ U) :
    laplacian (u ∘ planeIsometry.symm) (planeIsometry z) =
      D12Complex.coordinateLaplacian u z := by
  have hEU : IsOpen (planeIsometry '' U) := planeIsometry.toHomeomorph.isOpenMap U hU
  have hCr := (D04.crOn_iff_contDiffOn 2 _ _ hEU).mpr (contDiffOn_transport hu)
  change D04.laplacian (u ∘ planeIsometry.symm) (planeIsometry z) = _
  rw [D04.laplacian_coordinates _ _ _ hEU hCr (mem_image_of_mem _ hz)]
  rw [Fin.sum_univ_two]
  have h0 : (fun x => scalarPartialDerivative (u ∘ planeIsometry.symm) x 0) =
      D12Complex.partialX u ∘ planeIsometry.symm := by
    funext x
    simpa only [LinearIsometryEquiv.apply_symm_apply, Function.comp_apply] using partial_zero u (planeIsometry.symm x)
  have h1 : (fun x => scalarPartialDerivative (u ∘ planeIsometry.symm) x 1) =
      D12Complex.partialY u ∘ planeIsometry.symm := by
    funext x
    simpa only [LinearIsometryEquiv.apply_symm_apply, Function.comp_apply] using partial_one u (planeIsometry.symm x)
  change scalarPartialDerivative (fun y => scalarPartialDerivative (u ∘ planeIsometry.symm) y 0) (planeIsometry z) 0 +
    scalarPartialDerivative (fun y => scalarPartialDerivative (u ∘ planeIsometry.symm) y 1) (planeIsometry z) 1 = _
  rw [h0, h1, partial_zero, partial_one]
  rfl

lemma gradient_transport (u : ℂ → ℝ) (z : ℂ) (hu : DifferentiableAt ℝ u z) :
    scalarGradient (u ∘ planeIsometry.symm) (planeIsometry z) =
      planeIsometry (gradient u z) := by
  apply ext_inner_right ℝ
  intro w
  change inner ℝ (gradient (u ∘ planeIsometry.symm) (planeIsometry z)) w = _
  rw [inner_gradient_left]
  rw [fderiv_comp _ (by simpa using hu) planeIsometry.symm.differentiableAt]
  have he : fderiv ℝ (⇑planeIsometry.symm) (planeIsometry z) =
      planeIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    planeIsometry.symm.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.symm_apply_apply]

  conv_rhs => rw [← planeIsometry.apply_symm_apply w]
  rw [planeIsometry.inner_map_map, inner_gradient_left]
  rfl


lemma frontier_image (D : Set ℂ) :
    frontier (planeIsometry '' D) = planeIsometry '' frontier D :=
  (planeIsometry.toHomeomorph.image_frontier D).symm

/- The complex normal is obtained from the actual D04 outward normal. -/
lemma normalDerivative_transport {D : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (u : ℂ → ℝ) (p : frontier (planeIsometry '' D))
    (hu : DifferentiableAt ℝ u (planeIsometry.symm p)) :
    normalDerivative hD (u ∘ planeIsometry.symm) p =
      inner ℝ (gradient u (planeIsometry.symm p)) (planeOutwardNormal hD p) := by
  unfold normalDerivative
  have hg := gradient_transport u (planeIsometry.symm p) hu
  simp only [LinearIsometryEquiv.apply_symm_apply] at hg
  rw [hg]
  rw [← planeIsometry.apply_symm_apply (outwardNormal hD p)]
  exact planeIsometry.inner_map_map _ _

lemma outwardNormal_defining {D V : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (p : frontier D) (ρ : E 2 → ℝ) (hρ : IsDefiningFunction D V ρ) (hp : (p : E 2) ∈ V) :
    planeIsometry.symm (outwardNormal hD p) =
      ‖gradient (ρ ∘ planeIsometry) (planeIsometry.symm p)‖⁻¹ •
        gradient (ρ ∘ planeIsometry) (planeIsometry.symm p) := by
  have hd : DifferentiableAt ℝ ρ p :=
    ((hρ.regular p hp).contDiffAt (hρ.isOpen.mem_nhds hp)).differentiableAt (by norm_num)
  have hdp : DifferentiableAt ℝ ρ (planeIsometry (planeIsometry.symm p)) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hd
  have hc : DifferentiableAt ℝ (ρ ∘ planeIsometry) (planeIsometry.symm p) :=
    hdp.comp _ planeIsometry.differentiableAt
  have hg := gradient_transport (ρ ∘ planeIsometry) (planeIsometry.symm p) hc
  have he : (ρ ∘ planeIsometry) ∘ planeIsometry.symm = ρ := by
    funext x; simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [he] at hg
  simp only [LinearIsometryEquiv.apply_symm_apply] at hg
  rw [D04.ClassicalRegularDomains.outwardNormal_formula hD p hρ hp]
  change planeIsometry.symm (‖scalarGradient ρ p‖⁻¹ • scalarGradient ρ p) = _
  rw [hg, planeIsometry.norm_map, map_smul, LinearIsometryEquiv.symm_apply_apply]

lemma regionIntegral_zero {n : ℕ} (S : Set (E n)) :
    regionIntegral (fun _ : S => (0 : ℝ)) = 0 := by
  classical
  have he : zeroExtension (fun _ : S => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [zeroExtension]
  change Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral _ _ = _
  rw [he]
  exact (D04.Darboux.constant_integrals (enclosingBox S) 0).1.trans (zero_mul _)

/- Second Green identity with the canonical complex coordinate Laplacian.
The interior and boundary integrals are the original D04 Riemann integrals. -/
lemma second_green (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U) :
    let A := fun x : planeIsometry '' D =>
      u (planeIsometry.symm x) * coordinateLaplacian v (planeIsometry.symm x) -
      v (planeIsometry.symm x) * coordinateLaplacian u (planeIsometry.symm x)
    let B := fun x : frontier (planeIsometry '' D) =>
      u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x))
        (planeOutwardNormal hD x) -
      v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x))
        (planeOutwardNormal hD x)
    RegionIntegrable A ∧ HasDensityIntegral (d := 1) B (regionIntegral A) ∧
      regionIntegral A = boundaryIntegral B := by
  dsimp only
  have hEU : IsOpen (planeIsometry '' U) := planeIsometry.toHomeomorph.isOpenMap U hU
  have hEDU : closure (planeIsometry '' D) ⊆ planeIsometry '' U := by
    rw [closure_image]
    exact image_mono hDU
  have H := D04.GreenIdentities.second_green hD (planeIsometry '' U)
    (u ∘ planeIsometry.symm) (v ∘ planeIsometry.symm) hEU hEDU
    (contDiffOn_transport hu) (contDiffOn_transport hv)
  have hz (x : closure (planeIsometry '' D)) : planeIsometry.symm x ∈ U := by
    obtain ⟨z, hz, he⟩ := hEDU x.property
    simpa [← he] using hz
  have hA : (fun x : planeIsometry '' D =>
      (u ∘ planeIsometry.symm) x * laplacian (v ∘ planeIsometry.symm) x -
      (v ∘ planeIsometry.symm) x * laplacian (u ∘ planeIsometry.symm) x) =
      (fun x : planeIsometry '' D =>
      u (planeIsometry.symm x) * coordinateLaplacian v (planeIsometry.symm x) -
      v (planeIsometry.symm x) * coordinateLaplacian u (planeIsometry.symm x)) := by
    funext x
    have hx := hz ⟨x, subset_closure x.property⟩
    have hLu := laplacian_transport U u hU hu (planeIsometry.symm x) hx
    have hLv := laplacian_transport U v hU hv (planeIsometry.symm x) hx
    simpa only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using
      congrArg₂ (fun a b => u (planeIsometry.symm x) * a - v (planeIsometry.symm x) * b) hLv hLu
  have hB : (fun x : frontier (planeIsometry '' D) =>
      (u ∘ planeIsometry.symm) x * normalDerivative hD (v ∘ planeIsometry.symm) x -
      (v ∘ planeIsometry.symm) x * normalDerivative hD (u ∘ planeIsometry.symm) x) =
      (fun x : frontier (planeIsometry '' D) =>
      u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x)) (planeOutwardNormal hD x) -
      v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x)) (planeOutwardNormal hD x)) := by
    funext x
    have hx := hz ⟨x, frontier_subset_closure x.property⟩
    rw [normalDerivative_transport hD v x
      (((hv _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)),
      normalDerivative_transport hD u x
      (((hu _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))]
    rfl
  rw [hA, hB] at H
  exact H


lemma harmonic_second_green (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hLu : ∀ z ∈ D, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ D, coordinateLaplacian v z = 0) :
    let B := fun x : frontier (planeIsometry '' D) =>
      u (planeIsometry.symm x) * inner ℝ (gradient v (planeIsometry.symm x))
        (planeOutwardNormal hD x) -
      v (planeIsometry.symm x) * inner ℝ (gradient u (planeIsometry.symm x))
        (planeOutwardNormal hD x)
    HasDensityIntegral (d := 1) B 0 ∧ boundaryIntegral B = 0 := by
  have H := second_green D U hD hU hDU u v hu hv
  have he : (fun x : planeIsometry '' D =>
      u (planeIsometry.symm x) * coordinateLaplacian v (planeIsometry.symm x) -
      v (planeIsometry.symm x) * coordinateLaplacian u (planeIsometry.symm x)) =
      fun _ => 0 := by
    funext x
    obtain ⟨z, hz, hx⟩ := x.property
    have hz' : planeIsometry.symm x ∈ D := by
      rw [← hx, LinearIsometryEquiv.symm_apply_apply]; exact hz
    rw [hLu _ hz', hLv _ hz', mul_zero, mul_zero, sub_self]
  dsimp only at H ⊢
  rw [he, regionIntegral_zero] at H
  exact ⟨H.2.1, H.2.2.symm⟩


lemma gradient_deleted_disk (c : ℂ) (r : ℝ) (z : ℂ) :
    gradient (fun w : ℂ => r ^ 2 - ‖w - c‖ ^ 2) z = (-2 : ℝ) • (z - c) := by
  have hd := ((hasFDerivAt_id z).sub_const c).norm_sq.const_sub (r ^ 2)
  simp only [id_eq] at hd
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, hd.fderiv]
  simp
  ring

lemma normalFromDefining_deleted_disk (c : ℂ) (r : ℝ) (_hr : 0 < r)
    (z : ℂ) (hz : ‖z - c‖ = r) :
    ‖gradient (fun w : ℂ => r ^ 2 - ‖w - c‖ ^ 2) z‖⁻¹ •
      gradient (fun w : ℂ => r ^ 2 - ‖w - c‖ ^ 2) z =
        -(r⁻¹ • (z - c)) := by
  rw [gradient_deleted_disk, norm_smul, hz]
  norm_num
  ring

lemma circle_speed (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (t : ℝ) :
    ‖deriv (circleMap c r) t‖ = r := by
  rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hr]

lemma circle_inward_radial (c : ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    -(r⁻¹ • (circleMap c r t - c)) = -Complex.exp ((t : ℂ) * Complex.I) := by
  simp [circleMap, Complex.real_smul, ne_of_gt hr]


/- Isometric real parameter coordinate, with its standard Lebesgue volume. -/
lemma riemann_interval (a b : ℝ) (hab : a ≤ b) (f : E 1 → ℝ)
    (hf : RegionIntegrable (fun x : intervalIsometry '' Icc a b => f x)) :
    regionIntegral (fun x : intervalIsometry '' Icc a b => f x) =
      ∫ t in a..b, f (intervalIsometry t) := by
  have hs : MeasurableSet (intervalIsometry '' Icc a b) :=
    (intervalIsometry.toHomeomorph.isClosedMap _ isClosed_Icc).measurableSet
  have H := D04.MeasureBridge.region_bridge_ambient f hs hf
  calc
    _ = ∫ x in intervalIsometry '' Icc a b, f x := H.2
    _ = ∫ t in Icc a b, f (intervalIsometry t) :=
      intervalIsometry.measurePreserving.setIntegral_image_emb
        intervalIsometry.toHomeomorph.measurableEmbedding f (Icc a b)
    _ = _ := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]


lemma riemann_interval_integrable (a b : ℝ) (hab : a ≤ b) (f : E 1 → ℝ)
    (hf : RegionIntegrable (fun x : intervalIsometry '' Icc a b => f x)) :
    IntervalIntegrable (fun t => f (intervalIsometry t)) MeasureTheory.volume a b := by
  have hs : MeasurableSet (intervalIsometry '' Icc a b) :=
    (intervalIsometry.toHomeomorph.isClosedMap _ isClosed_Icc).measurableSet
  have H := D04.MeasureBridge.region_bridge_ambient f hs hf
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (intervalIsometry.measurePreserving.integrableOn_image
    intervalIsometry.toHomeomorph.measurableEmbedding).mp H.1

open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.GeneralizedStokes.Model

/- A finite boundary display; every field is geometric. In particular it
contains no asserted equality of any integrals. -/
lemma density_boundary_display {D U : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U) (B : BoundaryDisplay hD U) :
    HasDensityIntegral (d := 1) (normalFlux F (outwardNormal hD))
      (∑ j, (B.sign j).val * patchIntegral (B.patch j) (fun _ => 1) (fluxForm F)) := by
  have hCr := (D04.crOn_iff_contDiffOn 1 U F hU).mpr hF
  have hg := D04.Gauss.gauss hD U F hU hDU hCr
  obtain ⟨o, ho, hK, hM, hb, hJD, hJK, hn, hdef, hdata⟩ :=
    D04.RegularDomainBridge.regular_domain_interface hD
  have hbK : IsCompact (intrinsicBoundary 1 2 (closure D)) := by
    rw [B.boundary_eq]
    exact hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hMO : intrinsicBoundary 1 2 (closure D) ⊆ U := by
    rw [B.boundary_eq]
    exact frontier_subset_closure.trans hDU
  have hβ := D04.Dictionary.fluxForm_isCr 1 U F hU hCr
  have hI := D04.ManifoldBoundaryAssembly.regular_display_integral
    B.boundaryOrientation hbK hMO B.patch B.sign B.regular B.seams
    B.seam_dimension B.self_intersections B.intersections B.cover (fluxForm F)
    (D04.LocalStokes.form_C0 U _ hβ)
  let ν : intrinsicBoundary 1 2 (closure D) → E 2 :=
    fun x => outwardNormal hD ⟨x, B.boundary_eq ▸ x.property⟩
  have hν (x : intrinsicBoundary 1 2 (closure D)) :
      IsOutwardUnitConormal 1 1 (closure D) x (ν x) :=
    hn ⟨x, B.boundary_eq ▸ x.property⟩
  rw [D04.Gauss.boundary_flux B.orientation B.ambient B.boundaryOrientation B.outward ν hν F] at hI
  have hρ : Continuous (normalFlux F ν) := by
    have hmap : Continuous (fun x : intrinsicBoundary 1 2 (closure D) =>
        (⟨(x : E 2), B.boundary_eq ▸ x.property⟩ : frontier D)) :=
      continuous_subtype_val.subtype_mk _
    exact hg.2.1.comp hmap
  have hbM := (D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)).1
  have H := D04.Gauss.metric_density_integral hbM hbK B.boundaryOrientation
    (normalFlux F ν) hρ _ hI
  exact D04.Gauss.density_transport B.boundary_eq (normalFlux F (outwardNormal hD)) _ H


/- Total extension of the actual D04 normal along a parametrization. -/
lemma gramDensity_one (v : Fin 1 → E 2) : gramDensity v = ‖v 0‖ := by
  change Real.sqrt (Matrix.det (fun i j : Fin 1 => inner ℝ (v i) (v j))) = _
  rw [Matrix.det_fin_one, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma patch_interval_flux {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hU : IsOpen U) (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U)
    (P : Patch 1 U) (s : PointSign) (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = intervalIsometry '' Icc a b)
    (hframe : ∀ x ∈ P.region,
      ‖patchNormal hD P x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD P x) (fderiv ℝ P.map x (standardBasis 1 i)) = 0) ∧
      0 < s.val * omega 2 (Fin.cons (patchNormal hD P x)
        (fun i => fderiv ℝ P.map x (standardBasis 1 i)))) :
    s.val * patchIntegral P (fun _ => 1) (fluxForm F) =
      ∫ t in a..b, inner ℝ (F (P.map (intervalIsometry t)))
        (patchNormal hD P (intervalIsometry t)) *
          ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖ := by
  have hCr := (D04.crOn_iff_contDiffOn 1 U F hU).mpr hF
  have hβ := D04.Dictionary.fluxForm_isCr 1 U F hU hCr
  have hi := D04.GeometricPatches.weighted_integrable P (fluxForm F)
    (D04.LocalStokes.form_C0 U _ hβ) (fun _ => 1) continuousOn_const
  have convert_interval (S : Set (E 1)) (hS : S = intervalIsometry '' Icc a b)
      (g : E 1 → ℝ) (hg : RegionIntegrable (fun x : S => g x)) :
      regionIntegral (fun x : S => g x) = ∫ t in a..b, g (intervalIsometry t) := by
    subst S
    exact riemann_interval a b hab g hg
  have he' : patchIntegral P (fun _ => 1) (fluxForm F) =
      ∫ t in a..b, weightedCoefficient P (fun _ => 1) (fluxForm F) (intervalIsometry t) :=
    convert_interval P.region hregion (weightedCoefficient P (fun _ => 1) (fluxForm F)) hi
  rw [he', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hx : intervalIsometry t ∈ P.region := hregion ▸ mem_image_of_mem _ ht'
  obtain ⟨hn, hp, ho⟩ := hframe _ hx
  have h := D04.Gauss.frame_flux (F (P.map (intervalIsometry t)))
    (patchNormal hD P (intervalIsometry t))
    (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i)) hn hp s.val s.property ho
  change s.val * (1 * fluxForm F (P.map (intervalIsometry t))
    (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i))) = _
  rw [one_mul, D04.Dictionary.fluxForm_volume, h, gramDensity_one]

lemma patch_interval_integrable {D U : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (hU : IsOpen U) (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U)
    (P : Patch 1 U) (s : PointSign) (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = intervalIsometry '' Icc a b)
    (hframe : ∀ x ∈ P.region,
      ‖patchNormal hD P x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD P x) (fderiv ℝ P.map x (standardBasis 1 i)) = 0) ∧
      0 < s.val * omega 2 (Fin.cons (patchNormal hD P x)
        (fun i => fderiv ℝ P.map x (standardBasis 1 i)))) :
    IntervalIntegrable (fun t => inner ℝ (F (P.map (intervalIsometry t)))
        (patchNormal hD P (intervalIsometry t)) *
          ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖)
      MeasureTheory.volume a b := by
  have hCr := (D04.crOn_iff_contDiffOn 1 U F hU).mpr hF
  have hβ := D04.Dictionary.fluxForm_isCr 1 U F hU hCr
  have hi := D04.GeometricPatches.weighted_integrable P (fluxForm F)
    (D04.LocalStokes.form_C0 U _ hβ) (fun _ => 1) continuousOn_const
  have convert_interval (S : Set (E 1)) (hS : S = intervalIsometry '' Icc a b)
      (g : E 1 → ℝ) (hg : RegionIntegrable (fun x : S => g x)) :
      IntervalIntegrable (fun t => g (intervalIsometry t)) MeasureTheory.volume a b := by
    subst S
    exact riemann_interval_integrable a b hab g hg
  have hi' := (convert_interval P.region hregion _ hi).const_mul s.val
  apply hi'.congr
  intro t ht
  have ht' : t ∈ Icc a b := by
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)
  have hx : intervalIsometry t ∈ P.region := hregion ▸ mem_image_of_mem _ ht'
  obtain ⟨hn, hp, ho⟩ := hframe _ hx
  have h := D04.Gauss.frame_flux (F (P.map (intervalIsometry t)))
    (patchNormal hD P (intervalIsometry t))
    (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i)) hn hp s.val s.property ho
  change s.val * (1 * fluxForm F (P.map (intervalIsometry t))
    (fun i => fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 i))) = _
  rw [one_mul, D04.Dictionary.fluxForm_volume, h, gramDensity_one]

lemma density_interval_display {D U : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (hU : IsOpen U) (hDU : closure D ⊆ U)
    (F : E 2 → E 2) (hF : ContDiffOn ℝ 1 F U) (B : BoundaryDisplay hD U)
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))) :
    let J := ∑ j, ∫ t in (a j)..(b j),
      inner ℝ (F ((B.patch j).map (intervalIsometry t)))
        (patchNormal hD (B.patch j) (intervalIsometry t)) *
      ‖fderiv ℝ (B.patch j).map (intervalIsometry t) (standardBasis 1 0)‖
    HasDensityIntegral (d := 1) (normalFlux F (outwardNormal hD)) J ∧
      boundaryIntegral (normalFlux F (outwardNormal hD)) = J := by
  dsimp only
  have H := density_boundary_display hD hU hDU F hF B
  have he := fun j => patch_interval_flux hD hU F hF (B.patch j) (B.sign j)
    (a j) (b j) (hab j) (hregion j) (hframe j)
  simp_rw [he] at H
  exact ⟨H, D04.GreenIdentities.boundaryIntegral_eq H⟩


lemma interval_basis : intervalIsometry 1 = standardBasis 1 0 := by
  ext i
  fin_cases i
  simp [intervalIsometry, standardBasis]

lemma parametrization_speed {U : Set (E 2)} (P : Patch 1 U) (t : ℝ)
    (ht : intervalIsometry t ∈ P.domain) :
    ‖deriv (fun s => planeIsometry.symm (P.map (intervalIsometry s))) t‖ =
      ‖fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)‖ := by
  have hP := ((P.regular _ ht).contDiffAt (P.open_domain.mem_nhds ht)).differentiableAt (by norm_num)
  have hι := intervalIsometry.toContinuousLinearEquiv.toContinuousLinearMap.hasDerivAt (x := t)
  have hcomp := hP.hasFDerivAt.comp_hasDerivAt t hι
  have H := planeIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hcomp
  have he : deriv (fun s => planeIsometry.symm (P.map (intervalIsometry s))) t =
      planeIsometry.symm (fderiv ℝ P.map (intervalIsometry t) (standardBasis 1 0)) := by
    have Hd := H.deriv
    change deriv (fun s => planeIsometry.symm (P.map (intervalIsometry s))) t =
      planeIsometry.symm (fderiv ℝ P.map (intervalIsometry t) (intervalIsometry 1)) at Hd
    rw [interval_basis] at Hd
    exact Hd
  rw [he, planeIsometry.symm.norm_map]


lemma outwardNormal_deleted_disk {D V : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (p : frontier D) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hρ : IsDefiningFunction D V (fun x => r ^ 2 - ‖planeIsometry.symm x - c‖ ^ 2))
    (hp : (p : E 2) ∈ V) :
    planeIsometry.symm (outwardNormal hD p) =
      -(r⁻¹ • (planeIsometry.symm p - c)) := by
  have hz : ‖planeIsometry.symm p - c‖ = r := by
    have hz0 := (hρ.zero_level p hp).mp p.property
    change r ^ 2 - ‖planeIsometry.symm p - c‖ ^ 2 = 0 at hz0
    nlinarith [norm_nonneg (planeIsometry.symm p - c)]
  have H := outwardNormal_defining hD p _ hρ hp
  have he : (fun x : E 2 => r ^ 2 - ‖planeIsometry.symm x - c‖ ^ 2) ∘ planeIsometry =
      (fun z : ℂ => r ^ 2 - ‖z - c‖ ^ 2) := by
    funext z
    simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [he, normalFromDefining_deleted_disk c r hr _ hz] at H
  exact H

/- The vector field to which the real divergence theorem is applied. -/
lemma greenField_regular (U : Set ℂ) (hU : IsOpen U) (u v : ℂ → ℝ)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U) :
    ContDiffOn ℝ 1 (greenField u v) (planeIsometry '' U) := by
  have hEU : IsOpen (planeIsometry '' U) := planeIsometry.toHomeomorph.isOpenMap U hU
  have huE := contDiffOn_transport hu
  have hvE := contDiffOn_transport hv
  exact ((huE.of_le (by norm_num)).smul (D04.GreenIdentities.gradient_regular hEU hvE)).sub
    ((hvE.of_le (by norm_num)).smul (D04.GreenIdentities.gradient_regular hEU huE))

lemma greenField_flux (u v : ℂ → ℝ) (z : ℂ) (ν : E 2)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    inner ℝ (greenField u v (planeIsometry z)) ν =
      u z * inner ℝ (gradient v z) (planeIsometry.symm ν) -
      v z * inner ℝ (gradient u z) (planeIsometry.symm ν) := by
  unfold greenField
  rw [gradient_transport v z hv, gradient_transport u z hu]
  simp only [LinearIsometryEquiv.symm_apply_apply, inner_sub_left, inner_smul_left,
    RCLike.conj_to_real]
  conv_lhs => rw [← planeIsometry.apply_symm_apply ν]
  rw [planeIsometry.inner_map_map, planeIsometry.inner_map_map]


/- The real Green boundary density, written on the complex plane. -/

/- An ordinary scalar Lebesgue interval integral with the actual complex
parameter speed. The normal is the actual outward normal of the region. -/
lemma complex_boundary_display (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))) :
    HasDensityIntegral (d := 1) (boundaryFlux hD u v)
      (∑ j, arcFlux hD (B.patch j) u v (a j) (b j)) ∧
    boundaryIntegral (boundaryFlux hD u v) =
      ∑ j, arcFlux hD (B.patch j) u v (a j) (b j) := by
  have hEU : IsOpen (planeIsometry '' U) := planeIsometry.toHomeomorph.isOpenMap U hU
  have hEDU : closure (planeIsometry '' D) ⊆ planeIsometry '' U := by
    rw [closure_image]
    exact image_mono hDU
  have H := density_interval_display hD hEU hEDU (greenField u v)
    (greenField_regular U hU u v hu hv) B a b hab hregion hframe
  have hden : normalFlux (greenField u v) (outwardNormal hD) = boundaryFlux hD u v := by
    funext x
    have hxE := hEDU (frontier_subset_closure x.property)
    have hx : planeIsometry.symm x ∈ U := by
      obtain ⟨z, hz, he⟩ := hxE
      rw [← he, LinearIsometryEquiv.symm_apply_apply]
      exact hz
    have hc := greenField_flux u v (planeIsometry.symm x) (outwardNormal hD x)
      (((hu _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
      (((hv _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
    simpa only [LinearIsometryEquiv.apply_symm_apply, normalFlux, boundaryFlux, planeOutwardNormal] using hc
  have hsum : (∑ j, ∫ t in (a j)..(b j),
      inner ℝ (greenField u v ((B.patch j).map (intervalIsometry t)))
        (patchNormal hD (B.patch j) (intervalIsometry t)) *
      ‖fderiv ℝ (B.patch j).map (intervalIsometry t) (standardBasis 1 0)‖) =
      ∑ j, arcFlux hD (B.patch j) u v (a j) (b j) := by
    apply Finset.sum_congr rfl
    intro j _
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (a j) (b j) := by simpa only [uIcc_of_le (hab j)] using ht
    have hx : intervalIsometry t ∈ (B.patch j).domain :=
      (B.patch j).contains (subset_closure ((hregion j) ▸ mem_image_of_mem _ ht'))
    have hxE := (B.patch j).mapsTo hx
    have hz : planeIsometry.symm ((B.patch j).map (intervalIsometry t)) ∈ U := by
      obtain ⟨z, hz, he⟩ := hxE
      rw [← he, LinearIsometryEquiv.symm_apply_apply]
      exact hz
    dsimp only [arcIntegrand]
    rw [parametrization_speed (B.patch j) t hx]
    have hc := greenField_flux u v
      (planeIsometry.symm ((B.patch j).map (intervalIsometry t)))
      (patchNormal hD (B.patch j) (intervalIsometry t))
      (((hu _ hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      (((hv _ hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
    simp only [LinearIsometryEquiv.apply_symm_apply] at hc
    exact congrArg (fun q => q * ‖fderiv ℝ (B.patch j).map (intervalIsometry t) (standardBasis 1 0)‖) hc
  dsimp only at H
  rw [hden, hsum] at H
  exact H

lemma harmonic_boundary_display (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hLu : ∀ z ∈ D, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ D, coordinateLaplacian v z = 0)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))) :
    (∑ j, arcFlux hD (B.patch j) u v (a j) (b j)) = 0 ∧
      HasDensityIntegral (d := 1) (boundaryFlux hD u v) 0 := by
  have H := complex_boundary_display D U hD hU hDU u v hu hv B a b hab hregion hframe
  have H0 := harmonic_second_green D U hD hU hDU u v hu hv hLu hLv
  exact ⟨D04.GreenIdentities.density_value_unique H.1 H0.1, H0.1⟩

lemma complex_boundary_integrable (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (_hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (B : BoundaryDisplay hD (planeIsometry '' U))
    (a b : Fin B.count → ℝ) (hab : ∀ j, a j ≤ b j)
    (hregion : ∀ j, (B.patch j).region = intervalIsometry '' Icc (a j) (b j))
    (hframe : ∀ j x, x ∈ (B.patch j).region →
      ‖patchNormal hD (B.patch j) x‖ = 1 ∧
      (∀ i, inner ℝ (patchNormal hD (B.patch j) x)
        (fderiv ℝ (B.patch j).map x (standardBasis 1 i)) = 0) ∧
      0 < (B.sign j).val * omega 2 (Fin.cons (patchNormal hD (B.patch j) x)
        (fun i => fderiv ℝ (B.patch j).map x (standardBasis 1 i)))) :
    ∀ j, IntervalIntegrable (arcIntegrand hD (B.patch j) u v) MeasureTheory.volume (a j) (b j) := by
  intro j
  have hEU : IsOpen (planeIsometry '' U) := planeIsometry.toHomeomorph.isOpenMap U hU
  have H := patch_interval_integrable hD hEU (greenField u v)
    (greenField_regular U hU u v hu hv) (B.patch j) (B.sign j)
    (a j) (b j) (hab j) (hregion j) (hframe j)
  apply H.congr
  intro t ht
  have ht' : t ∈ Icc (a j) (b j) := by
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (hab j)] using ht)
  have hx : intervalIsometry t ∈ (B.patch j).domain :=
    (B.patch j).contains (subset_closure ((hregion j) ▸ mem_image_of_mem _ ht'))
  have hxE := (B.patch j).mapsTo hx
  have hz : planeIsometry.symm ((B.patch j).map (intervalIsometry t)) ∈ U := by
    obtain ⟨z, hz, he⟩ := hxE
    rw [← he, LinearIsometryEquiv.symm_apply_apply]
    exact hz
  unfold arcIntegrand
  rw [parametrization_speed (B.patch j) t hx]
  have hc := greenField_flux u v
    (planeIsometry.symm ((B.patch j).map (intervalIsometry t)))
    (patchNormal hD (B.patch j) (intervalIsometry t))
    (((hu _ hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
    (((hv _ hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  simp only [LinearIsometryEquiv.apply_symm_apply] at hc
  exact congrArg (fun q => q * ‖fderiv ℝ (B.patch j).map (intervalIsometry t) (standardBasis 1 0)‖) hc


lemma deleted_circle_normal_speed {D V : Set (E 2)}
    (hD : IsClassicalRegularDomain D) (c : ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (p : frontier D) (he : (p : E 2) = planeIsometry (circleMap c r t))
    (hρ : IsDefiningFunction D V (fun x => r ^ 2 - ‖planeIsometry.symm x - c‖ ^ 2))
    (hp : (p : E 2) ∈ V) :
    planeIsometry.symm (outwardNormal hD p) = -Complex.exp ((t : ℂ) * Complex.I) ∧
      ‖deriv (circleMap c r) t‖ = r := by
  refine ⟨?_, circle_speed c r hr.le t⟩
  rw [outwardNormal_deleted_disk hD p c r hr hρ hp, he,
    LinearIsometryEquiv.symm_apply_apply, circle_inward_radial c r hr t]


lemma region_integral_transport {D : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D)) (f : ℂ → ℝ)
    (hf : RegionIntegrable (fun x : planeIsometry '' D => f (planeIsometry.symm x))) :
    MeasureTheory.IntegrableOn f D ∧
      regionIntegral (fun x : planeIsometry '' D => f (planeIsometry.symm x)) =
        ∫ z in D, f z := by
  have H := D04.MeasureBridge.region_bridge_ambient (f ∘ planeIsometry.symm)
    hD.isOpen.measurableSet hf
  have he : (f ∘ planeIsometry.symm) ∘ planeIsometry = f := by
    funext z
    simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  have hi := (planeIsometry.measurePreserving.integrableOn_image
    planeIsometry.toHomeomorph.measurableEmbedding).mp H.1
  refine ⟨?_, ?_⟩
  · simpa only [he] using hi
  · calc
      _ = ∫ x in planeIsometry '' D, (f ∘ planeIsometry.symm) x := H.2
      _ = ∫ z in D, (f ∘ planeIsometry.symm) (planeIsometry z) :=
        planeIsometry.measurePreserving.setIntegral_image_emb
          planeIsometry.toHomeomorph.measurableEmbedding (f ∘ planeIsometry.symm) D
      _ = _ := by simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]


lemma second_green_lebesgue (D U : Set ℂ)
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (hU : IsOpen U) (hDU : closure D ⊆ U)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U) :
    let f := fun z => u z * coordinateLaplacian v z - v z * coordinateLaplacian u z
    MeasureTheory.IntegrableOn f D ∧
      HasDensityIntegral (d := 1) (boundaryFlux hD u v) (∫ z in D, f z) ∧
      (∫ z in D, f z) = boundaryIntegral (boundaryFlux hD u v) := by
  have H := second_green D U hD hU hDU u v hu hv
  have HT := region_integral_transport hD
    (fun z => u z * coordinateLaplacian v z - v z * coordinateLaplacian u z) H.1
  refine ⟨HT.1, ?_, ?_⟩
  · rw [← HT.2]
    exact H.2.1
  · rw [← HT.2]
    exact H.2.2


namespace Definitions
abbrev planeIsometry : Specs.D12Complex.Ch14.ComplexGreenBridge.planeIsometry_type :=
  @_root_.D12Complex.ComplexGreenBridge.planeIsometry

abbrev intervalIsometry : Specs.D12Complex.Ch14.ComplexGreenBridge.intervalIsometry_type :=
  @_root_.D12Complex.ComplexGreenBridge.intervalIsometry

abbrev planeOutwardNormal : Specs.D12Complex.Ch14.ComplexGreenBridge.planeOutwardNormal_type :=
  @_root_.D12Complex.ComplexGreenBridge.planeOutwardNormal

abbrev BoundaryDisplay : Specs.D12Complex.Ch14.ComplexGreenBridge.BoundaryDisplay_type :=
  @_root_.D12Complex.ComplexGreenBridge.BoundaryDisplay

abbrev patchNormal : Specs.D12Complex.Ch14.ComplexGreenBridge.patchNormal_type :=
  @_root_.D12Complex.ComplexGreenBridge.patchNormal

abbrev greenField : Specs.D12Complex.Ch14.ComplexGreenBridge.greenField_type :=
  @_root_.D12Complex.ComplexGreenBridge.greenField

abbrev boundaryFlux : Specs.D12Complex.Ch14.ComplexGreenBridge.boundaryFlux_type :=
  @_root_.D12Complex.ComplexGreenBridge.boundaryFlux

abbrev arcIntegrand : Specs.D12Complex.Ch14.ComplexGreenBridge.arcIntegrand_type :=
  @_root_.D12Complex.ComplexGreenBridge.arcIntegrand

abbrev arcFlux : Specs.D12Complex.Ch14.ComplexGreenBridge.arcFlux_type :=
  @_root_.D12Complex.ComplexGreenBridge.arcFlux

end Definitions

end D12Complex.ComplexGreenBridge
