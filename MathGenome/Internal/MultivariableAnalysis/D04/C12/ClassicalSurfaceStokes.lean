import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalSurfaceStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C10.SurfaceAssembly
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FinitePiecewiseStokes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open Set Function Topology
open scoped RealInnerProductSpace BigOperators ContDiff Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.ClassicalSurfaceStokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C12.ClassicalSurfaceStokes
open Model

abbrev cellFlux := @Model.cellFlux
abbrev NormalCompatible := @Model.NormalCompatible
abbrev workCoefficient := @Model.workCoefficient
abbrev chartUnitTangent := @Model.chartUnitTangent
abbrev HasBoundaryWorkIntegral := @Model.HasBoundaryWorkIntegral

lemma boundary_work_coefficient {B : Set (E 3)} (F : E 3 → E 3)
    (c : EmbeddedChart 1 1 3 B) (u : c.source) :
    topCoefficient (tangentRestriction 1 1 B (alpha F)) c u = workCoefficient F c u := rfl

theorem positive_chart_flux : positive_chart_fluxType := by
  intro M N o ho F c u hp
  have hs : normalChartSign N c u = 1 := (ho c u).symm.trans hp
  constructor
  · exact D04SurfaceAssembly.flux_form_coefficient (fun x : M => F x) c u
  · have he := (D04SurfaceAssembly.normal_chart_sign o.manifold N c u).2.2
      (fun x : M => F x)
    simp only [hs, one_mul] at he
    convert he using 1 <;> rfl

theorem boundary_work_bridge : boundary_work_bridgeType := by
  intro B bO F I
  rfl

theorem boundary_path_work : boundary_path_workType := by
  intro a b gamma d F h
  rfl

theorem boundary_chart_speed : boundary_chart_speedType := by
  intro B c u s F
  let v := chartDifferential c u (standardBasis 1 0)
  have hv : v ≠ 0 := by
    intro hz
    have he : chartDifferential c u (standardBasis 1 0) = chartDifferential c u 0 :=
      hz.trans (map_zero _).symm
    exact (standardBasis 1).ne_zero 0
      (D04.EmbeddedChart.differential_injective c
        (show ManifoldRegularity (1 : ℕ∞ω) from ⟨le_rfl, by simp⟩) u.property he)
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hd : chartDensity c u = ‖v‖ := D04MetricDensity.gram_speed (chartDifferential c u)
  constructor
  · change s * ⟪F (c.toFun u), v⟫ = ⟪F (c.toFun u), (s / ‖v‖) • v⟫ * _
    rw [hd, inner_smul_right]
    field_simp
  · intro hs
    change ‖(s / ‖v‖) • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg v),
      div_mul_cancel₀ _ hn]
    rcases hs with rfl | rfl <;> norm_num

lemma curl_continuousOn (O : Set (E 3)) (hO : IsOpen O)
    (F : E 3 → E 3) (hF : CrOn 1 O F) : ContinuousOn (curl F) O := by
  have hd : ContinuousOn (totalDerivative F) O :=
    ((D04.crOn_iff_contDiffOn 0 O _ hO).mp hF.2).continuousOn
  have hc (i j : Fin 3) : ContinuousOn (fun x =>
      (totalDerivative F x (standardBasis 3 j)) i) O :=
    (show Continuous (fun v : E 3 => v i) from (continuous_apply i).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))).comp_continuousOn
      (hd.clm_apply continuousOn_const)
  have hj (i j : Fin 3) : ContinuousOn
      (fun x => Specs.D04.C02.DerivativeBridge.Model.jacobian F x i j) O := by
    apply (hc i j).congr
    intro x hx
    exact D04.matrixOfLinearMap_apply (totalDerivative F x).toLinearMap i j
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · convert (hj 2 1).sub (hj 1 2) using 1 <;> rfl
  · convert (hj 0 2).sub (hj 2 0) using 1 <;> rfl
  · convert (hj 1 0).sub (hj 0 1) using 1 <;> rfl

lemma tangent_curl_bridge {M : Set (E 3)} (O : Set (E 3)) (F : E 3 → E 3)
    (hO : IsOpen O) (hMO : M ⊆ O) (hF : CrOn 1 O F) :
    tangentRestriction 1 2 M (exteriorDerivative (alpha F)) =
      surfaceFluxForm (fun x : M => curl F x) := by
  funext x
  change (exteriorDerivative (alpha F) x).compLinearMap _ = _
  rw [D04.Dictionary.exterior_alpha_curl O F hO hF x (hMO x.property)]
  rfl

/-- C10 identifies the geometric flux with every allowed C15 partition;
C15 supplies the equality with boundary work. -/
theorem surface_stokes : surface_stokesType := by
  intro M hM hcompact N
  obtain ⟨o, ho, hflux⟩ := D04SurfaceAssembly.flux_beta_identification hM hcompact N
  refine ⟨o, ho, ?_⟩
  intro O F hO hMO hF
  obtain ⟨bO, hout, I, hI, hB⟩ :=
    D04Stokes.ambient_stokes_compact o hcompact O (alpha F) hMO
      (D04.Dictionary.alpha_isCr 1 O F hO hF)
  rw [tangent_curl_bridge O F hO hMO hF] at hI
  have hc : Continuous (fun x : M => curl F x) :=
    ((curl_continuousOn O hO F hF).mono hMO).domRestrict
  obtain ⟨P⟩ := hI.2.2.1
  have he : surfaceFlux N (fun x : M => curl F x) = I :=
    (hflux _ hc).2 P |>.trans (hI.2.2.2 P).2
  exact ⟨bO, hout, he ▸ hI, (boundary_work_bridge bO F _).mpr (he ▸ hB)⟩

/-- Normal compatibility identifies the actual normalized metric area form. -/
lemma normal_metric_volume {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M) (ho : NormalCompatible N o) :
    surfaceFluxForm N.toFun = metricVolume o.atPoint := by
  funext x
  obtain ⟨c, u, hu, he⟩ := o.manifold.2.2 x x.property
  have hx : chartPoint c ⟨u, hu.1⟩ = x := Subtype.ext he
  rw [← hx]
  apply AlternatingMap.compLinearMap_injective (tangentChartMap c u hu.1)
    (D04.Orientations.tangentChartMap_bijective c o.manifold.1 o.manifold.2.1 u hu.1).2
  change tangentPullback (surfaceFluxForm N.toFun) c u hu.1 =
    tangentPullback (metricVolume o.atPoint) c u hu.1
  rw [D04MetricDensity.metricVolume_pullback o.manifold (by norm_num)]
  rw [(tangentPullback (surfaceFluxForm N.toFun) c u hu.1).eq_smul_basis_det
    (standardBasis 2)]
  congr 1
  exact (D04SurfaceAssembly.normal_coefficient o.manifold N c ⟨u, hu.1⟩).trans
    (congrArg (fun s => s * chartDensity c u) (ho c ⟨u, hu.1⟩).symm)

lemma cross_cross_identity (a b c : E 3) :
    euclideanCross (euclideanCross a b) c = ⟪a, c⟫ • b - ⟪b, c⟫ • a := by
  have h := cross_cross_eq_smul_sub_smul (WithLp.ofLp a) (WithLp.ofLp b) (WithLp.ofLp c)
  apply WithLp.ofLp_injective
  simpa only [euclideanCross, WithLp.ofLp_toLp, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, WithLp.ofLp_sub, WithLp.ofLp_smul, dotProduct_comm] using h

/-- Outward-first applied to an orthonormal boundary frame gives the usual
right-hand rule, including the sign on each boundary component. -/
theorem boundary_tangent_cross : boundary_tangent_crossType := by
  intro M N o ho x nu hnu b hb
  obtain ⟨B, hB0, hB1, hBo⟩ := hb
  let tau : E 3 := (b 0).val
  have ht : ‖tau‖ = 1 := b.norm_eq_one 0
  have hn : ‖nu‖ = 1 := hnu.2.1
  have hp : ⟪nu, tau⟫ = 0 := hnu.2.2.1 tau (b 0).property
  have htp : ⟪tau, nu⟫ = 0 := (real_inner_comm _ _).trans hp
  have hNN : ‖N.toFun ⟨x, x.property.1⟩‖ = 1 := (N.normal _).1
  have hmetric : metricVolume o.atPoint ⟨x, x.property.1⟩ B = 1 := by
    letI : Fact (Module.finrank ℝ (tangentSpace 1 2 M x) = 2) :=
      ⟨D04.tangentSpace_finrank o.manifold x x.property.1⟩
    rw [D04MetricDensity.metricVolume_eq o.manifold]
    rw [D04MetricDensity.metricTopForm_signed_gram (by norm_num)]
    have hpos := (D04.Orientations.representative_pos_iff
      (o.atPoint x x.property.1) B).mpr hBo
    rw [Real.sign_of_pos hpos, one_mul]
    change Real.sqrt (Matrix.det (fun i j : Fin 2 => ⟪(B i).val, (B j).val⟫)) = 1
    have he : (fun i => (B i).val) = ![nu, tau] := by
      funext i
      fin_cases i
      · exact hB0
      · exact hB1 0
    simp_rw [show ∀ i, (B i).val = ![nu, tau] i from congrFun he]
    simp [gramDensity, Matrix.det_fin_two, hp, htp, real_inner_self_eq_norm_sq, hn, ht]
  have hbeta : ⟪N.toFun ⟨x, x.property.1⟩, euclideanCross nu tau⟫ = 1 := by
    have hm := congrArg (fun eta : TangentTopField 1 2 M => eta ⟨x, x.property.1⟩ B)
      (normal_metric_volume N o ho)
    rw [hmetric] at hm
    change beta (fun _ => N.toFun ⟨x, x.property.1⟩) x (fun i => (B i).val) = 1 at hm
    have he : (fun i => (B i).val) = ![nu, tau] := by
      funext i
      fin_cases i
      · exact hB0
      · exact hB1 0
    rwa [he, D04.Dictionary.beta_cross] at hm
  have hcross : euclideanCross nu tau = N.toFun ⟨x, x.property.1⟩ := by
    have hc := D04MetricDensity.cross_norm_sq nu tau
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn, ht, hp, htp] at hc
    have hz := norm_sub_sq_real (N.toFun ⟨x, x.property.1⟩) (euclideanCross nu tau)
    rw [hNN, hbeta, ← hc] at hz
    have hzero : ‖N.toFun ⟨x, x.property.1⟩ - euclideanCross nu tau‖ = 0 := by nlinarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  have he := cross_cross_identity nu tau nu
  rw [real_inner_self_eq_norm_sq, hn, one_pow, htp, one_smul, zero_smul, sub_zero,
    hcross] at he
  exact he.symm


/-- The existing geometric flux has the expected value for any orientation
compatible with N, rather than only one chosen orientation witness. -/
lemma flux_value_of_integral {M : Set (E 3)} (N : UnitNormalField M)
    (o : PositiveManifoldOrientation 1 2 M) (ho : NormalCompatible N o)
    (hc : IsCompact M) (F : M → E 3) (hF : Continuous F) (I : ℝ)
    (hI : HasPositiveIntegral o (surfaceFluxForm F) I) : surfaceFlux N F = I := by
  obtain ⟨P⟩ := hI.2.2.1
  have he : surfaceFlux N F = orientedIntegral (surfaceFluxForm F) P := by
    change surfaceIntegral M (fun x => ⟪F x, N.toFun x⟫) = _
    rw [D04SurfaceAssembly.scalar_chart_formula o.manifold hc _ (hF.inner N.continuous)
      P.toChartPartition (D04SurfaceAssembly.flux_scalar_support_subset o.manifold N F)]
    dsimp only [orientedIntegral]
    apply Finset.sum_congr rfl
    intro i _
    rw [← D04.ManifoldIntegralIndependence.coefficientIntegral_smul (P.sign i).val
      (D04.ManifoldIntegral.top_coefficients_integrable (surfaceFluxForm F) hI.1
        P.toChartPartition i).2.2]
    congr 1
    funext u
    dsimp only [localizedDensityCoefficient, densityCoefficient, localizedTopCoefficient]
    rw [← (D04SurfaceAssembly.normal_chart_sign o.manifold N (P.chart i) u).2.2 F]
    have hs : normalChartSign N (P.chart i) u = (P.sign i).val :=
      (ho (P.chart i) u).symm.trans (P.agrees i u)
    rw [hs]
    ring
  exact he.trans (hI.2.2.2 P).2

open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model

/-- Internal boundaries are paired by actual C¹ parameter diffeomorphisms;
lower-dimensional seams are the displayed geometric seams, not assumed
cancellation identities. -/
theorem finite_surface_stokes : finite_surface_stokesType := by
  intro q O M N compatible bO hbO m P s hregular Z hlower hself hp hcover Zbulk hover
    l p e Q tSign b deltaOut hdOut hOut houter deltaPair hdPair hPair hpair F hO hF
  have ha := D04.Dictionary.alpha_isCr 1 O F hO hF
  obtain ⟨I, hI, hB, hst⟩ := D04.FinitePiecewiseStokes.manifold_piecewise_stokes
    M bO hbO m P s hregular Z hlower hself hp hcover (fun _ => 1) e Q tSign b
    deltaOut hdOut hOut houter deltaPair hdPair hPair
    (fun i => ⟨(hpair i).1, (hpair i).2, rfl⟩) (alpha F) ha
  have hval (j : Fin q) : surfaceFlux (N j) (fun x : (M j).carrier => curl F x) = I j := by
    have hj := hI j
    rw [tangent_curl_bridge O F hO (M j).subset_domain hF] at hj
    exact flux_value_of_integral (N j) (M j).orientation (compatible j) (M j).compact
      _ (((curl_continuousOn O hO F hF).mono (M j).subset_domain).domRestrict) (I j) hj
  have hsum : (∑ j, surfaceFlux (N j) (fun x : (M j).carrier => curl F x)) =
      ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) (alpha F)) := by
    simpa only [hval, one_zsmul] using hst
  obtain ⟨D, hD, hgeom⟩ := D04.FinitePiecewiseStokes.geometric_manifold_piecewise_stokes
    M bO hbO m P s hregular Z hlower hself hp hcover Zbulk hover
    e Q tSign b deltaOut hdOut hOut houter deltaPair hdPair hPair hpair (alpha F) ha
  exact ⟨D, hD, hgeom.trans hsum.symm, hsum⟩


open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

theorem cell_flux_coefficient : cell_flux_coefficientType := by
  intro O c F u
  change beta F (cellExtension c u)
    (fun j => fderiv ℝ (cellExtension c) u (standardBasis 2 j)) = _
  have he : (fun j => fderiv ℝ (cellExtension c) u (standardBasis 2 j)) =
      ![fderiv ℝ (cellExtension c) u (standardBasis 2 0),
        fderiv ℝ (cellExtension c) u (standardBasis 2 1)] := by
    funext j
    fin_cases j <;> rfl
  rw [he, D04.Dictionary.beta_cross]
  rfl

theorem patch_work_coefficient : patch_work_coefficientType := by
  intro O P F u
  rfl

lemma cell_curl_value {O : Set (E 3)} (c : Cell 1 2 O)
    (F : E 3 → E 3) (hO : IsOpen O) (hF : CrOn 1 O F) :
    cellIntegral c (exteriorDerivative (alpha F)) = cellFlux c (curl F) := by
  apply D04.Cells.lowerIntegral_congr
  intro u hu
  change exteriorDerivative (alpha F) (cellExtension c u) _ = beta (curl F) (cellExtension c u) _
  rw [D04.Dictionary.exterior_alpha_curl O F hO hF (cellExtension c u)
    (by
      have he : cellExtension c u = (c.toFun ⟨u, hu⟩).val := (extension_spec c).2.2.2 ⟨u, hu⟩
      rw [he]
      exact (c.toFun ⟨u, hu⟩).property)]

theorem finite_cell_surface_stokes : finite_cell_surface_stokesType := by
  intro N L O c P hp outer left right b s hs hmatch hweight hassembly hi hr Z hover F hO hF
  have ha := D04.Dictionary.alpha_isCr 1 O F hO hF
  have hst := D04.FinitePiecewiseStokes.cell_piecewise_stokes_patches c (fun _ => 1) P hp
    outer left right b s hs hmatch hweight hassembly (alpha F) ha
  have hsum : (∑ j, cellFlux (c j) (curl F)) = patchChainIntegral (alpha F) outer := by
    simpa only [Int.cast_one, one_mul, cell_curl_value _ F hO hF] using hst
  obtain ⟨D, hD, he⟩ := D04.FinitePiecewiseStokes.geometric_cell_piecewise_stokes
    c P hp outer left right b s hs hmatch hweight hassembly hi hr Z hover (alpha F) ha
  exact ⟨D, hD, he.trans hsum.symm, hsum⟩

theorem surface_stokes_oriented : surface_stokes_orientedType := by
  intro M N o ho hc O F hO hMO hF
  obtain ⟨bO, hout, I, hI, hB⟩ := D04Stokes.ambient_stokes_compact o hc O (alpha F) hMO
    (D04.Dictionary.alpha_isCr 1 O F hO hF)
  rw [tangent_curl_bridge O F hO hMO hF] at hI
  have he := flux_value_of_integral N o ho hc (fun x : M => curl F x)
    (((curl_continuousOn O hO F hF).mono hMO).domRestrict) I hI
  exact ⟨bO, hout, he ▸ hI, (boundary_work_bridge bO F _).mpr (he ▸ hB)⟩

theorem positive_chart_pullback : positive_chart_pullbackType := by
  intro M N o ho F c u hp
  have he := positive_chart_flux N o ho F c u hp
  have hx := (tangentPullback (tangentRestriction 1 2 M (beta F)) c u u.property).eq_smul_basis_det
    (standardBasis 2)
  exact ⟨hx.trans (congrArg (fun a : ℝ => a • omega 2) he.1),
    hx.trans (congrArg (fun a : ℝ => a • omega 2) he.2)⟩

theorem chart_unit_tangent_positive : chart_unit_tangent_positiveType := by
  intro B bO c u
  let y : B := chartPoint c u
  let ori := bO.atPoint y y.property
  let b := ori.finOrthonormalBasis (by norm_num : 0 < 1)
    (D04.tangentSpace_finrank bO.manifold y y.property)
  have hb : b.toBasis.orientation = ori := ori.finOrthonormalBasis_orientation
    (by norm_num) (D04.tangentSpace_finrank bO.manifold y y.property)
  let v := tangentChartMap c u u.property (standardBasis 1 0)
  let a : ℝ := b.toBasis.repr v 0
  have hv : v = a • b 0 := by
    have hh := (b.toBasis.sum_repr v).symm
    simp only [Fin.sum_univ_one] at hh
    convert hh using 1 <;> rfl
  have hvval : chartDifferential c u (standardBasis 1 0) = a • (b 0).val :=
    congrArg Subtype.val hv
  have ha : a ≠ 0 := by
    intro hz
    have hv0 : chartDifferential c u (standardBasis 1 0) = chartDifferential c u 0 := by
      rw [hvval, hz, zero_smul, map_zero]
    exact (standardBasis 1).ne_zero 0
      (D04.EmbeddedChart.differential_injective c bO.manifold.1 u.property hv0)
  have hp : 0 < ori.someVector b.toBasis :=
    (D04.Orientations.representative_pos_iff ori b.toBasis).mpr hb
  change 0 < ori.someVector b at hp
  have hs : chartSign bO.atPoint c u u.property = Real.sign a := by
    have ht : (fun i : Fin 1 => tangentChartMap c u u.property (standardBasis 1 i)) =
        fun i => a • b i := by
      funext i
      fin_cases i
      exact hv
    change Real.sign (ori.someVector (fun i => tangentChartMap c u u.property (standardBasis 1 i))) = _
    rw [ht, AlternatingMap.map_smul_univ, Fin.prod_univ_one, smul_eq_mul,
      D04.Orientations.sign_mul, Real.sign_of_pos hp, mul_one]
  refine ⟨b, hb, ?_⟩
  change (b 0).val = (chartSign bO.atPoint c u u.property /
    ‖chartDifferential c u (standardBasis 1 0)‖) • chartDifferential c u (standardBasis 1 0)
  rw [hs, hvval, norm_smul, show ‖(b 0).val‖ = 1 from b.norm_eq_one 0,
    Real.norm_eq_abs, mul_one, smul_smul]
  have he : Real.sign a / |a| * a = 1 := by
    rcases lt_or_gt_of_ne ha with hn | hp
    · rw [Real.sign_of_neg hn, abs_of_neg hn]
      field_simp
    · rw [Real.sign_of_pos hp, abs_of_pos hp]
      field_simp
  rw [he, one_smul]

theorem cell_flux_geometric : cell_flux_geometricType := by
  intro O c F hF
  have hb := D04.Dictionary.beta_isCr 0 O F c.open_target hF
  have hc := D04.Cells.cellCoefficient_continuous c (beta F) hb
  have he := D04Stokes.box_integral_eq_region (cubeBox 2) (fun _ => zero_lt_one)
    (cellCoefficient c (beta F)) hc
  apply he.trans
  change Specs.D04.C06.JordanRegions.Model.regionIntegral
    (fun x : cube 2 => cellCoefficient c (beta F) x) = _
  congr 1
  funext x
  convert cell_flux_coefficient c F x using 1 <;> rfl

end D04.ClassicalSurfaceStokes
