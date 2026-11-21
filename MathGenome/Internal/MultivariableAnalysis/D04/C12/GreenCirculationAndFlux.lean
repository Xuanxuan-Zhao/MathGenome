import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C12.RegularDomainRiemannManifoldBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C15.FinitePiecewiseStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.D04.C14.MetricTopFormsAndDensities
import Mathlib.Tactic.Linarith
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Function Topology
open scoped ContDiff BigOperators
namespace D04.Green
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.GreenCirculationAndFlux
open Model

abbrev circulationForm := Model.circulationForm
abbrev planarFluxForm := Model.planarFluxForm
abbrev circulationDensity := Model.circulationDensity
abbrev divergenceDensity := Model.divergenceDensity

lemma circulation_apply (P Q : E 2 → ℝ) (x : E 2) (v : Fin 1 → E 2) :
    circulationForm P Q x v = P x * v 0 0 + Q x * v 0 1 := rfl

lemma flux_apply (P Q : E 2 → ℝ) (x : E 2) (v : Fin 1 → E 2) :
    planarFluxForm P Q x v = P x * v 0 1 - Q x * v 0 0 := by
  change -Q x * v 0 0 + P x * v 0 1 = _
  ring

lemma partial_neg (f : E 2 → ℝ) (x : E 2) (i : Fin 2) :
    scalarPartialDerivative (fun y => -f y) x i = -scalarPartialDerivative f x i := by
  change deriv (fun t : ℝ => -f (x + t • standardBasis 2 i)) 0 =
    -deriv (fun t : ℝ => f (x + t • standardBasis 2 i)) 0
  exact deriv.neg

theorem exterior_derivatives : exterior_derivativesType := by
  intro U P Q hU hP hQ x hx
  refine ⟨D04.Dictionary.planar_derivative U P Q hU hP hQ x hx, ?_⟩
  have hn : CrOn 1 U (fun x => -Q x) :=
    (D04.crOn_iff_contDiffOn 1 U _ hU).mpr
      (((D04.crOn_iff_contDiffOn 1 U Q hU).mp hQ).neg)
  have h := D04.Dictionary.planar_derivative U (fun x => -Q x) P hU hn hP x hx
  change exteriorDerivative (planarFluxForm P Q) x =
    (scalarPartialDerivative P x 0 - scalarPartialDerivative (fun x => -Q x) x 1) • omega 2 at h
  rw [partial_neg] at h
  change exteriorDerivative (planarFluxForm P Q) x =
    (scalarPartialDerivative P x 0 + scalarPartialDerivative Q x 1) • omega 2
  simpa only [sub_neg_eq_add] using h

theorem line_coefficient : line_coefficientType := by
  intro M P Q c u
  exact circulation_apply P Q _ _

lemma circulation_regular (U : Set (E 2)) (P Q : E 2 → ℝ)
    (hU : IsOpen U) (hP : CrOn 1 U P) (hQ : CrOn 1 U Q) :
    IsCrForm (some 1) U (circulationForm P Q) := by
  have hF : CrOn 1 U (fun x => WithLp.toLp 2 ![P x,Q x]) := by
    apply (D04.crOn_iff_contDiffOn 1 U _ hU).mpr
    apply contDiffOn_euclidean.mpr
    intro i
    fin_cases i
    · exact (D04.crOn_iff_contDiffOn 1 U P hU).mp hP
    · exact (D04.crOn_iff_contDiffOn 1 U Q hU).mp hQ
  have he : circulationForm P Q = alpha (fun x => WithLp.toLp 2 ![P x,Q x]) := by
    funext x
    ext v
    change P x * v 0 0 + Q x * v 0 1 = inner ℝ (WithLp.toLp 2 ![P x,Q x]) (v 0)
    rw [D04.inner_coordinates, Fin.sum_univ_two]
    rfl
  rw [he]
  exact D04.Dictionary.alpha_isCr 1 U _ hU hF

lemma flux_regular (U : Set (E 2)) (P Q : E 2 → ℝ)
    (hU : IsOpen U) (hP : CrOn 1 U P) (hQ : CrOn 1 U Q) :
    IsCrForm (some 1) U (planarFluxForm P Q) := by
  apply circulation_regular U (fun x => -Q x) P hU _ hP
  exact (D04.crOn_iff_contDiffOn 1 U _ hU).mpr
    (((D04.crOn_iff_contDiffOn 1 U Q hU).mp hQ).neg)

/-- Algebraic metric calculation underlying the outward-first convention. -/
lemma unit_normal_rotation (ν τ : E 2) (hn : ‖ν‖ = 1) (ht : ‖τ‖ = 1)
    (ho : inner ℝ ν τ = 0) (hp : 0 < omega 2 ![ν,τ]) :
    τ 0 = -ν 1 ∧ τ 1 = ν 0 := by
  have hi (v w : E 2) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]
  have nn : ν 0 ^ 2 + ν 1 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq ν
    rw [hi, hn] at h
    change ν 0 * ν 0 + ν 1 * ν 1 = 1 ^ 2 at h
    nlinarith
  have tt : τ 0 ^ 2 + τ 1 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq τ
    rw [hi, ht] at h
    change τ 0 * τ 0 + τ 1 * τ 1 = 1 ^ 2 at h
    nlinarith
  have dot : ν 0 * τ 0 + ν 1 * τ 1 = 0 := by rwa [hi] at ho
  have detpos : 0 < ν 0 * τ 1 - τ 0 * ν 1 := by
    change 0 < Matrix.det (fun i j : Fin 2 => (![ν,τ] j) i) at hp
    rw [Matrix.det_fin_two] at hp
    exact hp
  have identity : (ν 0 * τ 1 - τ 0 * ν 1)^2 + (ν 0 * τ 0 + ν 1 * τ 1)^2 =
      (ν 0^2 + ν 1^2) * (τ 0^2 + τ 1^2) := by ring
  rw [nn, tt, dot] at identity
  have det : ν 0 * τ 1 - τ 0 * ν 1 = 1 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (τ 0 + ν 1), sq_nonneg (τ 1 - ν 0)]


theorem boundary_tangent_normal : boundary_tangent_normalType := by
  intro D hD hb o ho bO hout x b hbor
  obtain ⟨ν, hνcont, hν, hpos⟩ := hout
  let n := outwardNormal hD ⟨x, hb ▸ x.property⟩
  have hn : IsOutwardUnitConormal 1 1 (closure D) x n :=
    D04.RegularDomainGeometry.outward_normal_conormal hD ⟨x, hb ▸ x.property⟩
  have he : ν x = n := (D04BoundaryOrientation.conormal_exists_unique
    o.manifold x x.property).unique (hν x) hn
  obtain ⟨B, hB0, hB1, hBor⟩ := (hpos x b.toBasis).mp hbor
  have hp : 0 < omega 2 ![n,(b 0).val] := by
    have h := (ho ⟨x, x.property.1⟩ B).mp hBor
    have hvec : (fun i => (B i).val) = ![n,(b 0).val] := by
      funext i
      fin_cases i
      · exact hB0.trans he
      · exact hB1 0
    rwa [hvec] at h
  have ht : ‖(b 0).val‖ = 1 := b.norm_eq_one 0
  have ortho := hn.2.2.1 (b 0).val (b 0).property
  obtain ⟨h0,h1⟩ := unit_normal_rotation n (b 0).val hn.2.1 ht ortho hp
  exact ⟨h0,h1,h1.symm, by linarith⟩

theorem flux_field_identification : flux_field_identificationType := by
  intro D hD hb o ho bO hout P Q
  funext x
  let b := (bO.atPoint x x.property).finOrthonormalBasis (by norm_num)
    (D04.tangentSpace_finrank bO.manifold x x.property)
  have hbor : b.toBasis.orientation = bO.atPoint x x.property :=
    Orientation.finOrthonormalBasis_orientation _ _ _
  have hrot := boundary_tangent_normal hD hb o ho bO hout x b hbor
  apply b.toBasis.ext_alternating
  intro v _
  have hv : v = fun _ => 0 := by funext i; exact Subsingleton.elim _ _
  subst v
  change planarFluxForm P Q x (fun i => (b 0).val) =
    (P x * outwardNormal hD ⟨x, hb ▸ x.property⟩ 0 +
      Q x * outwardNormal hD ⟨x, hb ▸ x.property⟩ 1) *
      metricVolume bO.atPoint x (fun _ => b 0)
  have he : (fun _ : Fin 1 => b 0) = b := by funext i; congr 1; exact Subsingleton.elim _ _
  rw [he, D04MetricDensity.metricVolume_normalized bO.manifold bO.atPoint x b hbor,
    mul_one, flux_apply, hrot.1, hrot.2.1]
  ring

lemma outwardFirst_unique {M : Set (E 2)} (o : PositiveManifoldOrientation 1 2 M)
    (b c : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 M))
    (hb : OutwardFirst 1 o b) (hc : OutwardFirst 1 o c) : b = c := by
  obtain ⟨ν, _, hν, hpos⟩ := hb
  obtain ⟨μ, _, hμ, hpos'⟩ := hc
  have he : μ = ν := by
    funext x
    exact (D04BoundaryOrientation.conormal_exists_unique o.manifold x x.property).unique
      (hμ x) (hν x)
  subst μ
  exact (D04BoundaryOrientation.boundary_orientation o ν hν).unique hpos hpos'

/-- Stokes with a fixed outward-first orientation, followed by the actual
full-dimensional Riemann bridge. -/
lemma green_for_form {D : Set (E 2)} (hD : IsClassicalRegularDomain D)
    (o : PositiveManifoldOrientation 1 2 (closure D)) (ho : IsAmbientOrientation o)
    (bO : PositiveManifoldOrientation 1 1 (intrinsicBoundary 1 2 (closure D)))
    (hbO : OutwardFirst 1 o bO) (U : Set (E 2)) (hKU : closure D ⊆ U)
    (η : FormField 2 1) (hη : IsCrForm (some 1) U η)
    (f : E 2 → ℝ) (hf : ContinuousOn f U)
    (hd : ∀ x ∈ U, exteriorDerivative η x = f x • omega 2) :
    RegionIntegrable (fun x : D => f x) ∧
    HasPositiveIntegral bO (tangentRestriction 1 1 (intrinsicBoundary 1 2 (closure D)) η)
      (regionIntegral (fun x : D => f x)) := by
  obtain ⟨b, hb, I, hI, hJ⟩ := D04Stokes.ambient_stokes_compact o
    (D04.RegularDomainGeometry.closure_manifold hD).1 U η hKU hη
  have he := outwardFirst_unique o b bO hb hbO
  subst b
  have hfield : tangentRestriction 1 2 (closure D) (exteriorDerivative η) =
      volumeField (fun x : closure D => f x) := by
    funext x
    rw [tangentRestriction, hd x (hKU x.property)]
    rfl
  rw [hfield] at hI
  have hfc : Continuous (fun x : closure D => f x) :=
    (hf.mono hKU).domRestrict
  have hi := D04.RegularDomainGeometry.continuous_integral hD _ hfc
  refine ⟨hi.2.1, ?_⟩
  obtain ⟨A⟩ := hI.2.2.1
  have hval : I = regionIntegral (fun x : D => f x) :=
    ((hI.2.2.2 A).2).symm.trans
      ((D04.RegularDomainBridge.manifold_integral_eq_region hD o ho _ hfc A).trans hi.2.2)
  rwa [hval] at hJ

theorem green : greenType := by
  intro D hD U P Q hU hKU hP hQ
  obtain ⟨o, ho⟩ := D04.RegularDomainBridge.ambient_orientation_exists
    hD.dimension (D04.RegularDomainGeometry.closure_manifold hD).2
  obtain ⟨bO, hbO⟩ := D04Stokes.outwardFirst_exists o
  have hb := D04.RegularDomainGeometry.intrinsic_boundary hD
  have hpc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative P x i) U :=
    D04.crOn_scalarPartialDerivative 0 U P hU hP i
  have hqc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative Q x i) U :=
    D04.crOn_scalarPartialDerivative 0 U Q hU hQ i
  have hc := green_for_form hD o ho bO hbO U hKU (circulationForm P Q)
    (circulation_regular U P Q hU hP hQ) (circulationDensity P Q)
    ((hqc 0).sub (hpc 1)) (fun x hx => (exterior_derivatives U P Q hU hP hQ x hx).1)
  have hf := green_for_form hD o ho bO hbO U hKU (planarFluxForm P Q)
    (flux_regular U P Q hU hP hQ) (divergenceDensity P Q)
    ((hpc 0).add (hqc 1)) (fun x hx => (exterior_derivatives U P Q hU hP hQ x hx).2)
  refine ⟨hb, o, bO, ho, hbO, hc.1, hf.1, hc.2, hf.2, ?_⟩
  rw [← flux_field_identification hD hb o ho bO hbO P Q]
  exact hf.2

lemma circulation_eq_alpha (P Q : E 2 → ℝ) :
    circulationForm P Q = alpha (fun x => WithLp.toLp 2 ![P x,Q x]) := by
  funext x
  ext v
  change P x * v 0 0 + Q x * v 0 1 = inner ℝ (WithLp.toLp 2 ![P x,Q x]) (v 0)
  rw [D04.inner_coordinates, Fin.sum_univ_two]
  rfl

lemma exterior_circulation_all (P Q : E 2 → ℝ) :
    exteriorDerivative (circulationForm P Q) = fun x => circulationDensity P Q x • omega 2 := by
  funext x
  rw [circulation_eq_alpha]
  change D04.exteriorDerivative (D04.Dictionary.alpha (fun x => WithLp.toLp 2 ![P x,Q x])) x = _
  rw [D04.Dictionary.exterior_alpha_formula]
  simp [Fin.sum_univ_two, D04.Dictionary.coordinateOne_wedge_omega_two,
    circulationDensity, Model.circulationDensity]
  rfl

lemma exterior_flux_all (P Q : E 2 → ℝ) :
    exteriorDerivative (planarFluxForm P Q) = fun x => divergenceDensity P Q x • omega 2 := by
  change exteriorDerivative (circulationForm (fun x => -Q x) P) = _
  rw [exterior_circulation_all]
  funext x
  change (scalarPartialDerivative P x 0 - scalarPartialDerivative (fun y => -Q y) x 1) • omega 2 = _
  rw [partial_neg]
  change (scalarPartialDerivative P x 0 - -scalarPartialDerivative Q x 1) • omega 2 =
    (scalarPartialDerivative P x 0 + scalarPartialDerivative Q x 1) • omega 2
  rw [sub_neg_eq_add]

open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

/-- Actual geometric cell unions, retaining their prescribed outer boundary
and every signed internal matching. The two bulk integrands are the displayed
scalar densities times the standard planar volume covector. -/
theorem geometric_cell_green : geometric_cell_greenType := by
  intro N L O c P hP outer left right b s hs hrep hw heq hi hr Z hZ f g hO hf hg
  have h (η : FormField 2 1) (hη : IsCrForm (some 1) O η) :=
    D04.FinitePiecewiseStokes.geometric_cell_piecewise_stokes c P hP outer left right b s
      hs hrep hw heq hi hr Z hZ η hη
  constructor
  · simpa only [exterior_circulation_all] using h (circulationForm f g) (circulation_regular O f g hO hf hg)
  · simpa only [exterior_flux_all] using h (planarFluxForm f g) (flux_regular O f g hO hf hg)

/-- Compact manifold pieces, including disconnected unions and holes. Boundary
occurrences are enumerated by outer pieces and cancelling internal pairs. -/
theorem geometric_manifold_green : geometric_manifold_greenType := by
  intro q O M bO hbO m P s hreg Z hdim hself hover hcover Zbulk hbulk
    l p e Q tSign b deltaOut hdelta hOut hout deltaPair hdeltaPair hPair hpair
    f g hO hf hg
  have h (η : FormField 2 1) (hη : IsCrForm (some 1) O η) :=
    D04.FinitePiecewiseStokes.geometric_manifold_piecewise_stokes M bO hbO m P s
      hreg Z hdim hself hover hcover Zbulk hbulk e Q tSign b deltaOut hdelta
      hOut hout deltaPair hdeltaPair hPair hpair η hη
  constructor
  · simpa only [exterior_circulation_all] using h (circulationForm f g) (circulation_regular O f g hO hf hg)
  · simpa only [exterior_flux_all] using h (planarFluxForm f g) (flux_regular O f g hO hf hg)

open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model

abbrev rightUnitNormal := Model.rightUnitNormal
abbrev normalFluxField := @Model.normalFluxField

theorem flux_speed : flux_speedType := by
  intro P Q x v
  rw [flux_apply]
  by_cases hv : v = 0
  · subst v
    simp [Model.rightUnitNormal]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    change P x * v 1 - Q x * v 0 =
      (P x * (‖v‖⁻¹ * v 1) + Q x * (‖v‖⁻¹ * -v 0)) * ‖v‖
    field_simp
    ring

lemma rightUnitNormal_unit (v : E 2) (hv : v ≠ 0) : ‖rightUnitNormal v‖ = 1 := by
  have he : ‖WithLp.toLp 2 ![v 1,-v 0]‖ = ‖v‖ := by
    simp [D04.norm_coordinates, Fin.sum_univ_two, add_comm]
  change ‖‖v‖⁻¹ • WithLp.toLp 2 ![v 1,-v 0]‖ = 1
  rw [norm_smul, norm_inv, norm_norm, he, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem circulation_work_integrable : circulation_work_integrableType := by
  intro a b γ d P Q
  change OneFormIntegrable d (circulationForm P Q) ↔ _
  rw [circulation_eq_alpha]
  exact D04.Dictionary.alpha_integrable_iff d _

theorem circulation_work : circulation_workType := by
  intro a b γ d P Q ha hw
  have he : Model.circulationForm P Q = alpha (fun x => WithLp.toLp 2 ![P x,Q x]) :=
    circulation_eq_alpha P Q
  revert ha
  rw [he]
  intro ha
  exact D04.Dictionary.alpha_integral_work d _ ha hw

theorem cell_volume_coefficient : cell_volume_coefficientType := by
  intro O c f u
  change f (cellExtension c u) *
    (standardBasis 2).det ((fderiv ℝ (cellExtension c) u).toLinearMap ∘ standardBasis 2) = _
  rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem patch_line_coefficients : patch_line_coefficientsType := by
  intro O C P Q u
  constructor
  · exact circulation_apply P Q _ _
  · exact flux_speed P Q (C.map u) (fderiv ℝ C.map u (standardBasis 1 0))

theorem cell_chain_green : cell_chain_greenType := by
  intro N P O V c a outer refined left right b s hassembly hrep heq f g hV hf hg hc hr
  have h (η : FormField 2 1) (hη : IsCrForm (some 1) V η) :=
    D04.FinitePiecewiseStokes.cell_piecewise_stokes_refined c a outer refined
      left right b s hassembly hrep heq η hη hc hr
  constructor
  · simpa only [exterior_circulation_all] using h (circulationForm f g) (circulation_regular V f g hV hf hg)
  · simpa only [exterior_flux_all] using h (planarFluxForm f g) (flux_regular V f g hV hf hg)

lemma positive_cell_region {O : Set (E 2)} (c : Cell 1 2 O)
    (hi : InjOn (cellExtension c) (cube 2))
    (hd : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (f : E 2 → ℝ) (hf : ContinuousOn f O) :
    Jordan (cellExtension c '' cube 2) ∧
    RegionIntegrable (fun x : cellExtension c '' cube 2 => f x) ∧
    cellIntegral c (fun x => f x • omega 2) =
      regionIntegral (fun x : cellExtension c '' cube 2 => f x) := by
  have hK : IsCompact (cube 2) := D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)
  have hdom : cube 2 ⊆ extensionDomain c := (extension_spec c).2.1
  obtain ⟨e, he, hKe, _, hC, hCi⟩ := D04.FinitePiecewiseStokes.compact_parameter_extension
    (cube 2) (cellExtension c) (extensionDomain c) hK (extension_spec c).1
    hdom (D04.Cells.extension_C1 c) hi (fun x hx => ne_of_gt (hd x hx))
  have hcl : closure (cube 2) = cube 2 := hK.isClosed.closure_eq
  have hKcl : closure (cube 2) ⊆ e.source := by rw [hcl]; exact hKe
  have hJ := (D04.RegionSubstitution.jordan_image e hC hCi (cube 2)
    (D04.OneCoordinate.Boxes.jordan_carrier (cubeBox 2)) hK.closure hKcl).2
  have heI : e '' cube 2 = cellExtension c '' cube 2 := by rw [he]
  have hI : IsCompact (e '' cube 2) := hK.image_of_continuousOn (hC.continuousOn.mono hKe)
  have hIO : e '' cube 2 ⊆ O := by
    rintro y ⟨x, hx, rfl⟩
    rw [he]
    change D04.Cells.cellExtension c x ∈ O
    rw [D04.Cells.extension_on_cube c ⟨x,hx⟩]
    exact (c.toFun ⟨x,hx⟩).property
  have hif : RegionIntegrable (fun x : e '' cube 2 => f x) :=
    D04.JordanRegions.integrable_continuous_on_closure (by norm_num) hJ (fun x => f x)
      ((hf.mono (by rwa [hI.isClosed.closure_eq])).domRestrict)
  have hsub := D04.RegionSubstitution.region_substitution e hC hCi (cube 2)
    (D04.OneCoordinate.Boxes.jordan_carrier (cubeBox 2)) hK.closure hKcl
    (fun x : e '' cube 2 => f x) hif.1
  have hv := hsub.2.2 (Or.inl hif)
  have hp : (fun x : cube 2 => f (e x) * |(fderiv ℝ e x).det|) =
      (fun x : cube 2 => f (cellExtension c x) * (fderiv ℝ (cellExtension c) x).det) := by
    funext x
    rw [he, abs_of_pos (hd x x.property)]
  rw [hp, heI] at hv
  rw [heI] at hJ hif
  refine ⟨hJ, hif, ?_⟩
  have hfc : ContinuousOn (fun x => f (cellExtension c x)) (cube 2) :=
    hf.comp ((D04.Cells.extension_C1 c).continuousOn.mono hdom) (by
      intro x hx
      change D04.Cells.cellExtension c x ∈ O
      rw [D04.Cells.extension_on_cube c ⟨x,hx⟩]
      exact (c.toFun ⟨x,hx⟩).property)
  have hdc : ContinuousOn (fun x => (fderiv ℝ (cellExtension c) x).det) (cube 2) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (((D04.Cells.extension_C1 c).continuousOn_fderiv_of_isOpen
        (extension_spec c).1 le_rfl).mono hdom)
  have hcoef : ContinuousOn (cellCoefficient c (fun x => f x • omega 2)) (cube 2) :=
    (hfc.mul hdc).congr (fun x _ => cell_volume_coefficient c f x)
  change D04.Darboux.lowerIntegral (cellCoefficient c (fun x => f x • omega 2)) (cubeBox 2) = _
  rw [D04Stokes.box_integral_eq_region (cubeBox 2) (fun i => by norm_num [cubeBox]) _ hcoef]
  calc
    _ = regionIntegral (fun x : cube 2 => f (cellExtension c x) *
        (fderiv ℝ (cellExtension c) x).det) := by
      congr 1
      funext x
      exact cell_volume_coefficient c f x
    _ = _ := hv.symm

lemma planar_seams_contentZero (Z : AmbientSeams 2 2) :
    Specs.D04.C06.NullCovers.Model.ContentZero Z.carrier := by
  let c := D04.RegularDomainGeometry.interiorChart (isOpen_univ : IsOpen (univ : Set (E 2)))
  have h := (D04.GeometricUnion.chart_seams_contentZero c le_rfl Z Z.carrier Z.isCompact
    (by intro x hx; exact ⟨by simp, mem_univ x⟩)).2
  change Specs.D04.C06.NullCovers.Model.ContentZero (id '' (Z.carrier ∩ Z.carrier)) at h
  simpa only [inter_self, image_id] using h

lemma positive_cell_union {N : ℕ} {O : Set (E 2)} (c : Fin N → Cell 1 2 O)
    (hi : ∀ j, InjOn (cellExtension (c j)) (cube 2))
    (hd : ∀ j x, x ∈ cube 2 → 0 < (fderiv ℝ (cellExtension (c j)) x).det)
    (Z : AmbientSeams 2 2)
    (hZ : ∀ i j, i ≠ j → (cellExtension (c i) '' cube 2) ∩
      (cellExtension (c j) '' cube 2) ⊆ Z.carrier)
    (f : E 2 → ℝ) (hf : ContinuousOn f O) :
    Jordan (⋃ j, cellExtension (c j) '' cube 2) ∧
    RegionIntegrable (fun x : (⋃ j, cellExtension (c j) '' cube 2) => f x) ∧
    regionIntegral (fun x : (⋃ j, cellExtension (c j) '' cube 2) => f x) =
      ∑ j, cellIntegral (c j) (fun x => f x • omega 2) := by
  have hdata j := positive_cell_region (c j) (hi j) (hd j) f hf
  have hK : IsCompact (⋃ j, cellExtension (c j) '' cube 2) := by
    apply isCompact_iUnion
    intro j
    apply (D04.DiscontinuityCriterion.carrier_compact (cubeBox 2)).image_of_continuousOn
    exact (D04.Cells.extension_C1 (c j)).continuousOn.mono (extension_spec (c j)).2.1
  have hU : (⋃ j, cellExtension (c j) '' cube 2) ⊆ O := by
    rintro x hx
    obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.mp hx
    change D04.Cells.cellExtension (c j) u ∈ O
    rw [D04.Cells.extension_on_cube (c j) ⟨u,hu⟩]
    exact ((c j).toFun ⟨u,hu⟩).property
  have hcoord := D04.GeometricUnion.coordinate_union_integral
    (fun j => cellExtension (c j) '' cube 2) (fun j => (hdata j).1)
    Z.carrier (planar_seams_contentZero Z) hZ f
    (hf.mono (by rwa [hK.isClosed.closure_eq]))
  refine ⟨hcoord.1,hcoord.2.1,hcoord.2.2.trans ?_⟩
  exact Finset.sum_congr rfl (fun j _ => (hdata j).2.2.symm)

theorem riemann_cell_green : riemann_cell_greenType := by
  intro N L O c P hP outer left right b s hs hrep hw heq hi hd Z hZ f g hO hf hg
  have hpc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative f x i) O :=
    D04.crOn_scalarPartialDerivative 0 O f hO hf i
  have hqc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative g x i) O :=
    D04.crOn_scalarPartialDerivative 0 O g hO hg i
  have hcir := positive_cell_union c hi hd Z hZ (circulationDensity f g)
    ((hqc 0).sub (hpc 1))
  have hflux := positive_cell_union c hi hd Z hZ (divergenceDensity f g)
    ((hpc 0).add (hqc 1))
  have h (η : FormField 2 1) (hη : IsCrForm (some 1) O η) :
      (∑ j, cellIntegral (c j) (exteriorDerivative η)) = patchChainIntegral η outer := by
    simpa only [Int.cast_one, one_mul] using
      D04.FinitePiecewiseStokes.cell_piecewise_stokes_patches c (fun _ => 1) P hP
        outer left right b s hs hrep hw heq η hη
  refine ⟨hcir.1,hcir.2.1,hflux.2.1,hcir.2.2.trans ?_,hflux.2.2.trans ?_⟩
  · simpa only [exterior_circulation_all] using
      h (circulationForm f g) (circulation_regular O f g hO hf hg)
  · simpa only [exterior_flux_all] using
      h (planarFluxForm f g) (flux_regular O f g hO hf hg)


open Specs.D04.C15.DirectedSubstitution.Model
open private inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

/-- Full-dimensional charts can be refined to restrictions of genuine ambient
C¹ diffeomorphisms, including at points of the flat boundary. -/
lemma compact_piece_ambient_chart {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (x : M) :
    ∃ C : D04.RegularDomainBridge.AmbientChart M, (x : E n) ∈ C.chart.ambient := by
  obtain ⟨c, u, hu, hcu⟩ := hM.2.2 x x.property
  obtain ⟨W, g, hW, huW, hgc, hg, hgr⟩ := c.regular u hu.1
  let A := (LinearEquiv.ofInjectiveEndo (fderiv ℝ g u).toLinearMap
    (hgr u huW)).toContinuousLinearEquiv
  obtain ⟨X, Y, q, hI, hq⟩ := inverse_neighborhood W g u A le_rfl hW hg huW rfl
  obtain ⟨hX,hY,huX,hguY,hXW,hbij,hqX,hleft,hright,_⟩ := hI
  obtain ⟨d, hds, hda, hdf, hdi, hdh⟩ := D04.embeddedChart_restrict_parameter c X hX
  obtain ⟨a, hah, has, haa, haf, hai⟩ := D04.embeddedChart_restrict d Y hY
  have haX : a.source ⊆ X := by
    rw [has,hds]
    exact fun _ hv => hv.1.2
  have hac : a.source ⊆ c.source := by
    rw [has,hds]
    exact fun _ hv => hv.1.1
  have hafg : EqOn a.toFun g a.source := by
    intro v hv
    rw [haf,hdf]
    exact (hgc ⟨hac hv,hXW (haX hv)⟩).symm
  have hagu : a.toFun u = x := by
    rw [haf,hdf,hcu]
  have hus : u ∈ a.source := by
    rw [has,hds]
    refine ⟨⟨hu.1,huX⟩,?_⟩
    change d.toFun u ∈ Y
    rw [hdf,← hgc ⟨hu.1,huW⟩]
    exact hguY
  have hax : (x : E n) ∈ a.ambient := hagu ▸ (a.map_source hus).2
  let e : OpenPartialHomeomorph (E n) (E n) := {
    toFun := g
    invFun := q
    source := X ∩ g ⁻¹' a.ambient
    target := a.ambient
    map_source' := fun _ hv => hv.2
    map_target' := by
      intro y hy
      have hyY : y ∈ Y := by rw [haa] at hy; exact hy.2
      exact ⟨hqX hyY, by change g (q y) ∈ a.ambient; rwa [hright hyY]⟩
    left_inv' := fun _ hv => hleft hv.1
    right_inv' := by
      intro y hy
      exact hright (by rw [haa] at hy; exact hy.2)
    open_source := (hg.continuousOn.mono hXW).isOpen_inter_preimage hX a.ambient_open
    open_target := a.ambient_open
    continuousOn_toFun := hg.continuousOn.mono (inter_subset_left.trans hXW)
    continuousOn_invFun := hq.continuousOn.mono (by rw [haa]; exact inter_subset_right) }
  refine ⟨⟨a,e,hg.mono (inter_subset_left.trans hXW),
    hq.mono (by change a.ambient ⊆ Y; rw [haa]; exact inter_subset_right),?_,rfl,
    hafg,?_⟩,hax⟩
  · intro v hv
    exact ⟨haX hv, by change g v ∈ a.ambient; rw [← hafg hv]; exact (a.map_source hv).2⟩
  · intro v hv
    exact D04.chartDifferential_extension a hM.1 v hv W g hW (hXW (haX hv))
      (fun w hw => (hafg hw.1).symm)
      ((hg.contDiffAt (hW.mem_nhds (hXW (haX hv)))).differentiableAt one_ne_zero)


/-- Compact full-dimensional manifolds are Jordan sets, by a finite cover of
compact Jordan cores in ambient inverse-function charts. -/
lemma compact_piece_jordan {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (hK : IsCompact M) : Jordan M := by
  classical
  have hlocal (x : M) : ∃ (T V : Set (E n)), Jordan T ∧ T ⊆ M ∧
      IsOpen V ∧ (x : E n) ∈ V ∧ M ∩ V ⊆ T := by
    obtain ⟨C,hxC⟩ := compact_piece_ambient_chart hM x
    let c := C.chart
    let u := c.invFun x
    have hu : u ∈ c.source := c.map_target ⟨x.property,hxC⟩
    obtain ⟨W,hW,hSW⟩ := c.source_open
    obtain ⟨Q,huQ,hnd,hQ⟩ := D04.OneCoordinate.Boxes.exists_closed_box
      (hW.inter C.extension.open_source) u ⟨(hSW ▸ hu).2,C.source_subset hu⟩
    let K := D04.Darboux.carrier Q ∩ parameterSpace n c.half
    have hKS : K ⊆ c.source := by
      intro v hv
      exact hSW ▸ ⟨hv.2,(hQ hv.1).1⟩
    have hKe : K ⊆ C.extension.source := hKS.trans C.source_subset
    have hKc : IsCompact K := (D04.DiscontinuityCriterion.carrier_compact Q).inter_right
      (D04.DirectedSubstitution.parameterSpace_closed n c.half)
    have hKJ : Jordan K := D04.GeometricUnion.parameter_box_jordan Q c.half
    have hTJ : Jordan (C.extension '' K) :=
      (D04.RegionSubstitution.jordan_image C.extension C.regular C.inverse_regular K hKJ
        hKc.closure (by rwa [hKc.isClosed.closure_eq])).2
    have hTM : C.extension '' K ⊆ M := by
      rintro y ⟨v,hv,rfl⟩
      rw [← C.agrees (hKS hv)]
      exact (c.map_source (hKS hv)).1
    obtain ⟨V,hV,hVe⟩ := continuousOn_iff'.mp c.continuous_invFun
      (interior (D04.Darboux.carrier Q)) isOpen_interior
    have hxV : (x : E n) ∈ V := by
      have hv : (x : E n) ∈ c.invFun ⁻¹' interior (D04.Darboux.carrier Q) ∩
          (M ∩ c.ambient) := ⟨huQ,x.property,hxC⟩
      rw [hVe] at hv
      exact hv.1
    refine ⟨C.extension '' K,c.ambient ∩ V,hTJ,hTM,c.ambient_open.inter hV,
      ⟨hxC,hxV⟩,?_⟩
    intro y hy
    have hym : y ∈ M ∩ c.ambient := ⟨hy.1,hy.2.1⟩
    have hyv : y ∈ V ∩ (M ∩ c.ambient) := ⟨hy.2.2,hym⟩
    rw [← hVe] at hyv
    have hys := c.map_target hym
    refine ⟨c.invFun y,⟨interior_subset hyv.1,(hSW ▸ hys).1⟩,?_⟩
    exact (C.agrees hys).symm.trans (c.right_inv y hym)
  choose T V hT hTM hV hxV hcover using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have heq : M = ⋃ i : s, T i.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨i,hi⟩,hcover i ⟨hx,hxi⟩⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hTM i.val hi
  rw [heq]
  simpa only [Finset.mem_univ,iUnion_true] using
    D04.JordanRegions.jordan_finite_union Finset.univ (fun i : s => T i.val)
      (fun i _ => hT i.val)

lemma compact_piece_partition {n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 n M) (hK : IsCompact M) :
    ∃ (Q : ChartPartition 1 n M univ)
      (C : Fin Q.count → D04.RegularDomainBridge.AmbientChart M), ∀ i, (C i).chart = Q.chart i := by
  classical
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hK
  choose C hC using fun p : (univ : Set M) => compact_piece_ambient_chart hM p.val
  obtain ⟨m,a,p,w,hw,hs⟩ := D04.FiniteCompactPartition.finite_partition_refined
    hM univ isCompact_univ (fun _ : Unit => (univ : Set M))
    (fun _ => isOpen_univ) (by intro x hx; exact mem_iUnion.mpr ⟨(),mem_univ _⟩)
    (fun p => (C p).chart) hC (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  let Q : ChartPartition 1 n M univ := ⟨m,fun i => (C (p i)).chart,
    w,hw.1,hw.2.1,fun i => ⟨(hw.2.2.1 i).1,fun x hx => (hs i hx).2⟩,hw.2.2.2⟩
  exact ⟨Q,fun i => C (p i),fun _ => rfl⟩

/-- The positive ambient orientation removes the chart determinant sign.
This extends the regular-domain bridge to every compact manifold piece. -/
theorem compact_manifold_riemann : compact_manifold_riemannType := by
  intro n hn M o ho hK f hf
  classical
  have hM := o.manifold
  have hJ := compact_piece_jordan hM hK
  have hin (g : M → ℝ) (hg : Continuous g) : RegionIntegrable g := by
    have hc := D04.JordanRegions.integrable_continuous_on_closure hn hJ
      (fun x : closure M => g ⟨x,hK.isClosed.closure_subset x.property⟩)
      (hg.comp (continuous_subtype_val.subtype_mk _))
    exact hc
  have hfi := hin f hf
  refine ⟨hJ,hfi,?_⟩
  intro P
  obtain ⟨Q,C,hC⟩ := compact_piece_partition hM hK
  have hη := D04.RegularDomainBridge.volume_field_continuous f hf
  have hc : ∀ i, Continuous (fun x : M => Q.weight i x * f x) :=
    fun i => ((Q.partition.1 i).continuous.comp continuous_subtype_val).mul hf
  have hi : ∀ i, RegionIntegrable (fun x : M => Q.weight i x * f x) :=
    fun i => hin _ (hc i)
  have hv i : coefficientIntegral
      (D04.ManifoldIntegralIndependence.weightedCoefficient
        (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
        (Q.chart i) (Q.weight i)) =
      regionIntegral (fun x : M => Q.weight i x * f x) := by
    have hs : tsupport (fun x : M => Q.weight i x * f x) ⊆
        Subtype.val ⁻¹' (C i).chart.ambient := by
      rw [hC i]
      exact tsupport_mul_subset_left.trans (Q.partition.2.2.1 i).2
    have hk : HasCompactSupport (fun x : M => Q.weight i x * f x) :=
      (Q.partition.2.2.1 i).1.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left
    rw [← hC i]
    have heq : D04.ManifoldIntegralIndependence.weightedCoefficient
        (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
        (C i).chart (Q.weight i) =
        fun u : (C i).chart.source =>
          (Q.weight i (chartPoint (C i).chart u) * f (chartPoint (C i).chart u)) *
            |(chartDifferential (C i).chart u).det| := by
      funext u
      change Q.weight i ((C i).chart.toFun u) *
        D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f) (C i).chart u = _
      rw [D04.RegularDomainBridge.signedCoefficient_volume o ho]
      exact (mul_assoc _ _ _).symm
    rw [heq]
    exact D04.RegularDomainBridge.chart_absolute_substitution (C i).chart (C i).extension (C i).regular
      (C i).inverse_regular (C i).source_subset (C i).ambient_eq (C i).agrees
      (C i).differential (fun x : M => Q.weight i x * f x) (hi i) hk hs
  change (∑ i, (P.sign i).val * coefficientIntegral
    (localizedTopCoefficient (volumeField f) (P.chart i) (P.weight i))) = _
  rw [D04.ManifoldIntegralIndependence.signed_expression o (volumeField f) hη P]
  have hcmp := D04.ManifoldIntegralIndependence.partition_independence
    (D04.ManifoldIntegralIndependence.signedCoefficient o (volumeField f))
    (D04.ManifoldIntegralIndependence.signedCoefficient_continuous o (volumeField f) hη)
    (D04.ManifoldIntegralIndependence.signedCoefficient_transition o (volumeField f))
    hM.1 hM.2.1 P.toChartPartition Q
    (fun c u hu => D04.ManifoldIntegralIndependence.signedCoefficient_support o (volumeField f) c u hu)
    (fun _ _ _ => mem_univ _)
  apply hcmp.trans
  rw [Finset.sum_congr rfl (fun i _ => hv i)]
  apply (D04.RegularDomainBridge.region_integral_sum hK.isBounded _ hi f hfi ?_).symm
  intro x
  obtain ⟨V,hV,hKV,hsum⟩ := Q.partition.2.2.2.1
  have hx := hsum x (hKV (mem_univ x))
  rw [← Finset.sum_mul,hx,one_mul]


/-- Both scalar densities use the same standard ambient orientation and the
same prescribed outer boundary, with all internal pairs cancelled. -/
theorem riemann_manifold_green : riemann_manifold_greenType := by
  intro q O M hamb bO hbO m P s hreg Z hdim hself hover hcover Zbulk hbulk
    l p e Q tSign b deltaOut hdelta hOut hout deltaPair hdeltaPair hPair hpair
    f g hO hf hg
  have hpc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative f x i) O :=
    D04.crOn_scalarPartialDerivative 0 O f hO hf i
  have hqc (i : Fin 2) : ContinuousOn (fun x => scalarPartialDerivative g x i) O :=
    D04.crOn_scalarPartialDerivative 0 O g hO hg i
  have hK : IsCompact (⋃ j, (M j).carrier) := isCompact_iUnion (fun j => (M j).compact)
  have hKO : (⋃ j, (M j).carrier) ⊆ O := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    exact (M j).subset_domain hj
  have hdata (ρ : E 2 → ℝ) (hρ : ContinuousOn ρ O) (j : Fin q) :=
    compact_manifold_riemann 2 (by norm_num) (M j).orientation (hamb j) (M j).compact
      (fun x => ρ x) ((hρ.mono (M j).subset_domain).domRestrict)
  have hcoord (ρ : E 2 → ℝ) (hρ : ContinuousOn ρ O) :=
    D04.GeometricUnion.coordinate_union_integral (fun j => (M j).carrier)
      (fun j => (hdata ρ hρ j).1) Zbulk.carrier (planar_seams_contentZero Zbulk)
      hbulk ρ (hρ.mono (by rwa [hK.isClosed.closure_eq]))
  have hcρ : ContinuousOn (circulationDensity f g) O := (hqc 0).sub (hpc 1)
  have hfρ : ContinuousOn (divergenceDensity f g) O := (hpc 0).add (hqc 1)
  have hcir := hcoord (circulationDensity f g) hcρ
  have hflux := hcoord (divergenceDensity f g) hfρ
  have h (η : FormField 2 1) (hη : IsCrForm (some 1) O η)
      (ρ : E 2 → ℝ) (hρ : ContinuousOn ρ O)
      (hd : exteriorDerivative η = fun x => ρ x • omega 2) :
      regionIntegral (fun x : (⋃ j, (M j).carrier) => ρ x) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) η) := by
    obtain ⟨I,hI,hB,hst⟩ := D04.FinitePiecewiseStokes.manifold_piecewise_stokes
      M bO hbO m P s hreg Z hdim hself hover hcover (fun _ => 1)
      e Q tSign b deltaOut hdelta hOut hout deltaPair hdeltaPair hPair
      (fun i => ⟨(hpair i).1,(hpair i).2,rfl⟩) η hη
    change ∀ j, HasPositiveIntegral (M j).orientation
      (tangentRestriction 1 2 (M j).carrier (exteriorDerivative η)) (I j) at hI
    rw [hd] at hI
    have hvalues j : regionIntegral (fun x : (M j).carrier => ρ x) = I j := by
      have hi : HasPositiveIntegral (M j).orientation
          (volumeField (fun x : (M j).carrier => ρ x)) (I j) := hI j
      obtain ⟨A⟩ := hi.2.2.1
      exact ((hdata ρ hρ j).2.2 A).symm.trans ((hi.2.2.2 A).2)
    calc
      _ = ∑ j, regionIntegral (fun x : (M j).carrier => ρ x) := (hcoord ρ hρ).2.2
      _ = ∑ j, I j := Finset.sum_congr rfl (fun j _ => hvalues j)
      _ = _ := by simpa only [one_zsmul] using hst
  exact ⟨hcir.1,hcir.2.1,hflux.2.1,
    h (circulationForm f g) (circulation_regular O f g hO hf hg)
      (circulationDensity f g) hcρ (exterior_circulation_all f g),
    h (planarFluxForm f g) (flux_regular O f g hO hf hg)
      (divergenceDensity f g) hfρ (exterior_flux_all f g)⟩

end D04.Green
