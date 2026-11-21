import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.RadialFluxObstruction
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.D04.C15.ExactFormsIntegrateToZeroOnCycles
import MathGenome.Internal.MultivariableAnalysis.D04.C10.SphereAreaFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C02.CrCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Set
open scoped RealInnerProductSpace ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.RadialFluxObstruction
open D04
open Specs.D04.C15.RadialFluxObstruction
open Specs.D04.C15.RadialFluxObstruction.Model
open Specs.D04.C10.SphereAreaFlux.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C15.GeneralizedStokes.Model

abbrev puncturedSpace := Specs.D04.C15.RadialFluxObstruction.Model.puncturedSpace
abbrev radialField := Specs.D04.C15.RadialFluxObstruction.Model.radialField
abbrev radialForm := Specs.D04.C15.RadialFluxObstruction.Model.radialForm

lemma puncturedSpace_open : IsOpen puncturedSpace := isClosed_singleton.isOpen_compl
lemma mem_puncturedSpace {x : E 3} : x ∈ puncturedSpace ↔ x ≠ 0 := Iff.rfl

lemma radialField_contDiff : ContDiffOn ℝ ∞ radialField puncturedSpace := by
  have hn : ContDiffOn ℝ ∞ (fun x : E 3 => ‖x‖) puncturedSpace :=
    contDiffOn_id.norm ℝ (fun _ hx => hx)
  exact ((hn.pow 3).inv (fun x hx => pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).smul
    contDiffOn_id

theorem radialField_smooth : radialField_smoothType :=
  (smoothOn_iff_contDiffOn _ _ puncturedSpace_open).mpr radialField_contDiff

theorem radialForm_smooth : radialForm_smoothType := by
  refine ⟨puncturedSpace_open, ?_⟩
  intro I r
  exact (Dictionary.beta_isCr r puncturedSpace radialField puncturedSpace_open
    (radialField_smooth r)).2 I

lemma radialField_fderiv_apply (x : E 3) (hx : x ≠ 0) (v : E 3) :
    fderiv ℝ radialField x v = (‖x‖ ^ 3)⁻¹ • v -
      (3 * (‖x‖ ^ 5)⁻¹ * ⟪x, v⟫) • x := by
  have hn0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : HasFDerivAt (fun y : E 3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn0) using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg y)).symm
    · ext w
      simp only [Real.sqrt_sq (norm_nonneg x), smul_apply, smul_eq_mul,
        innerSL_apply_apply, nsmul_eq_mul]
      field_simp
      <;> ring
  have hi : HasFDerivAt (fun y : E 3 => (‖y‖ ^ 3)⁻¹)
      ((-3 * (‖x‖ ^ 5)⁻¹) • innerSL ℝ x) x := by
    convert (hasDerivAt_inv (pow_ne_zero 3 hn0)).comp_hasFDerivAt x (hn.pow 3) using 1
    · rfl
    · ext w
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, nsmul_eq_mul]
      norm_num only [show (3 : ℕ) - 1 = 2 from rfl]
      field_simp
      <;> ring
  have hs := hi.smul (hasFDerivAt_id x)
  change HasFDerivAt radialField _ x at hs
  rw [hs.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply]
  simp [sub_eq_add_neg, mul_assoc, neg_smul]

lemma sum_coordinate_sq (x : E 3) : ∑ i : Fin 3, (x i)^2 = ‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coordinates]
  simp only [pow_two]

theorem divergence_formula : divergence_formulaType := by
  intro x hx
  change divergence radialField x = _
  rw [divergence_eq_jacobian_trace]
  change (∑ i : Fin 3, matrixOfLinearMap (fderiv ℝ radialField x).toLinearMap i i) = _
  simp_rw [matrixOfLinearMap_apply]
  have hb (i : Fin 3) : ⟪x, standardBasis 3 i⟫ = x i :=
    EuclideanSpace.inner_basisFun_real _ _ i
  change (∑ i : Fin 3, (fderiv ℝ radialField x (standardBasis 3 i)) i) = _
  simp_rw [radialField_fderiv_apply x hx]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, standardBasis_apply,
    if_true, mul_one, hb]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem divergence_zero : divergence_zeroType := by
  intro x hx
  rw [divergence_formula x hx, sum_coordinate_sq]
  have hn0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  <;> ring

theorem radialForm_closed : radialForm_closedType := by
  intro x hx
  have hd := Dictionary.exterior_beta_divergence puncturedSpace radialField
    puncturedSpace_open (radialField_smooth 1) x hx
  have hz : divergence radialField x = 0 := divergence_zero x hx
  rw [hz, zero_smul] at hd
  exact hd

lemma sphere_subset_punctured : sphere 1 ⊆ puncturedSpace := by
  intro x hx
  change x ≠ 0
  intro hzero
  change ‖x‖ = 1 at hx
  simp [hzero] at hx

theorem sphere_normal_pairing : sphere_normal_pairingType := by
  intro x hx
  have hf : radialField x = x := by
    change (‖x‖ ^ 3)⁻¹ • x = x
    change ‖x‖ = 1 at hx
    simp [hx]
  refine ⟨hf, ?_⟩
  exact (congrArg (fun y : E 3 => ⟪y, radialNormal 1 x⟫) hf).trans
    (SphereAreaFlux.radialNormal_inner 1 (by norm_num) x hx)

theorem sphere_flux : sphere_fluxType := by
  change surfaceIntegral (sphere 1) (fun x => ⟪radialField x, radialNormal 1 x⟫) = _
  have he : (fun x : sphere 1 => ⟪radialField x, radialNormal 1 x⟫) =
      (fun _ => (1 : ℝ)) := funext fun x => (sphere_normal_pairing x x.property).2
  rw [he, SphereAreaFlux.sphere_area 1 (by norm_num)]
  ring

/-- The flux/oriented-form bridge supplies the actual outward orientation. -/
theorem sphere_form_integral : sphere_form_integralType := by
  have hM := SphereAreaFlux.sphere_embedded 1 (by norm_num)
  have hc := SphereAreaFlux.sphere_compact 1
  let N : UnitNormalField (sphere 1) :=
    ⟨fun x => radialNormal 1 x, (SphereAreaFlux.outward_normal 1 (by norm_num)).1,
      fun x => ((SphereAreaFlux.outward_normal 1 (by norm_num)).2 x).1⟩
  obtain ⟨o, ho, hflux⟩ := D04SurfaceAssembly.flux_beta_identification hM hc N
  have hF : Continuous (fun x : sphere 1 => radialField x) := by
    have he : (fun x : sphere 1 => radialField x) = (fun x : sphere 1 => (x : E 3)) :=
      funext fun x => (sphere_normal_pairing x x.property).1
    rw [he]
    exact continuous_subtype_val
  have hh := hflux (fun x : sphere 1 => radialField x) hF
  have he : surfaceFluxForm (fun x : sphere 1 => radialField x) =
      tangentRestriction 1 2 (sphere 1) radialForm := rfl
  rw [he] at hh
  have hk : IsCompact (topSupport (tangentRestriction 1 2 (sphere 1) radialForm)) := by
    letI : CompactSpace (sphere 1) := isCompact_iff_compactSpace.mp hc
    exact isClosed_closure.isCompact
  refine ⟨o, ho, hh.1, hk, D04.ManifoldIntegral.signed_partition_exists o _ hk, ?_⟩
  intro P
  refine ⟨fun i => (D04.ManifoldIntegral.top_coefficients_integrable _ hh.1
    P.toChartPartition i).2.2, ?_⟩
  exact (hh.2 P).symm.trans sphere_flux

/-- A C¹ ambient primitive is already ruled out by boundaryless Stokes. -/
theorem no_C1_primitive : no_C1_primitiveType := by
  rintro ⟨eta, heta, heq⟩
  obtain ⟨o, _, hi⟩ := sphere_form_integral
  have hc := SphereAreaFlux.sphere_compact 1
  have hb := (D04.boundaryless_iff.mp (SphereAreaFlux.sphere_manifold 1 (by norm_num)).2).2
  have hz := ExactCycles.exact_ambient_integral_zero o hc hb puncturedSpace eta
    sphere_subset_punctured heta
  have hr : tangentRestriction 1 2 (sphere 1) (exteriorDerivative eta) =
      tangentRestriction 1 2 (sphere 1) radialForm := by
    funext x
    exact congrArg (fun a : Covector (E 3) 2 => a.compLinearMap
      (Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace 1 2 (sphere 1) x).subtype)
      (heq x (sphere_subset_punctured x.property))
  rw [hr] at hz
  have h := D04Stokes.positive_integral_unique o _ hi hz
  exact (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)) h

theorem no_C2_primitive : no_C2_primitiveType := by
  rintro ⟨eta, heta, heq⟩
  apply no_C1_primitive
  refine ⟨eta, ⟨heta.1, ?_⟩, heq⟩
  intro I
  apply (crOn_iff_contDiffOn 1 _ _ puncturedSpace_open).mpr
  exact ((crOn_iff_contDiffOn 2 _ _ puncturedSpace_open).mp (heta.2 I)).of_le (by norm_num)

theorem no_vector_potential : no_vector_potentialType := by
  rintro ⟨A, hA, hcurl⟩
  apply no_C1_primitive
  refine ⟨Dictionary.alpha A, Dictionary.alpha_isCr 1 puncturedSpace A puncturedSpace_open hA, ?_⟩
  intro x hx
  have hd := Dictionary.exterior_alpha_curl puncturedSpace A puncturedSpace_open hA x hx
  have hp : curl A x = radialField x := hcurl x hx
  apply hd.trans
  change Dictionary.beta (curl A) x = Dictionary.beta radialField x
  simp only [Dictionary.beta, Specs.D04.C13.OrientedEuclideanDictionary.Model.beta, hp]

end D04.RadialFluxObstruction
