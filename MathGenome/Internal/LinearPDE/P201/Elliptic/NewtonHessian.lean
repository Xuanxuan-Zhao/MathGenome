import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201.Potential.NewtonPotential
import MathGenome.Internal.LinearPDE.P201.Elliptic.HolderCancellation
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff ENNReal

namespace P201.Elliptic.NewtonHessian
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

abbrev hessianKernel : hessianKernelType := @P201Specs.Elliptic.NewtonHessian.hessianKernel
abbrev holderPotential : holderPotentialType := @P201Specs.Elliptic.NewtonHessian.holderPotential

/-- In dimension one the Laplacian has just one entry. The sign follows
from the accepted fundamental-solution theorem on the original distribution space. -/
theorem dimensionOneIdentity : dimensionOneIdentityStatement := by
  have h := P201.fundamentalSolution 1 (by omega)
  simp only [P201Specs.distributionLaplacian, Fin.sum_univ_one] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Agreement with the earlier Newton integral on smooth compact data. -/
theorem holderPotential_eq_newtonPotential {n : ℕ} (f : Test ℝ (⊤ : Domain n)) :
    holderPotential f = P201.newtonPotential f := rfl

open private P201.profile_derivative P201.omega_pos from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental

lemma hessianKernel_symmetric {n : ℕ} (i j : Fin n) :
    hessianKernel i j = hessianKernel j i := by
  funext x
  simp only [hessianKernel, P201Specs.Elliptic.NewtonHessian.hessianKernel,
    kronecker, eq_comm (a := i)]
  ring

lemma hessianKernel_smooth {n : ℕ} (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (hessianKernel i j) ({0}ᶜ : Set (Space n)) := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => ‖y‖) x := contDiffAt_norm ℝ hx0
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => y i) x :=
    (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.contDiffAt
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => y j) x :=
    (EuclideanSpace.proj j : Space n →L[ℝ] ℝ).contDiff.contDiffAt
  have ha : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => (n : ℝ) * y i * y j / ‖y‖ ^ (n + 2)) x :=
    ((contDiffAt_const.mul hi).mul hj).div (hnorm.pow (n + 2))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx0))
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => kronecker i j / ‖y‖ ^ n) x :=
    contDiffAt_const.div (hnorm.pow n) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx0))
  exact ((ha.sub hb).div_const (omega n)).contDiffWithinAt

lemma hessianKernel_homogeneous {n : ℕ} (i j : Fin n) {r : ℝ} (hr : 0 < r)
    (x : Space n) :
    hessianKernel i j (r • x) = ((r ^ n)⁻¹ : ℝ) • hessianKernel i j x := by
  simp only [hessianKernel, P201Specs.Elliptic.NewtonHessian.hessianKernel,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, PiLp.smul_apply, smul_eq_mul,
    mul_pow, pow_add, pow_two]
  field_simp

lemma hessianKernel_trace {n : ℕ} (_hn : 1 ≤ n) {x : Space n} (hx : x ≠ 0) :
    (∑ i : Fin n, hessianKernel i i x) = 0 := by
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [hessianKernel, P201Specs.Elliptic.NewtonHessian.hessianKernel,
    kronecker, ite_true, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (∑ i : Fin n, (n : ℝ) * x i * x i) = (n : ℝ) * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, pow_add]
  field_simp
  ring

lemma norm_fderiv_coordinate {n : ℕ} {x : Space n} (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : Space n => ‖y‖) x (coordinate n i) = x i / ‖x‖ := by
  have hd : DifferentiableAt ℝ (fun y : Space n => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hs := congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinate n i))
    (hd.hasFDerivAt.pow 2).fderiv
  rw [fderiv_norm_sq_apply] at hs
  have hinner : inner ℝ x (coordinate n i) = x i := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
    hinner, nsmul_eq_mul, Nat.add_one_sub_one, pow_one] at hs
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  norm_num at hs
  nlinarith [hs]

lemma fundamental_coordinate_derivative {n : ℕ} (hn : 1 ≤ n) {x : Space n}
    (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fundamentalKernel n) x (coordinate n i) = gradientKernel i x := by
  have hnorm : DifferentiableAt ℝ (fun y : Space n => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hd := (P201.profile_derivative hn (norm_pos_iff.mpr hx)).comp_hasFDerivAt x
    hnorm.hasFDerivAt
  change fderiv ℝ (fundamentalProfile n ∘ (fun y : Space n => ‖y‖)) x (coordinate n i) = _
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, norm_fderiv_coordinate hx]
  unfold gradientKernel
  have hp : ‖x‖ ^ n = ‖x‖ ^ (n - 1) * ‖x‖ := by
    calc
      _ = ‖x‖ ^ ((n - 1) + 1) := congrArg (fun k : ℕ => ‖x‖ ^ k) (Nat.sub_add_cancel hn).symm
      _ = _ := pow_succ _ _
  rw [hp]
  field_simp

lemma holderPotential_integrable {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ}
    (hF : Continuous F) (hc : HasCompactSupport F) (x : Space n) :
    Integrable (fun y => fundamentalKernel n y * F (x - y)) volume := by
  exact (P201.fundamentalLocalIntegrability n hn).integrable_smul_right_of_hasCompactSupport
    (hF.comp (continuous_const.sub continuous_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x))

open scoped Convolution in
lemma holderPotential_continuous {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ}
    (hF : Continuous F) (hc : HasCompactSupport F) : Continuous (holderPotential F) := by
  exact hc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (P201.fundamentalLocalIntegrability n hn) hF

open scoped Pointwise in
lemma unitSurface_apply_cone {n : ℕ} (s : Set (Space n)) (hs : MeasurableSet s) :
    unitSurface n s = (n : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • (s ∩ sphere 0 1)) := by
  rw [P201.Elliptic.HolderCancellation.unitSurface_eq_polar,
    Measure.map_apply (by fun_prop) hs,
    Measure.toSphere_apply' _ (hs.preimage (by fun_prop))]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    image_preimage_eq_inter_range, Subtype.range_coe]

open scoped Pointwise in
lemma unitSurface_isometry_invariant {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving e (unitSurface n) (unitSurface n) := by
  refine ⟨by fun_prop, ?_⟩
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    unitSurface_apply_cone _ (hs.preimage (by fun_prop)), unitSurface_apply_cone _ hs]
  congr 1
  have heq : Ioo (0 : ℝ) 1 • (e ⁻¹' s ∩ sphere 0 1) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (s ∩ sphere 0 1)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, hy, rfl⟩
      exact ⟨r, hr, e y, ⟨hy.1, by simpa using hy.2⟩, by simp⟩
    · rintro ⟨r, hr, y, hy, he⟩
      refine ⟨r, hr, e.symm y, ⟨by simpa using hy.1, by simpa using hy.2⟩, ?_⟩
      apply e.injective
      simpa using he
  rw [heq]
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

lemma continuous_integrable_unitSurface {n : ℕ} {f : Space n → ℝ} (hf : Continuous f) :
    Integrable f (unitSurface n) := by
  rw [P201.Elliptic.HolderCancellation.unitSurface_eq_polar]
  apply (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr
  exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma sphere_diagonal_moments_equal {n : ℕ} (i j : Fin n) :
    (∫ θ, (θ i) ^ 2 ∂unitSurface n) = ∫ θ, (θ j) ^ 2 ∂unitSurface n := by
  let e : Space n ≃ₗᵢ[ℝ] Space n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := (unitSurface_isometry_invariant e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun θ => (θ i) ^ 2)
  simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using h.symm

lemma sphere_mixed_moment_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∫ θ, θ i * θ j ∂unitSurface n) = 0 := by
  classical
  let e : Space n ≃ₗᵢ[ℝ] Space n := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin n => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have h := (unitSurface_isometry_invariant e).integral_comp
    e.toHomeomorph.measurableEmbedding (fun θ => θ i * θ j)
  have he (θ : Space n) : e θ i * e θ j = -(θ i * θ j) := by
    simp [e, LinearIsometryEquiv.piLpCongrRight_apply, hij.symm]
  simp_rw [he, integral_neg] at h
  linarith

open private P201.unitSurface_norm_ae from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental

/-- The actual geometric sphere moment, including the endpoint measure in n=1. -/
theorem sphereMoment : sphereMomentStatement := by
  intro n hn i j
  by_cases hij : i = j
  · subst j
    have hi : Integrable (fun θ : Space n => (θ i) ^ 2) (unitSurface n) :=
      continuous_integrable_unitSurface ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).continuous.pow 2)
    have hsum : (∑ j : Fin n, ∫ θ, (θ j) ^ 2 ∂unitSurface n) = omega n := by
      rw [← integral_finsetSum Finset.univ (f := fun (j : Fin n) (θ : Space n) => (θ j) ^ 2) (fun j _ =>
        continuous_integrable_unitSurface ((EuclideanSpace.proj j : Space n →L[ℝ] ℝ).continuous.pow 2))]
      have he : (fun θ : Space n => ∑ j : Fin n, (θ j) ^ 2) =ᵐ[unitSurface n]
          (fun _ => (1 : ℝ)) := by
        filter_upwards [P201.unitSurface_norm_ae n] with θ hθ
        rw [← EuclideanSpace.real_norm_sq_eq, hθ, one_pow]
      rw [integral_congr_ae he, integral_const]
      simp [smul_eq_mul, omega, P201Specs.omega]
    have he : (∑ j : Fin n, ∫ θ, (θ j) ^ 2 ∂unitSurface n) =
        (n : ℝ) * ∫ θ, (θ i) ^ 2 ∂unitSurface n := by
      simp_rw [sphere_diagonal_moments_equal (j := i)]
      simp
    rw [he] at hsum
    simp only [kronecker, ite_true, mul_one]
    rw [show (fun θ : Space n => θ i * θ i) = (fun θ => (θ i) ^ 2) by funext θ; ring]
    exact (eq_div_iff (by exact_mod_cast (show n ≠ 0 by omega))).mpr (by linarith)
  · rw [sphere_mixed_moment_zero i j hij]
    simp [kronecker, hij]

lemma gradientKernel_coordinate_derivative {n : ℕ} (hn : 1 ≤ n)
    {x : Space n} (hx : x ≠ 0) (i j : Fin n) :
    fderiv ℝ (gradientKernel i) x (coordinate n j) = hessianKernel i j x := by
  have hnorm : DifferentiableAt ℝ (fun y : Space n => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hnz : omega n * ‖x‖ ^ n ≠ 0 :=
    mul_ne_zero (P201.omega_pos hn).ne' (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  have hden := (hnorm.hasFDerivAt.pow n).const_mul (omega n)
  have hd := ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.neg).fun_mul
    ((hasDerivAt_inv hnz).comp_hasFDerivAt x hden)
  simp only [Pi.neg_apply, Function.comp_apply, EuclideanSpace.proj, PiLp.proj_apply] at hd
  change fderiv ℝ (fun y : Space n => -y i * (omega n * ‖y‖ ^ n)⁻¹) x (coordinate n j) = _
  rw [hd.fderiv]
  have hc : (coordinate n j) i = kronecker i j := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, kronecker]
  simp only [add_apply, smul_apply, neg_apply,
    PiLp.proj_apply, norm_fderiv_coordinate hx,
    smul_eq_mul, nsmul_eq_mul, hc]
  have hp : ‖x‖ ^ n = ‖x‖ ^ (n - 1) * ‖x‖ := by
    calc
      _ = ‖x‖ ^ ((n - 1) + 1) := congrArg (fun k : ℕ => ‖x‖ ^ k) (Nat.sub_add_cancel hn).symm
      _ = _ := pow_succ _ _
  unfold hessianKernel P201Specs.Elliptic.NewtonHessian.hessianKernel
  rw [pow_add]
  field_simp [norm_ne_zero_iff.mpr hx, (P201.omega_pos hn).ne']
  rw [hp]
  ring

lemma unitSurface_finite (n : ℕ) : IsFiniteMeasure (unitSurface n) := by
  rw [P201.Elliptic.HolderCancellation.unitSurface_eq_polar]
  infer_instance

lemma hessianKernel_mean_zero {n : ℕ} (hn : 1 ≤ n) (i j : Fin n) :
    (∫ θ, hessianKernel i j θ ∂unitSurface n) = 0 := by
  haveI : IsFiniteMeasure (unitSurface n) := unitSurface_finite n
  have hi : Integrable (fun θ : Space n => (n : ℝ) * θ i * θ j) (unitSurface n) :=
    continuous_integrable_unitSurface (by fun_prop)
  have he : (fun θ => hessianKernel i j θ) =ᵐ[unitSurface n]
      (fun θ : Space n => ((n : ℝ) * θ i * θ j - kronecker i j) / omega n) := by
    filter_upwards [P201.unitSurface_norm_ae n] with θ hθ
    simp [hessianKernel, P201Specs.Elliptic.NewtonHessian.hessianKernel, hθ]
  rw [integral_congr_ae he, integral_div,
    integral_sub hi (integrable_const _)]
  have he' : (fun θ : Space n => (n : ℝ) * θ i * θ j) =
      (fun θ : Space n => (n : ℝ) * (θ i * θ j)) := by funext θ; ring
  rw [he', integral_const_mul, sphereMoment hn i j, integral_const]
  change ((n : ℝ) * (omega n * kronecker i j / (n : ℝ)) - omega n * kronecker i j) / omega n = 0
  rw [mul_div_cancel₀ _ (by exact_mod_cast (show n ≠ 0 by omega))]
  simp

/-- The explicit Newtonian Hessian qualifies for the upstream cancellation theorem. -/
theorem kernelHypotheses : kernelHypothesesStatement := by
  intro n hn i j
  exact ⟨hessianKernel_smooth i j,
    fun r hr z _ => hessianKernel_homogeneous i j hr z,
    hessianKernel_mean_zero (by omega) i j⟩

/-- Actual ordinary Hessian off the singularity, with the original fundamental kernel. -/
lemma fundamental_hessian_off_origin {n : ℕ} (hn : 1 ≤ n) {x : Space n}
    (hx : x ≠ 0) (i j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (fundamentalKernel n) y (coordinate n i)) x
      (coordinate n j) = hessianKernel i j x := by
  have he : (fun y => fderiv ℝ (fundamentalKernel n) y (coordinate n i)) =ᶠ[𝓝 x]
      gradientKernel i := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact fundamental_coordinate_derivative hn hy i
  rw [he.fderiv_eq]
  exact gradientKernel_coordinate_derivative hn hx i j

theorem potentialBasic : potentialBasicStatement := by
  intro n hn α hα F hc hF
  have hcont := P201.Elliptic.HolderCancellation.holder_continuous hα hF
  exact ⟨holderPotential_integrable hn hcont hc, holderPotential_continuous hn hcont hc⟩

theorem hessianOperatorHolder : hessianOperatorStatement := by
  intro n hn α hα hα1 F hc hF i j
  have hK := kernelHypotheses hn i j
  exact ⟨P201.Elliptic.HolderCancellation.globalHolder (by omega) α hα hα1 _ F hK hc hF,
    P201.Elliptic.HolderCancellation.principalValueExists (by omega) α hα hα1 _ F hK hc hF⟩

theorem hessianOperatorEstimate : hessianOperatorEstimateStatement := by
  intro n hn α hα hα1 i j a R hR
  have hK := kernelHypotheses hn i j
  obtain ⟨A, B, hKB⟩ := P201.Elliptic.HolderCancellation.sphere_bounds_exist hK
  obtain ⟨C, hC, he⟩ := P201.Elliptic.HolderCancellation.quantitativeHolder
    (𝕜 := ℝ) (by omega : 1 ≤ n) α hα hα1 a R A B hR hKB.1 hKB.2.1
  exact ⟨C, hC, fun F hc hs hF => he _ F hK hKB hc hs hF⟩

open private P201.coordEquiv P201.omega_eq_sphereArea P201.kernel_bridge
  P201.coordinateTest P201.partial_bridge from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental

private lemma gradient_coordinate_bridge {n : ℕ} (hn : n ≠ 1) (i : Fin n)
    (x : Fin n → ℝ) :
    gradientKernel i (P201.coordEquiv n x) =
      -ExpandedFA.PartIV.LaplaceFundamental.kernelGradient n i x := by
  unfold gradientKernel ExpandedFA.PartIV.LaplaceFundamental.kernelGradient
  rw [show P201Specs.omega n = _ from P201.omega_eq_sphereArea hn]
  simp only [ExpandedFA.PartIV.LaplaceFundamental.euclideanRadius,
    Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  change -x i / (_ * ‖WithLp.toLp 2 x‖ ^ n) =
    -(x i * (‖WithLp.toLp 2 x‖ ^ n)⁻¹ / _)
  ring

/-- Local integrability of the actual gradient, including its endpoint case. -/
lemma gradientKernel_locallyIntegrable {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    LocallyIntegrable (gradientKernel i) volume := by
  by_cases h1 : n = 1
  · subst n
    apply (locallyIntegrable_const (1 / omega 1 : ℝ)).mono
    · exact (((EuclideanSpace.proj i : Space 1 →L[ℝ] ℝ).continuous.measurable.neg).div
        (measurable_const.mul (continuous_norm.measurable.pow_const 1))).aestronglyMeasurable
    · filter_upwards [] with x
      rw [gradientKernel, norm_div, norm_neg]
      have hw : 0 < omega 1 := P201.omega_pos (by omega)
      simp only [pow_one, norm_mul, Real.norm_eq_abs,
        abs_of_pos hw, abs_of_nonneg (norm_nonneg x)]
      calc
        |x i| / (omega 1 * ‖x‖) ≤ ‖x‖ / (omega 1 * ‖x‖) :=
          div_le_div_of_nonneg_right (PiLp.norm_apply_le x i) (by positivity)
        _ ≤ |1 / omega 1| := by
          by_cases hx : x = 0
          · simp [hx]
          · rw [mul_comm (omega 1), div_mul_eq_div_div, div_self (norm_ne_zero_iff.mpr hx),
              abs_of_pos (by positivity : 0 < 1 / omega 1)]
  · have hm : Measure.map (P201.coordEquiv n).toHomeomorph volume = volume :=
      (PiLp.volume_preserving_toLp (ι := Fin n)).map_eq
    rw [← hm]
    apply (locallyIntegrable_map_homeomorph (P201.coordEquiv n).toHomeomorph).2
    change LocallyIntegrable (fun x => gradientKernel i (P201.coordEquiv n x)) volume
    simp_rw [gradient_coordinate_bridge h1]
    exact (ExpandedFA.PartIV.LaplaceFundamental.locallyIntegrable_kernelGradient hn i).neg

/-- Integration by parts with an arbitrary compact smooth test; the singularity
is crossed, rather than excluded from the conclusion. -/
lemma fundamental_gradient_pairing {n : ℕ} (hn : 2 ≤ n)
    (φ : Test ℝ (⊤ : Domain n)) (i : Fin n) :
    (∫ x, fundamentalKernel n x * P102.U4.testPartialWord ⊤ [i] φ x) =
      -(∫ x, gradientKernel i x * φ x) := by
  let ψ := P201.coordinateTest φ
  let ψ' := ExpandedFA.Distributions.testPartialCLM [i] ψ
  have hg : ∀ x, HasLineDerivAt ℝ ψ (ψ' x) x
      (ExpandedFA.Distributions.coordinateVector i) := by
    intro x
    have h := (ψ.contDiff.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt
      (ExpandedFA.Distributions.coordinateVector i)
    convert h using 1
    rw [ExpandedFA.Distributions.testPartial_formula ℝ n ⊤ [i] ψ]
    rfl
  have h := ExpandedFA.PartIV.LaplaceFundamental.integral_smul_lineDeriv_off_origin
    hn i _ _ ψ ψ'
    ((ExpandedFA.PartIV.LaplaceFundamental.locallyIntegrable_kernel (by omega)).integrable_smul_right_of_hasCompactSupport
      ψ.continuous ψ.hasCompactSupport)
    ((ExpandedFA.PartIV.LaplaceFundamental.locallyIntegrable_kernelGradient (by omega) i).integrable_smul_right_of_hasCompactSupport
      ψ.continuous ψ.hasCompactSupport)
    ((ExpandedFA.PartIV.LaplaceFundamental.locallyIntegrable_kernel (by omega)).integrable_smul_right_of_hasCompactSupport
      ψ'.continuous ψ'.hasCompactSupport)
    (fun x hx => ExpandedFA.PartIV.LaplaceFundamental.kernel_hasLineDerivAt hn x hx i) hg
  have hchange (g : Space n → ℝ) := (PiLp.volume_preserving_toLp (ι := Fin n)).integral_comp
    (P201.coordEquiv n).toHomeomorph.measurableEmbedding g
  rw [← hchange (fun x => fundamentalKernel n x * P102.U4.testPartialWord ⊤ [i] φ x),
    ← hchange (fun x => gradientKernel i x * φ x)]
  have he (x : Fin n → ℝ) : P102.U4.testPartialWord ⊤ [i] φ (P201.coordEquiv n x) = ψ' x := by
    rw [P102.U4.testPartialWord_coe]
    calc
      _ = ExpandedFA.Distributions.partialFunction [i] ψ x :=
        (congrFun (P201.partial_bridge φ [i]) x).symm
      _ = ψ' x := (congrFun (ExpandedFA.Distributions.testPartial_formula ℝ n ⊤ [i] ψ) x).symm
  have hk : (fun x : Fin n → ℝ => fundamentalKernel n (P201.coordEquiv n x) *
      P102.U4.testPartialWord ⊤ [i] φ (P201.coordEquiv n x)) =
      (fun x => -(ExpandedFA.PartIV.LaplaceFundamental.kernel n x * ψ' x)) := by
    funext x
    rw [P201.kernel_bridge, he, neg_mul]
  have hgk : (fun x : Fin n → ℝ => gradientKernel i (P201.coordEquiv n x) *
      φ (P201.coordEquiv n x)) =
      (fun x => -(ExpandedFA.PartIV.LaplaceFundamental.kernelGradient n i x * ψ x)) := by
    funext x
    rw [gradient_coordinate_bridge (by omega : n ≠ 1)]
    change -_ * ψ x = -(_ * ψ x)
    ring
  erw [hk, hgk]
  rw [integral_neg, integral_neg, neg_neg]
  simpa only [smul_eq_mul, neg_neg] using congrArg Neg.neg h

/-- The first distributional derivative has no atom at the origin. -/
lemma fundamental_distribution_gradient {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    distributionDerivative {i}
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
      regularDistribution (⊤ : Domain n) (gradientKernel i) := by
  ext φ
  simp only [distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.distributionPartial, Multiset.card_singleton, pow_one,
    Multiset.sort_singleton, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    neg_one_mul]
  rw [P102.U4.regular_pairing n ℝ ⊤ _
    ((P201.fundamentalLocalIntegrability n (by omega)).locallyIntegrableOn _),
    P102.U4.regular_pairing n ℝ ⊤ _
    ((gradientKernel_locallyIntegrable (by omega) i).locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, setIntegral_univ]
  change -(∫ x, P201Specs.fundamentalKernel n x * P102.U4.testPartialWord ⊤ [i] φ x) =
    ∫ x, gradientKernel i x * φ x
  rw [fundamental_gradient_pairing hn φ i, neg_neg]


lemma compact_essential_support_of_hasCompactSupport {n : ℕ}
    {F : Space n → ℝ} (hF : HasCompactSupport F) :
    P102.U4.HasCompactEssentialSupport F := by
  exact ⟨⟨tsupport F, hF⟩,
    Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx⟩

lemma regularDistribution_compactSupport_of_continuous {n : ℕ}
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F) :
    IsCompact (P102.U4.relativeSupport (regularDistribution (⊤ : Domain n) F)) := by
  exact P102.U4.regularDistribution_compactSupport_of_essential F
    hF.locallyIntegrable (compact_essential_support_of_hasCompactSupport hc)

lemma holderPotential_eq_functionConvolution {n : ℕ} (F : Space n → ℝ) :
    P201Specs.Elliptic.NewtonHessian.holderPotential F =
      P102.U4.functionConvolution (fundamentalKernel n) F := by
  funext x
  change (∫ y, fundamentalKernel n y * F (x - y)) =
    ∫ y, fundamentalKernel n (x - y) * F y
  rw [← integral_sub_left_eq_self (fun y => fundamentalKernel n y * F (x - y)) volume x]
  simp only [sub_sub_cancel]

lemma regular_holderPotential_eq_rightCompactConvolution {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F)
    (hS : IsCompact (P102.U4.relativeSupport (regularDistribution (⊤ : Domain n) F))) :
    regularDistribution (⊤ : Domain n)
        (P201Specs.Elliptic.NewtonHessian.holderPotential F) =
      P102.U4.rightCompactConvolution
        (regularDistribution (⊤ : Domain n) (fundamentalKernel n))
        (regularDistribution (⊤ : Domain n) F) hS := by
  rw [holderPotential_eq_functionConvolution]
  exact (P102.U4.rightCompactConvolution_regular (fundamentalKernel n) F
    (P201.fundamentalLocalIntegrability n hn) hF.locallyIntegrable
    (Or.inr (compact_essential_support_of_hasCompactSupport hc)) hS).symm

lemma holderPotential_distributionPartial {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F)
    (hS : IsCompact (P102.U4.relativeSupport (regularDistribution (⊤ : Domain n) F)))
    (β : MultiIndex n) :
    distributionDerivative β
        (regularDistribution (⊤ : Domain n)
          (P201Specs.Elliptic.NewtonHessian.holderPotential F)) =
      P102.U4.rightCompactConvolution
        (distributionDerivative β (regularDistribution (⊤ : Domain n) (fundamentalKernel n)))
        (regularDistribution (⊤ : Domain n) F) hS := by
  rw [regular_holderPotential_eq_rightCompactConvolution hn hc hF hS]
  exact P102.U4.rightCompactConvolution_partial_left _ _ _ _

/-- Any locally integrable derivative kernel transports through the ordinary
Newton integral, for continuous compact data; the input kernel identity is
an independent obligation. -/
lemma holderPotential_distributionPartial_of_kernel {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F)
    (β : MultiIndex n) (G : Space n → ℝ) (hG : LocallyIntegrable G volume)
    (hder : distributionDerivative β
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
      regularDistribution (⊤ : Domain n) G) :
    distributionDerivative β
        (regularDistribution (⊤ : Domain n)
          (P201Specs.Elliptic.NewtonHessian.holderPotential F)) =
      regularDistribution (⊤ : Domain n) (P102.U4.functionConvolution G F) := by
  let hS := regularDistribution_compactSupport_of_continuous hc hF
  rw [holderPotential_distributionPartial hn hc hF hS β, hder]
  exact P102.U4.rightCompactConvolution_regular G F hG hF.locallyIntegrable
    (Or.inr (compact_essential_support_of_hasCompactSupport hc)) hS


lemma isHolder_of_bounded_lipschitz {n : ℕ} {g : Space n → ℝ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hg : Continuous g)
    (hc : HasCompactSupport g) {L : NNReal} (hL : LipschitzWith L g) :
    IsHolder α g := by
  obtain ⟨M', hM'⟩ := hc.exists_bound_of_continuous hg
  let M := max M' 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (x : Space n) : ‖g x‖ ≤ M := (hM' x).trans (le_max_left _ _)
  refine ⟨M, max (L : ℝ) (2 * M), hM, le_trans L.coe_nonneg (le_max_left _ _), hbound, ?_⟩
  intro x y
  by_cases hd : dist x y ≤ 1
  · calc
      ‖g x - g y‖ ≤ (L : ℝ) * dist x y := by simpa only [dist_eq_norm] using hL.dist_le_mul x y
      _ ≤ (L : ℝ) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg hd hα1) L.coe_nonneg
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · have hd1 : 1 ≤ dist x y := (not_le.mp hd).le
    calc
      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hbound x, hbound y]
      _ ≤ (2 * M) * dist x y ^ α :=
        le_mul_of_one_le_right (mul_nonneg (by norm_num) hM) (Real.one_le_rpow hd1 hα)
      _ ≤ max (L : ℝ) (2 * M) * dist x y ^ α :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

lemma test_isHolder_half {n : ℕ} (φ : Test ℝ (⊤ : Domain n)) :
    IsHolder (1 / 2 : ℝ) (fun x => φ x) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport φ.contDiff (by simp)
  exact isHolder_of_bounded_lipschitz (by norm_num) (by norm_num) φ.continuous φ.hasCompactSupport hL

lemma hessianKernel_neg {n : ℕ} (i j : Fin n) (x : Space n) :
    hessianKernel i j (-x) = hessianKernel i j x := by
  simp only [hessianKernel, P201Specs.Elliptic.NewtonHessian.hessianKernel,
    norm_neg, PiLp.neg_apply]
  ring

lemma truncatedPairing_eq_truncated {n : ℕ} (i j : Fin n) (ε : ℝ)
    (φ : Test ℝ (⊤ : Domain n)) :
    truncatedPairing i j ε φ = truncated (hessianKernel i j) (fun x => φ x) ε 0 := by
  simp only [truncatedPairing, truncated, zero_sub, norm_neg, hessianKernel_neg]

lemma truncatedPairing_limit {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun x => hessianKernel i j x * φ x) {x | ε < ‖x‖} volume) ∧
    Tendsto (fun ε => truncatedPairing i j ε φ) (𝓝[>] 0)
      (𝓝 (hessianOperator i j (fun x => φ x) 0)) := by
  have h := P201.Elliptic.HolderCancellation.principalValueExists (by omega : 1 ≤ n)
    (1 / 2 : ℝ) (by norm_num) (by norm_num) (hessianKernel i j) (fun x => φ x) (kernelHypotheses hn i j)
    φ.hasCompactSupport (test_isHolder_half φ) 0
  constructor
  · intro ε hε
    simpa only [zero_sub, norm_neg, hessianKernel_neg] using h.1 ε hε
  · simpa only [truncatedPairing_eq_truncated, hessianOperator] using h.2.2.1

lemma convolution_norm_bound {n : ℕ} {k F : Space n → ℝ}
    (hk : LocallyIntegrable k volume) (hF : Continuous F)
    (hc : HasCompactSupport F) {a : Space n} {R S M : ℝ}
    (hsupp : tsupport F ⊆ closedBall a R) (hM : ∀ y, ‖F y‖ ≤ M)
    {x : Space n} (hx : ‖x‖ ≤ S) :
    ‖∫ y, k y * F (x-y)‖ ≤
      (∫ y in closedBall (0 : Space n) (S + ‖a‖ + R), ‖k y‖) * M := by
  let B := closedBall (0 : Space n) (S + ‖a‖ + R)
  have hi : Integrable (fun y => k y * F (x-y)) volume :=
    hk.integrable_smul_right_of_hasCompactSupport
      (hF.comp (continuous_const.sub continuous_id))
      (hc.comp_homeomorph (Homeomorph.subLeft x))
  have hiB : IntegrableOn (fun y => ‖k y‖) B volume :=
    (hk.integrableOn_isCompact (isCompact_closedBall _ _)).norm
  have he : (fun y => k y * F (x-y)) = B.indicator (fun y => k y * F (x-y)) := by
    funext y
    symm
    by_cases hy : y ∈ B
    · simp [hy]
    rw [indicator_of_notMem hy]
    have hz : F (x-y) = 0 := by
      by_contra hn
      have hs : x-y ∈ closedBall a R := hsupp (subset_tsupport _ hn)
      have hh : ‖y‖ ≤ S + ‖a‖ + R := by
        have hy : y = x - a - (x-y-a) := by abel
        rw [hy]
        calc
          ‖x-a-(x-y-a)‖ ≤ ‖x-a‖ + ‖x-y-a‖ := norm_sub_le _ _
          _ ≤ (‖x‖+‖a‖)+R := add_le_add (norm_sub_le _ _) (by simpa [mem_closedBall, dist_eq_norm] using hs)
          _ ≤ S+‖a‖+R := by linarith
      exact hy (by simpa [B, mem_closedBall, dist_zero_right] using hh)
    simp [hz]
  rw [he, integral_indicator measurableSet_closedBall]
  calc
    _ ≤ ∫ y in B, ‖k y * F (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in B, ‖k y‖ * M := by
      apply integral_mono_ae (hi.norm.integrableOn) (hiB.mul_const M)
      filter_upwards [] with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]

lemma gradientConvolution_integrable {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ}
    (hF : Continuous F) (hc : HasCompactSupport F) (i : Fin n) (x : Space n) :
    Integrable (fun y => gradientKernel i y * F (x-y)) volume := by
  exact (gradientKernel_locallyIntegrable hn i).integrable_smul_right_of_hasCompactSupport
    (hF.comp (continuous_const.sub continuous_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x))

open scoped Convolution in
lemma gradientConvolution_continuous {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ}
    (hF : Continuous F) (hc : HasCompactSupport F) (i : Fin n) :
    Continuous (fun x => ∫ y, gradientKernel i y * F (x-y)) := by
  exact hc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (gradientKernel_locallyIntegrable hn i) hF

/-- The size of a potential and of all its proposed first derivatives is
controlled on a prescribed bounded set, before any smoothness is assumed of F. -/
lemma potentialLowerOrderBound {n : ℕ} (hn : 1 ≤ n) (α : ℝ)
    (s : Set (Space n)) (hs : Bornology.IsBounded s) (a : Space n) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
      Continuous F → ∀ x ∈ s,
        ‖holderPotential F x‖ ≤ C * holderNorm α F ∧
        ∀ i : Fin n, ‖∫ y, gradientKernel i y * F (x-y)‖ ≤ C * holderNorm α F := by
  obtain ⟨S, hS⟩ := hs.exists_norm_le
  let B := closedBall (0 : Space n) (S + ‖a‖ + R)
  let L := ∫ y in B, ‖fundamentalKernel n y‖
  let G := fun i : Fin n => ∫ y in B, ‖gradientKernel i y‖
  have hL : 0 ≤ L := integral_nonneg fun y => norm_nonneg _
  have hG (i : Fin n) : 0 ≤ G i := integral_nonneg fun y => norm_nonneg _
  refine ⟨L + ∑ i, G i, add_nonneg hL (Finset.sum_nonneg fun i _ => hG i), ?_⟩
  intro F hc hsupp hHolder hF x hx
  have hb := P201.Elliptic.HolderCancellation.bounds_by_holderNorm hn hHolder
  constructor
  · exact (convolution_norm_bound (P201.fundamentalLocalIntegrability n hn) hF hc hsupp
      hb.2.2.1 (hS x hx)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hG i)) hb.1)
  · intro i
    apply (convolution_norm_bound (gradientKernel_locallyIntegrable hn i) hF hc hsupp
      hb.2.2.1 (hS x hx)).trans
    apply mul_le_mul_of_nonneg_right _ hb.1
    exact (Finset.single_le_sum (fun j _ => hG j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hL)


lemma holderBounds_sub_const_mul {n : ℕ} {α M H N J : ℝ} {g F : Space n → ℝ}
    (hg : HolderBounds α g M H) (hF : HolderBounds α F N J) (c : ℝ) :
    HolderBounds α (fun x => g x - c * F x) (M + ‖c‖ * N) (H + ‖c‖ * J) := by
  refine ⟨by positivity [hg.1, hF.1], by positivity [hg.2.1, hF.2.1], ?_, ?_⟩
  · intro x
    calc
      ‖g x-c*F x‖ ≤ ‖g x‖+‖c*F x‖ := norm_sub_le _ _
      _ ≤ M+‖c‖*N := by rw [norm_mul]; exact add_le_add (hg.2.2.1 _) (mul_le_mul_of_nonneg_left (hF.2.2.1 _) (norm_nonneg _))
  · intro x y
    have he : (g x-c*F x)-(g y-c*F y) = (g x-g y)-c*(F x-F y) := by ring
    rw [he]
    calc
      _ ≤ ‖g x-g y‖+‖c*(F x-F y)‖ := norm_sub_le _ _
      _ ≤ H*dist x y^α+‖c‖*(J*dist x y^α) := by
        rw [norm_mul]
        exact add_le_add (hg.2.2.2 _ _) (mul_le_mul_of_nonneg_left (hF.2.2.2 _ _) (norm_nonneg _))
      _ = _ := by ring

lemma isHolderOn_of_isHolder {n : ℕ} {α : ℝ} {F : Space n → ℝ}
    (hF : IsHolder α F) (s : Set (Space n)) : IsHolderOn α F s := by
  obtain ⟨M,H,hF⟩ := hF
  exact ⟨M,H,hF.1,hF.2.1,fun x _ => hF.2.2.1 x,fun x _ y _ => hF.2.2.2 x y⟩

lemma hessianDensityEstimate {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (i j : Fin n) (a : Space n) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
      let H := fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)
      IsHolder α H ∧ holderNorm α H ≤ C * holderNorm α F := by
  obtain ⟨C,hC,he⟩ := hessianOperatorEstimate hn α hα hα1 i j a R hR
  let c := kronecker i j / (n : ℝ)
  refine ⟨2*(C+‖c‖),by positivity,?_⟩
  intro F hc hsupp hF
  obtain ⟨hOp,hOpN⟩ := he F hc hsupp hF
  have hbOp := P201.Elliptic.HolderCancellation.bounds_by_holderNorm (by omega : 1 ≤ n) hOp
  have hbF := P201.Elliptic.HolderCancellation.bounds_by_holderNorm (by omega : 1 ≤ n) hF
  have hb := holderBounds_sub_const_mul hbOp hbF c
  have hfun : (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) =
      (fun x => hessianOperator i j F x - c * F x) := by funext x; dsimp [c]; ring
  rw [hfun]
  refine ⟨⟨_,_,hb⟩,?_⟩
  calc
    holderNorm α (fun x => hessianOperator i j F x-c*F x) ≤
        (holderNorm α (hessianOperator i j F)+‖c‖*holderNorm α F)+
        (holderNorm α (hessianOperator i j F)+‖c‖*holderNorm α F) :=
      P201.Elliptic.HolderCancellation.holderNorm_le (by omega) hb
    _ ≤ (C*holderNorm α F+‖c‖*holderNorm α F)+
        (C*holderNorm α F+‖c‖*holderNorm α F) := by gcongr
    _ = _ := by ring


lemma holderPotential_distribution_gradient {n : ℕ} (hn : 2 ≤ n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F) (i : Fin n) :
    distributionDerivative {i} (regularDistribution (⊤ : Domain n) (holderPotential F)) =
      regularDistribution (⊤ : Domain n)
        (fun x => ∫ y, gradientKernel i y * F (x-y)) := by
  have he := holderPotential_distributionPartial_of_kernel (by omega : 1 ≤ n) hc hF {i}
    (gradientKernel i) (gradientKernel_locallyIntegrable (by omega) i)
    (fundamental_distribution_gradient hn i)
  convert he using 1
  congr 1
  funext x
  change (∫ y, gradientKernel i y * F (x-y)) =
    ∫ y, gradientKernel i (x-y) * F y
  rw [← integral_sub_left_eq_self (fun y => gradientKernel i y * F (x-y)) volume x]
  simp only [sub_sub_cancel]

lemma hasDerivAt_integral_Iic {f : ℝ → ℝ} (hf : Integrable f) (hc : Continuous f) (x : ℝ) :
    HasDerivAt (fun t => ∫ s in Iic t, f s) (f x) x := by
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable x x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (∫ s in Iic x, f s)
  convert h using 1
  · funext t
    have ht := intervalIntegral.integral_Iic_sub_Iic (hf.integrableOn (s := Iic x))
      (hf.integrableOn (s := Iic t))
    linarith

/-- Scalar convolution with the one-dimensional fundamental solution. -/
def oneDimPotential (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, -|x-y| / 2 * f y

lemma oneDimPotential_integrable {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (x : ℝ) : Integrable (fun y => -|x-y| / 2 * f y) := by
  exact (by fun_prop : Continuous (fun y => -|x-y| / 2 * f y)).integrable_of_hasCompactSupport
    hs.mul_left

lemma oneDimPotential_split {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (x : ℝ) :
    oneDimPotential f x =
      x * (∫ y, f y) / 2 - (∫ y, y * f y) / 2 +
        (∫ y in Iic x, y * f y) - x * (∫ y in Iic x, f y) := by
  have hi : Integrable f volume := hf.integrable_of_hasCompactSupport hs
  have hyi : Integrable (fun y => y * f y) :=
    (continuous_id.mul hf).integrable_of_hasCompactSupport hs.mul_left
  have hui := oneDimPotential_integrable hf hs x
  rw [oneDimPotential, ← intervalIntegral.integral_Iic_add_Ioi hui.integrableOn hui.integrableOn]
  have hleft : (∫ y in Iic x, -|x-y| / 2 * f y) =
      -x / 2 * (∫ y in Iic x, f y) + (∫ y in Iic x, y * f y) / 2 := by
    rw [← integral_const_mul, ← integral_div, ← integral_add
      (hi.integrableOn.const_mul _) (hyi.integrableOn.div_const _)]
    apply setIntegral_congr_fun measurableSet_Iic
    intro y hy
    change -|x-y| / 2 * f y = -x / 2 * f y + y * f y / 2
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    ring
  have hright : (∫ y in Ioi x, -|x-y| / 2 * f y) =
      x / 2 * (∫ y in Ioi x, f y) - (∫ y in Ioi x, y * f y) / 2 := by
    rw [← integral_const_mul, ← integral_div, ← integral_sub
      (hi.integrableOn.const_mul _) (hyi.integrableOn.div_const _)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change -|x-y| / 2 * f y = x / 2 * f y - y * f y / 2
    rw [abs_of_nonpos (sub_nonpos.mpr hy.le)]
    ring
  rw [hleft, hright]
  have hi' := intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn (s := Iic x))
    (hi.integrableOn (s := Ioi x))
  have hyi' := intervalIntegral.integral_Iic_add_Ioi (hyi.integrableOn (s := Iic x))
    (hyi.integrableOn (s := Ioi x))
  rw [← hi', ← hyi']
  ring

lemma hasDerivAt_oneDimPotential {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (oneDimPotential f)
      ((∫ y, f y) / 2 - (∫ y in Iic x, f y)) x := by
  have hi : Integrable f volume := hf.integrable_of_hasCompactSupport hs
  have hyi : Integrable (fun y => y * f y) :=
    (continuous_id.mul hf).integrable_of_hasCompactSupport hs.mul_left
  have h := ((((hasDerivAt_id x).mul_const (∫ y, f y)).div_const 2).sub_const
    ((∫ y, y * f y) / 2)).add
    (hasDerivAt_integral_Iic hyi (continuous_id.mul hf) x)
  have h' := h.sub ((hasDerivAt_id x).mul (hasDerivAt_integral_Iic hi hf x))
  convert h' using 1
  · funext t
    exact oneDimPotential_split hf hs t
  · simp only [id_eq]
    ring

lemma deriv_oneDimPotential {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) :
    deriv (oneDimPotential f) = fun x => (∫ y, f y) / 2 - (∫ y in Iic x, f y) := by
  funext x
  exact (hasDerivAt_oneDimPotential hf hs x).deriv

lemma hasDerivAt_deriv_oneDimPotential {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (x : ℝ) :
    HasDerivAt (deriv (oneDimPotential f)) (-f x) x := by
  rw [deriv_oneDimPotential hf hs]
  exact (hasDerivAt_integral_Iic (hf.integrable_of_hasCompactSupport hs) hf x).const_sub _

lemma deriv_deriv_oneDimPotential {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : deriv (deriv (oneDimPotential f)) = -f := by
  funext x
  exact (hasDerivAt_deriv_oneDimPotential hf hs x).deriv

lemma oneDimPotential_contDiff_two {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : ContDiff ℝ 2 (oneDimPotential f) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_oneDimPotential hf hs x).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_deriv_oneDimPotential hf hs x).differentiableAt, ?_⟩
  rw [deriv_deriv_oneDimPotential hf hs]
  exact hf.neg

private def oneCoord : Space 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)

private lemma oneCoord_apply (x : Space 1) : oneCoord x = x 0 := rfl

private lemma oneCoord_norm (x : Space 1) : ‖x‖ = |oneCoord x| := by
  simp [EuclideanSpace.norm_eq, oneCoord_apply, Real.sqrt_sq_eq_abs]

private lemma oneCoord_measurePreserving : MeasurePreserving oneCoord volume volume := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

private lemma oneCoord_symm_measurePreserving : MeasurePreserving oneCoord.symm volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm (MeasurableEquiv.funUnique (Fin 1) ℝ))

lemma holderPotential_oneCoord (F : Space 1 → ℝ) :
    holderPotential F = (oneDimPotential (F ∘ oneCoord.symm)) ∘ oneCoord := by
  funext x
  unfold holderPotential P201Specs.Elliptic.NewtonHessian.holderPotential
  rw [← integral_sub_left_eq_self (fun y : Space 1 => P201Specs.fundamentalKernel 1 y * F (x-y)) volume x]
  simp only [sub_sub_cancel]
  rw [← oneCoord_symm_measurePreserving.integral_comp oneCoord.symm.toHomeomorph.measurableEmbedding]
  unfold oneDimPotential
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [P201Specs.fundamentalKernel, P201Specs.fundamentalProfile, ite_true]
  rw [oneCoord_norm, map_sub, oneCoord.apply_symm_apply]
  rfl

lemma holderPotential_oneDim_contDiff {F : Space 1 → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : ContDiff ℝ 2 (holderPotential F) := by
  rw [holderPotential_oneCoord]
  exact (oneDimPotential_contDiff_two (hF.comp oneCoord.symm.continuous)
    (hFc.comp_isClosedEmbedding oneCoord.symm.toHomeomorph.isClosedEmbedding)).comp oneCoord.contDiff

private lemma oneCoord_coordinate : oneCoord (coordinate 1 0) = 1 := by
  simp [oneCoord_apply, coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply]

private lemma partial_oneCoord {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    (fun x : Space 1 => fderiv ℝ (g ∘ oneCoord) x (coordinate 1 0)) =
      deriv g ∘ oneCoord := by
  funext x
  rw [fderiv_comp x (hg _) oneCoord.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply, Function.comp_apply]
  change fderiv ℝ g (oneCoord x) (oneCoord (coordinate 1 0)) = _
  rw [oneCoord_coordinate, fderiv_apply_one_eq_deriv]

lemma holderPotential_oneDim_secondPartial {F : Space 1 → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    multiPartial (holderPotential F) ({0, 0} : MultiIndex 1) = -F := by
  have hf := hF.comp oneCoord.symm.continuous
  have hfc := hFc.comp_isClosedEmbedding oneCoord.symm.toHomeomorph.isClosedEmbedding
  have hd : Differentiable ℝ (oneDimPotential (F ∘ oneCoord.symm)) :=
    fun t => (hasDerivAt_oneDimPotential hf hfc t).differentiableAt
  have hdd : Differentiable ℝ (deriv (oneDimPotential (F ∘ oneCoord.symm))) :=
    fun t => (hasDerivAt_deriv_oneDimPotential hf hfc t).differentiableAt
  rw [holderPotential_oneCoord]
  change P102.U4.partialWord _ (({0,0} : MultiIndex 1).sort (· ≤ ·)) = _
  have hsort : ({0,0} : MultiIndex 1).sort (· ≤ ·) = [0,0] := by
    simp [Multiset.sort_cons]
  rw [hsort]
  change (fun x : Space 1 => fderiv ℝ
    (fun x : Space 1 => fderiv ℝ (oneDimPotential (F ∘ oneCoord.symm) ∘ oneCoord) x
      (coordinate 1 0)) x (coordinate 1 0)) = _
  rw [partial_oneCoord hd, partial_oneCoord hdd, deriv_deriv_oneDimPotential hf hfc]
  funext x
  simp

lemma holderPotential_oneDim_distribution {F : Space 1 → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    distributionDerivative ({0, 0} : MultiIndex 1)
      (regularDistribution (⊤ : Domain 1) (holderPotential F)) =
      -(regularDistribution (⊤ : Domain 1) F) := by
  have hc := holderPotential_oneDim_contDiff hF hFc
  have hcompat := P102.U4.derivative_classicalCompatibility 1 ℝ ⊤
    ({0,0} : MultiIndex 1) (holderPotential F) (by simpa using hc.contDiffOn)
  change distributionDerivative ({0,0} : MultiIndex 1)
    (regularDistribution (⊤ : Domain 1) (holderPotential F)) =
      regularDistribution (⊤ : Domain 1) (multiPartial (holderPotential F) {0,0}) at hcompat
  rw [holderPotential_oneDim_secondPartial hF hFc] at hcompat
  rw [hcompat]
  ext φ
  rw [P102.U4.regular_pairing 1 ℝ ⊤ (-F) (hF.neg.locallyIntegrable.locallyIntegrableOn _),
    neg_apply,
    P102.U4.regular_pairing 1 ℝ ⊤ F (hF.locallyIntegrable.locallyIntegrableOn _)]
  simp [integral_neg]

theorem dimensionOnePotential : dimensionOnePotentialStatement := by
  intro α hα hα1 F hFc hFH
  have hF := P201.Elliptic.HolderCancellation.holder_continuous hα hFH
  have hd := holderPotential_oneDim_secondPartial hF hFc
  refine ⟨(potentialBasic (by omega) α hα F hFc hFH).1,
    ⟨holderPotential_oneDim_contDiff hF hFc, ?_⟩, hd,
    holderPotential_oneDim_distribution hF hFc⟩
  intro s hs i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  change IsHolderOn α (multiPartial (holderPotential F) ({0,0} : MultiIndex 1)) s
  rw [hd]
  obtain ⟨M,H,hM,hH,hsup,hhol⟩ := hFH
  refine ⟨M,H,hM,hH,?_,?_⟩
  · intro x hx
    simpa using hsup x
  · intro x hx y hy
    simpa [dist_comm, sub_eq_add_neg, add_comm] using hhol y x



private def mollifyContinuous {n : ℕ} (f : P201Specs.Space n → ℝ) (ε : ℝ) :
    P201Specs.Space n → ℝ :=
  P102.U4.localConvolution (P201Specs.regularDistribution ⊤ f)
    (P102.U4.sobolevMollifierKernel n ℝ ε)

private lemma mollifyContinuous_eq_convolution {n : ℕ} {f : P201Specs.Space n → ℝ}
    (hf : Continuous f) (ε : ℝ) :
    mollifyContinuous f ε = MeasureTheory.convolution
      ((P102.U4.sobolevMollifierBump n ε).normed volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  rw [mollifyContinuous, P102.U4.localConvolution_regular_whole hf.locallyIntegrable]
  funext x
  unfold P102.U2.Young.integralConvolution MeasureTheory.convolution
  rw [← integral_sub_left_eq_self (fun y =>
    (P102.U4.sobolevMollifierKernel n ℝ ε) (x-y) * f y) volume x]
  simp only [sub_sub_cancel]
  rfl

private lemma mollifier_rOut_tendsto (n : ℕ) :
    Tendsto (fun ε => (P102.U4.sobolevMollifierBump n ε).rOut) (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  simp [P102.U4.sobolevMollifierBump, hεpos]

private lemma mollifyContinuous_joint_tendsto {n : ℕ} {f : P201Specs.Space n → ℝ}
    (hf : Continuous f) (x : P201Specs.Space n) :
    Tendsto (fun p : ℝ × P201Specs.Space n => mollifyContinuous f p.1 p.2)
      ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (f x)) := by
  have hb := (mollifier_rOut_tendsto n).comp
    (tendsto_fst : Tendsto (Prod.fst : ℝ × P201Specs.Space n → ℝ)
      ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝[>] 0))
  have hg : Tendsto (fun p : (ℝ × P201Specs.Space n) × P201Specs.Space n => f p.2)
      (((𝓝[>] 0) ×ˢ 𝓝 x) ×ˢ 𝓝 x) (𝓝 (f x)) :=
    (hf.tendsto x).comp tendsto_snd
  have h := ContDiffBump.convolution_tendsto_right (μ := volume)
    (φ := fun p : ℝ × P201Specs.Space n => P102.U4.sobolevMollifierBump n p.1)
    (g := fun _ => f) (k := fun p => p.2) hb
    (Eventually.of_forall fun _ => hf.aestronglyMeasurable) hg tendsto_snd
  simpa only [← mollifyContinuous_eq_convolution hf] using h

private lemma mollifyContinuous_locallyUniform {n : ℕ} {f : P201Specs.Space n → ℝ}
    (hf : Continuous f) :
    TendstoLocallyUniformly (mollifyContinuous f) f (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  exact (((hf.tendsto x).comp tendsto_snd).prodMk_nhds
    (mollifyContinuous_joint_tendsto hf x)).mono_right (nhds_le_uniformity _)

private def coordinateGradient {n : ℕ} (g : Fin n → P201Specs.Space n → ℝ)
    (x : P201Specs.Space n) : P201Specs.Space n →L[ℝ] ℝ :=
  ∑ i : Fin n, g i x • EuclideanSpace.proj i

private lemma coordinateGradient_continuous {n : ℕ}
    {g : Fin n → P201Specs.Space n → ℝ} (hg : ∀ i, Continuous (g i)) :
    Continuous (coordinateGradient g) := by
  exact continuous_finsetSum _ fun i _ => (hg i).smul continuous_const

private lemma mollifyContinuous_hasFDerivAt {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i))
    (ε : ℝ) (x : P201Specs.Space n) :
    HasFDerivAt (mollifyContinuous f ε)
      (coordinateGradient (fun i => mollifyContinuous (g i) ε) x) x := by
  have hd : DifferentiableAt ℝ (mollifyContinuous f ε) x := (P102.U4.localConvolution_contDiff
    (P201Specs.regularDistribution ⊤ f) (P102.U4.sobolevMollifierKernel n ℝ ε)).differentiable
      (by simp) x
  have hi (i : Fin n) : fderiv ℝ (mollifyContinuous f ε) x
      (P102.U4.coordinateVector n i) = mollifyContinuous (g i) ε x := by
    have he := P102.U4.localConvolution_distributionPartial
      P102.U4.distributionConvolution
      (P201Specs.regularDistribution ⊤ f)
      (P102.U4.sobolevMollifierKernel n ℝ ε) {i}
    change P201Specs.multiPartial (mollifyContinuous f ε) {i} =
      P102.U4.localConvolution
        (P201Specs.distributionDerivative {i} (P201Specs.regularDistribution ⊤ f)) _ at he
    rw [hweak i] at he
    simpa [P201Specs.multiPartial, P102.U4.multiPartial, P102.U4.partialWord, mollifyContinuous] using congrFun he x
  have he : coordinateGradient (fun i => mollifyContinuous (g i) ε) x =
      fderiv ℝ (mollifyContinuous f ε) x := by
    ext v
    simp only [coordinateGradient, sum_apply, smul_apply]
    change (∑ i : Fin n, mollifyContinuous (g i) ε x * v i) =
      fderiv ℝ (mollifyContinuous f ε) x v
    have hv : (∑ i : Fin n, v i • P102.U4.coordinateVector n i) = v :=
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    conv_rhs => rw [← hv]
    simp only [map_sum, map_smul, hi, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he]
  exact hd.hasFDerivAt

/-- If a continuous scalar function has continuous distributional coordinate
first derivatives, those are its actual classical first derivatives. -/
theorem continuous_weak_hasFDerivAt {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i))
    (x : P201Specs.Space n) :
    HasFDerivAt f (coordinateGradient g x) x := by
  have hA : TendstoLocallyUniformly
      (fun ε => coordinateGradient (fun i => mollifyContinuous (g i) ε))
      (coordinateGradient g) (𝓝[>] 0) := by
    rw [tendstoLocallyUniformly_iff_forall_tendsto]
    intro z
    have hm : Tendsto (fun p : ℝ × P201Specs.Space n =>
        coordinateGradient (fun i => mollifyContinuous (g i) p.1) p.2)
        ((𝓝[>] 0) ×ˢ 𝓝 z) (𝓝 (coordinateGradient g z)) :=
      tendsto_finsetSum _ fun i _ => (mollifyContinuous_joint_tendsto (hg i) z).smul
        tendsto_const_nhds
    exact ((((coordinateGradient_continuous hg).tendsto z).comp tendsto_snd).prodMk_nhds hm
      ).mono_right (nhds_le_uniformity _)
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
    hA.tendstoLocallyUniformlyOn
    (fun ε z _ => mollifyContinuous_hasFDerivAt hweak ε z)
    (fun z _ => (mollifyContinuous_locallyUniform hf).tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)) (mem_univ x)

/-- Continuous representatives with continuous weak first derivatives are C¹. -/
theorem continuous_weak_contDiff_one {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i)) :
    ContDiff ℝ 1 f := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 0)).2
  exact ⟨coordinateGradient g, contDiff_zero.2 (coordinateGradient_continuous hg),
    continuous_weak_hasFDerivAt hf hg hweak⟩

/-- Identification of the actual first coordinate derivatives. -/
theorem continuous_weak_multiPartial_one {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i))
    (i : Fin n) : P201Specs.multiPartial f {i} = g i := by
  funext x
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_singleton,
    P102.U4.partialWord]
  change fderiv ℝ f x (P102.U4.coordinateVector n i) = g i x
  rw [(continuous_weak_hasFDerivAt hf hg hweak x).fderiv]
  simp [coordinateGradient, sum_apply, smul_apply, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.proj, mul_comm]

/-- Continuous weak first and second derivative densities imply classical C². -/
theorem continuous_weak_contDiff_two {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    {h : Fin n → Fin n → P201Specs.Space n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (hh : ∀ i j, Continuous (h i j))
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i))
    (hweak2 : ∀ i j, P201Specs.distributionDerivative {i, j}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (h i j)) :
    ContDiff ℝ 2 f := by
  have hwg (i j : Fin n) : P201Specs.distributionDerivative {j}
      (P201Specs.regularDistribution ⊤ (g i)) = P201Specs.regularDistribution ⊤ (h i j) := by
    rw [← hweak i]
    change P102.U4.distributionPartial {j}
      (P102.U4.distributionPartial {i} (P201Specs.regularDistribution ⊤ f)) = _
    rw [← P102.U4.derivative_add n ℝ ⊤ {j} {i}]
    change P102.U4.distributionPartial {j,i} (P201Specs.regularDistribution ⊤ f) = _
    rw [Multiset.pair_comm j i]
    exact hweak2 i j
  have hgc1 (i : Fin n) : ContDiff ℝ 1 (g i) :=
    continuous_weak_contDiff_one (hg i) (hh i) (hwg i)
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).2
  refine ⟨coordinateGradient g, ?_, continuous_weak_hasFDerivAt hf hg hweak⟩
  exact ContDiff.sum fun i _ => (hgc1 i).smul contDiff_const

/-- The continuous second weak densities are the actual second derivatives. -/
theorem continuous_weak_multiPartial_two {n : ℕ}
    {f : P201Specs.Space n → ℝ} {g : Fin n → P201Specs.Space n → ℝ}
    {h : Fin n → Fin n → P201Specs.Space n → ℝ}
    (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (hh : ∀ i j, Continuous (h i j))
    (hweak : ∀ i, P201Specs.distributionDerivative {i}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (g i))
    (hweak2 : ∀ i j, P201Specs.distributionDerivative {i, j}
      (P201Specs.regularDistribution ⊤ f) = P201Specs.regularDistribution ⊤ (h i j))
    (i j : Fin n) : P201Specs.multiPartial f {i, j} = h i j := by
  have hC2 := continuous_weak_contDiff_two hf hg hh hweak hweak2
  have hα : ({i,j} : P201Specs.MultiIndex n).card = 2 := by simp
  have hp : Continuous (P201Specs.multiPartial f {i,j}) := by
    have hp := (P102.U4.partialWord_contDiffOn (⊤ : P201Specs.Domain n)
      hC2.contDiffOn (({i,j} : P201Specs.MultiIndex n).sort (· ≤ ·)) 0 (by simp)).continuousOn
    exact continuousOn_univ.mp hp
  have he : P201Specs.regularDistribution ⊤ (P201Specs.multiPartial f {i,j}) =
      P201Specs.regularDistribution ⊤ (h i j) := by
    have hc := P102.U4.derivative_classicalCompatibility n ℝ ⊤ {i,j} f
      (by simpa using hC2.contDiffOn)
    change P201Specs.distributionDerivative {i,j}
      (P201Specs.regularDistribution ⊤ f) =
      P201Specs.regularDistribution ⊤ (P201Specs.multiPartial f {i,j}) at hc
    exact hc.symm.trans (hweak2 i j)
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _ hp (hh i j)
  have hae := (P102.U4.regular_injectivity n ℝ ⊤ _ _
    (hp.locallyIntegrable.locallyIntegrableOn _)
    ((hh i j).locallyIntegrable.locallyIntegrableOn _)).mp he
  simpa using hae


lemma hessian_test_integrable_of_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) (hφ : φ 0 = 0) :
    Integrable (fun x => hessianKernel i j x * φ x) volume := by
  let ψ : Test ℝ (⊤ : Domain n) := {
    toFun x := φ (-x)
    contDiff' := φ.contDiff.comp contDiff_neg
    hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.neg (Space n))
    tsupport_subset' := subset_univ _ }
  have hi := P201.Elliptic.HolderCancellation.compensated_integrable (by omega : 1 ≤ n)
    (by norm_num : (0 : ℝ) < 1 / 2) (kernelHypotheses hn i j)
    ψ.hasCompactSupport (test_isHolder_half ψ) 0
  change Integrable (fun z => hessianKernel i j z *
    (φ (-(0 - z)) - (ball (0 : Space n) 1).indicator (fun _ => φ (-0)) z)) volume at hi
  simpa only [zero_sub, neg_neg, neg_zero, hφ, indicator_zero, sub_zero] using hi

open private P201.coordEquiv P201.coordinate_vector P201.partial_bridge P201.coordinateTest from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental

lemma integral_mul_testPartial_off_origin {n : ℕ} (hn : 2 ≤ n) (j : Fin n)
    (f f' : Space n → ℝ) (φ : Test ℝ (⊤ : Domain n))
    (hfg : Integrable (fun x => f x * φ x) volume)
    (hf'g : Integrable (fun x => f' x * φ x) volume)
    (hfg' : Integrable (fun x => f x * P102.U4.testPartialWord ⊤ [j] φ x) volume)
    (hf : ∀ x ≠ 0, HasLineDerivAt ℝ f (f' x) x (coordinate n j)) :
    (∫ x, f x * P102.U4.testPartialWord ⊤ [j] φ x) = -(∫ x, f' x * φ x) := by
  let e := P201.coordEquiv n
  let ψ := P201.coordinateTest φ
  let ψ' := ExpandedFA.Distributions.testPartialCLM [j] ψ
  have hfline : ∀ x ≠ 0, HasLineDerivAt ℝ (f ∘ e) (f' (e x)) x
      (ExpandedFA.Distributions.coordinateVector j) := by
    intro x hx
    have hh := hf (e x) (by simpa [e] using hx)
    simpa only [HasLineDerivAt, Function.comp_apply, map_add, map_smul,
      e, P201.coordinate_vector] using hh
  have hgline : ∀ x, HasLineDerivAt ℝ ψ (ψ' x) x
      (ExpandedFA.Distributions.coordinateVector j) := by
    intro x
    have h := (ψ.contDiff.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt
      (ExpandedFA.Distributions.coordinateVector j)
    convert h using 1
    rw [ExpandedFA.Distributions.testPartial_formula ℝ n ⊤ [j] ψ]
    rfl
  have he (x : Fin n → ℝ) : P102.U4.testPartialWord ⊤ [j] φ (e x) = ψ' x := by
    rw [P102.U4.testPartialWord_coe]
    calc
      _ = ExpandedFA.Distributions.partialFunction [j] ψ x :=
        (congrFun (P201.partial_bridge φ [j]) x).symm
      _ = ψ' x := (congrFun (ExpandedFA.Distributions.testPartial_formula ℝ n ⊤ [j] ψ) x).symm
  have hm := PiLp.volume_preserving_toLp (ι := Fin n)
  have hfgc : Integrable (fun x : Fin n → ℝ => f (e x) • ψ x) := by
    change Integrable ((fun x => f x * φ x) ∘ WithLp.toLp 2)
    exact (hm.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr hfg
  have hf'gc : Integrable (fun x : Fin n → ℝ => f' (e x) • ψ x) := by
    change Integrable ((fun x => f' x * φ x) ∘ WithLp.toLp 2)
    exact (hm.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr hf'g
  have hfg'c : Integrable (fun x : Fin n → ℝ => f (e x) • ψ' x) := by
    have hh := (hm.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr hfg'
    change Integrable (fun x : Fin n → ℝ => f (e x) * P102.U4.testPartialWord ⊤ [j] φ (e x)) at hh
    simpa only [smul_eq_mul, he] using hh
  have h := ExpandedFA.PartIV.LaplaceFundamental.integral_smul_lineDeriv_off_origin hn j
    (f ∘ e) (f' ∘ e) ψ ψ' hfgc hf'gc hfg'c hfline hgline
  have hchange (g : Space n → ℝ) := hm.integral_comp e.toHomeomorph.measurableEmbedding g
  rw [← hchange (fun x => f x * P102.U4.testPartialWord ⊤ [j] φ x),
    ← hchange (fun x => f' x * φ x)]
  change (∫ x : Fin n → ℝ, f (e x) * P102.U4.testPartialWord ⊤ [j] φ (e x)) =
    -(∫ x : Fin n → ℝ, f' (e x) * ψ x)
  simpa only [he, smul_eq_mul, Function.comp_apply] using h
open private P201.omega_pos from MathGenome.Internal.LinearPDE.P201.Potential.Fundamental

lemma gradientKernel_differentiableAt {n : ℕ} (hn : 1 ≤ n) {x : Space n}
    (hx : x ≠ 0) (i : Fin n) : DifferentiableAt ℝ (gradientKernel i) x := by
  have hnorm : DifferentiableAt ℝ (fun y : Space n => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  change DifferentiableAt ℝ (fun y : Space n => -y i / (omega n * ‖y‖ ^ n)) x
  simp only [div_eq_mul_inv]
  have hd := (hnorm.pow n).const_mul (omega n)
  have hnz := mul_ne_zero (P201.omega_pos hn).ne' (pow_ne_zero n (norm_ne_zero_iff.mpr hx))
  exact ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).differentiableAt.neg).mul
    ((hasDerivAt_inv hnz).comp_hasFDerivAt x hd.hasFDerivAt).differentiableAt

lemma gradient_pairing_of_test_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) (hφ : φ 0 = 0) :
    (∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [j] φ x) =
      -(∫ x, hessianKernel i j x * φ x) := by
  have hg := gradientKernel_locallyIntegrable (by omega : 1 ≤ n) i
  let φ' := P102.U4.testPartialWord ⊤ [j] φ
  apply integral_mul_testPartial_off_origin hn j (gradientKernel i) (hessianKernel i j) φ
    (hg.integrable_smul_right_of_hasCompactSupport φ.continuous φ.hasCompactSupport)
    (hessian_test_integrable_of_zero hn i j φ hφ)
    (hg.integrable_smul_right_of_hasCompactSupport φ'.continuous φ'.hasCompactSupport)
  intro x hx
  have hl := (gradientKernel_differentiableAt (by omega : 1 ≤ n) hx i).hasFDerivAt.hasLineDerivAt
    (coordinate n j)
  simpa only [gradientKernel_coordinate_derivative (by omega : 1 ≤ n) hx i j] using hl



lemma holderPotential_contDiff_one {n : ℕ} (hn : 2 ≤ n) {F : Space n → ℝ}
    (hc : HasCompactSupport F) (hF : Continuous F) : ContDiff ℝ 1 (holderPotential F) := by
  exact continuous_weak_contDiff_one (holderPotential_continuous (by omega) hF hc)
    (gradientConvolution_continuous (by omega) hF hc)
    (holderPotential_distribution_gradient hn hc hF)

lemma holderPotential_firstPartial {n : ℕ} (hn : 2 ≤ n) {F : Space n → ℝ}
    (hc : HasCompactSupport F) (hF : Continuous F) (i : Fin n) :
    multiPartial (holderPotential F) {i} =
      fun x => ∫ y, gradientKernel i y * F (x-y) := by
  exact continuous_weak_multiPartial_one (holderPotential_continuous (by omega) hF hc)
    (gradientConvolution_continuous (by omega) hF hc)
    (holderPotential_distribution_gradient hn hc hF) i


lemma oneDimPotential_deriv_norm_le {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : ℝ) :
    ‖deriv (oneDimPotential f) x‖ ≤ (3 / 2 : ℝ) * ∫ y, ‖f y‖ := by
  have hi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  rw [deriv_oneDimPotential hf hfc]
  change ‖(∫ y, f y) / 2 - ∫ y in Iic x, f y‖ ≤ _
  have hs : (∫ y in Iic x, ‖f y‖) ≤ ∫ y, ‖f y‖ :=
    integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall (fun y => norm_nonneg _)) hi.norm
  calc
    _ ≤ ‖(∫ y, f y) / 2‖ + ‖∫ y in Iic x, f y‖ := norm_sub_le _ _
    _ ≤ (∫ y, ‖f y‖) / 2 + (∫ y, ‖f y‖) := by
      simp only [norm_div, Real.norm_ofNat]
      exact add_le_add (div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) (by norm_num))
        ((norm_integral_le_integral_norm _).trans hs)
    _ = _ := by ring

lemma holderPotential_oneDim_firstPartial_bound {F : Space 1 → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (x : Space 1) :
    ‖multiPartial (holderPotential F) ({0} : MultiIndex 1) x‖ ≤
      (3 / 2 : ℝ) * ∫ y, ‖F y‖ := by
  have hf := hF.comp oneCoord.symm.continuous
  have hfc := hFc.comp_isClosedEmbedding oneCoord.symm.toHomeomorph.isClosedEmbedding
  have hd : Differentiable ℝ (oneDimPotential (F ∘ oneCoord.symm)) :=
    fun t => (hasDerivAt_oneDimPotential hf hfc t).differentiableAt
  rw [holderPotential_oneCoord]
  change ‖P102.U4.partialWord _ (({0} : MultiIndex 1).sort (· ≤ ·)) x‖ ≤ _
  rw [Multiset.sort_singleton]
  change ‖(fun x : Space 1 => fderiv ℝ (oneDimPotential (F ∘ oneCoord.symm) ∘ oneCoord) x
    (coordinate 1 0)) x‖ ≤ _
  rw [partial_oneCoord hd]
  have heq : (∫ y, ‖F (oneCoord.symm y)‖) = ∫ y, ‖F y‖ :=
    oneCoord_symm_measurePreserving.integral_comp oneCoord.symm.toHomeomorph.measurableEmbedding (fun y => ‖F y‖)
  simpa only [Function.comp_apply, heq] using oneDimPotential_deriv_norm_le hf hfc (oneCoord x)

/-- A real supremum respects a nonnegative upper bound even for an empty set. -/
lemma real_sSup_le_of_nonneg {t : Set ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ht : ∀ r ∈ t, r ≤ M) : sSup t ≤ M := by
  rcases t.eq_empty_or_nonempty with he | he
  · simp [he, hM]
  · exact csSup_le he ht

lemma supNormOn_le {n : ℕ} {g : Space n → ℝ} {s : Set (Space n)} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ x ∈ s, ‖g x‖ ≤ M) :
    sSup {r : ℝ | ∃ x ∈ s, r = ‖g x‖} ≤ M := by
  apply real_sSup_le_of_nonneg hM
  rintro r ⟨x,hx,rfl⟩
  exact hg x hx

lemma holderNormOn_le {n : ℕ} {α : ℝ} {g : Space n → ℝ} {s : Set (Space n)}
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hg : ∀ x ∈ s, ‖g x‖ ≤ M)
    (hh : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ H * dist x y ^ α) :
    holderNormOn α g s ≤ M + H := by
  apply add_le_add (supNormOn_le hM hg)
  apply real_sSup_le_of_nonneg hH
  rintro r ⟨x,hx,y,hy,hxy,rfl⟩
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) α)).mpr (hh x hx y hy)

lemma compactSupport_L1_bound {n : ℕ} {F : Space n → ℝ} (_hF : Continuous F)
    (_hFc : HasCompactSupport F) {a : Space n} {R M : ℝ}
    (hsupp : tsupport F ⊆ closedBall a R) (hM : ∀ y, ‖F y‖ ≤ M) :
    (∫ y, ‖F y‖) ≤ M * volume.real (closedBall a R) := by
  have he : (∫ y, ‖F y‖) = ∫ y in closedBall a R, ‖F y‖ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : F y = 0 := by
      by_contra hn
      exact hy (hsupp (subset_tsupport _ hn))
    simp [hz]
  rw [he]
  have hpos : 0 ≤ ∫ y in closedBall a R, ‖F y‖ := integral_nonneg (fun y => norm_nonneg _)
  calc
    _ = ‖∫ y in closedBall a R, ‖F y‖‖ := (Real.norm_of_nonneg hpos).symm
    _ ≤ M * volume.real (closedBall a R) :=
      norm_setIntegral_le_of_norm_le_const (measure_closedBall_lt_top) (fun y hy => by simpa using hM y)

lemma holderNormOn_neg_le {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ} {α : ℝ}
    (hF : IsHolder α F) (s : Set (Space n)) :
    holderNormOn α (-F) s ≤ 2 * holderNorm α F := by
  have h := P201.Elliptic.HolderCancellation.bounds_by_holderNorm hn hF
  have hh : HolderBounds α (-F) (holderNorm α F) (holderNorm α F) := by
    refine ⟨h.1,h.2.1,?_,?_⟩
    · intro x
      simpa using h.2.2.1 x
    · intro x y
      simpa [dist_comm, sub_eq_add_neg, add_comm] using h.2.2.2 y x
  exact (holderNormOn_le hh.1 hh.2.1 (fun x _ => hh.2.2.1 x)
    (fun x _ y _ => hh.2.2.2 x y)).trans_eq (by ring)

/-- The complete quantitative potential theorem in dimension one. -/
theorem dimensionOnePotentialEstimate (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (s : Set (Space 1)) (hs : Bornology.IsBounded s) (a : Space 1) (R : ℝ) (_hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space 1 → ℝ,
      HasCompactSupport F → tsupport F ⊆ closedBall a R → IsHolder α F →
      IsC2HolderLoc α (holderPotential F) ∧
      c2HolderNormOn α (holderPotential F) s ≤ C * holderNorm α F := by
  obtain ⟨C₀,hC₀,hbound⟩ := potentialLowerOrderBound (n := 1) (by omega) α s hs a R
  let V := volume.real (closedBall a R)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨C₀ + (3/2)*V + 2,by positivity,?_⟩
  intro F hFc hsupp hFH
  have hF := P201.Elliptic.HolderCancellation.holder_continuous hα hFH
  have h := dimensionOnePotential α hα hα1 F hFc hFH
  have hN := P201.Elliptic.HolderCancellation.bounds_by_holderNorm (by omega : 1 ≤ 1) hFH
  have hu : sSup {r : ℝ | ∃ x ∈ s, r = ‖holderPotential F x‖} ≤
      C₀ * holderNorm α F :=
    supNormOn_le (mul_nonneg hC₀ hN.1) (fun x hx => (hbound F hFc hsupp hFH hF x hx).1)
  have hgrad : sSup {r : ℝ | ∃ x ∈ s,
      r = ‖multiPartial (holderPotential F) ({0} : MultiIndex 1) x‖} ≤
      ((3/2)*V) * holderNorm α F := by
    apply supNormOn_le (mul_nonneg (mul_nonneg (by norm_num) hV) hN.1)
    intro x hx
    calc
      _ ≤ (3/2) * ∫ y, ‖F y‖ := holderPotential_oneDim_firstPartial_bound hF hFc x
      _ ≤ (3/2) * (holderNorm α F * V) :=
        mul_le_mul_of_nonneg_left (compactSupport_L1_bound hF hFc hsupp hN.2.2.1) (by norm_num)
      _ = _ := by ring
  refine ⟨h.2.1,?_⟩
  unfold c2HolderNormOn
  simp only [Fin.sum_univ_one]
  change _ + _ + holderNormOn α (multiPartial (holderPotential F) ({0,0} : MultiIndex 1)) s ≤ _
  rw [holderPotential_oneDim_secondPartial hF hFc]
  have hh := holderNormOn_neg_le (by omega : 1 ≤ 1) hFH s
  calc
    _ ≤ C₀ * holderNorm α F + ((3/2)*V) * holderNorm α F + 2 * holderNorm α F :=
      add_le_add (add_le_add hu hgrad) hh
    _ = _ := by ring



open P201.Elliptic.HolderCancellation

lemma truncatedKernel_locallyIntegrable {n : ℕ} {K : Space n → ℝ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Space n))) {ε : ℝ} (hε : 0 < ε) :
    LocallyIntegrable ({z : Space n | ε < ‖z‖}.indicator K) volume := by
  apply locallyIntegrable_iff.mpr
  intro s hs
  let S := s ∩ {z : Space n | ε ≤ ‖z‖}
  have hS : IsCompact S := hs.inter_right (isClosed_le continuous_const continuous_norm)
  have hc : ContinuousOn K S := hK.mono (fun z hz => by
    change z ≠ 0
    exact norm_pos_iff.mp (hε.trans_le hz.2))
  have hi := ((hc.integrableOn_compact (μ := volume) hS).integrable_indicator hS.measurableSet).indicator
    (by measurability : MeasurableSet {z : Space n | ε < ‖z‖})
  apply hi.integrableOn.congr
  filter_upwards [ae_restrict_mem hs.measurableSet] with z hz
  by_cases hd : ε < ‖z‖
  · have hzS : z ∈ S := ⟨hz, hd.le⟩
    simp [hd, hzS]
  · simp [hd]

lemma truncated_eq_functionConvolution {n : ℕ} (K F : Space n → ℝ) (ε : ℝ) :
    truncated K F ε =
      P102.U4.functionConvolution ({z : Space n | ε < ‖z‖}.indicator K) F := by
  funext x
  rw [truncated, ← integral_indicator
    (by measurability : MeasurableSet {y : Space n | ε < ‖x-y‖})]
  unfold P102.U4.functionConvolution
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hd : ε < ‖x-y‖ <;> simp [hd]

lemma truncated_supremum_bound {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α)
    {K F : Space n → ℝ} (hK : KernelHypotheses K) (hc : HasCompactSupport F)
    {A M H : ℝ} (hA : 0 ≤ A)
    (hsize : ∀ u : Space n, ‖u‖ = 1 → ‖K u‖ ≤ A)
    (hF : HolderBounds α F M H) {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    ‖truncated K F ε x‖ ≤
      (A * H) * (∫ z : Space n in ball 0 1, ‖z‖ ^ (α - (n : ℝ))) +
        A * ∫ z : Space n, ‖F z‖ := by
  let : NeZero n := ⟨by omega⟩
  have hcont := holder_continuous hα (g := F) ⟨M,H,hF⟩
  have hgi : Integrable F volume := hcont.integrable_of_hasCompactSupport hc
  have hni0 : IntegrableOn (fun z : Space n => (A * H) * ‖z‖ ^ (α - (n : ℝ)))
      (ball 0 1) volume := (radial_majorant_integrable hn hα 1).const_mul (A * H)
  have hni := hni0.integrable_indicator measurableSet_ball
  have hti := (hgi.comp_sub_left x).norm.const_mul A
  rw [truncated_compensated hn hα hK hc ⟨M,H,hF⟩ x hε,
    ← integral_indicator (by measurability : MeasurableSet {z : Space n | ε < ‖z‖})]
  calc
    _ ≤ ∫ z : Space n,
        (ball (0 : Space n) 1).indicator
          (fun z => (A * H) * ‖z‖ ^ (α - (n : ℝ))) z + A * ‖F (x - z)‖ := by
      apply norm_integral_le_of_norm_le (hni.add hti)
      filter_upwards [volume.ae_ne (0 : Space n)] with z hz
      by_cases hd : ε < ‖z‖
      · simpa [hd] using compensated_norm_bound hA hK hsize hF x hz
      · simp only [mem_ofPred_eq, hd, not_false_eq_true, indicator_of_notMem, norm_zero]
        have hrad : 0 ≤ (ball (0 : Space n) 1).indicator
            (fun z => (A * H) * ‖z‖ ^ (α - (n : ℝ))) z := by
          apply indicator_nonneg
          intro w hw
          exact mul_nonneg (mul_nonneg hA hF.2.1) (Real.rpow_nonneg (norm_nonneg _) _)
        exact add_nonneg hrad (mul_nonneg hA (norm_nonneg _))
    _ = _ := by
      rw [integral_add hni hti, integral_indicator measurableSet_ball,
        integral_const_mul, integral_const_mul]
      congr 1
      congr 1
      exact (volume.measurePreserving_sub_left x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding (fun z : Space n => ‖F z‖)

lemma truncated_pairing_convolutionInner {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : Continuous F)
    (hS : IsCompact (P102.U4.relativeSupport (regularDistribution (⊤ : Domain n) F)))
    (φ : Test ℝ (⊤ : Domain n)) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, truncated (hessianKernel i j) F ε x * φ x) =
      truncatedPairing i j ε (P102.U4.convolutionInnerTest
        (regularDistribution (⊤ : Domain n) F) hS φ) := by
  let Kε := {z : Space n | ε < ‖z‖}.indicator (hessianKernel i j)
  have hKi : LocallyIntegrable Kε volume :=
    truncatedKernel_locallyIntegrable (hessianKernel_smooth i j).continuousOn hε
  rw [truncated_eq_functionConvolution]
  change (∫ x, P102.U4.functionConvolution Kε F x * φ x) = _
  rw [P102.U4.functionConvolution_pairing_right Kε F hKi hF.locallyIntegrable
    ⟨tsupport F,hc⟩ (Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx) φ]
  unfold truncatedPairing
  rw [← integral_indicator (by measurability : MeasurableSet {z : Space n | ε < ‖z‖})]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hψ : P102.U4.convolutionInnerTest
        (regularDistribution (⊤ : Domain n) F) hS φ z = ∫ y, F y * φ (z+y) := by
      change P102.U4.convolutionInner (regularDistribution (⊤ : Domain n) F) φ z = _
      exact P102.U4.distributionConvolution_regularInner n ℝ F hF.locallyIntegrable φ z
    change Kε z * (∫ y, F y * φ (z+y)) =
      {z : Space n | ε < ‖z‖}.indicator (fun z => hessianKernel i j z *
        (P102.U4.convolutionInnerTest (regularDistribution (⊤ : Domain n) F) hS φ) z) z
    by_cases hd : ε < ‖z‖
    · simp only [Kε, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hd]
      rw [hψ]
    · simp only [Kε, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hd, zero_mul]

/-- The actual principal-value convolution is the density of distribution
convolution with any distribution having the actual punctured test limits. -/
lemma hessianOperator_regular_convolution {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (i j : Fin n)
    {F : Space n → ℝ} (hc : HasCompactSupport F) (hF : IsHolder α F)
    (T : Distribution ℝ (⊤ : Domain n))
    (hT : ∀ ψ : Test ℝ (⊤ : Domain n),
      Tendsto (fun ε => truncatedPairing i j ε ψ) (𝓝[>] 0) (𝓝 (T ψ)))
    (hS : IsCompact (P102.U4.relativeSupport (regularDistribution (⊤ : Domain n) F))) :
    P102.U4.rightCompactConvolution T (regularDistribution (⊤ : Domain n) F) hS =
      regularDistribution (⊤ : Domain n) (hessianOperator i j F) := by
  have hcont := holder_continuous hα hF
  have hPV := hessianOperatorHolder hn α hα hα1 F hc hF i j
  have hPVcont := holder_continuous hα hPV.1
  obtain ⟨M,H,hFH⟩ := hF
  obtain ⟨A,B,hKB⟩ := sphere_bounds_exist (kernelHypotheses hn i j)
  let C := (A * H) * (∫ z : Space n in ball 0 1, ‖z‖ ^ (α - (n : ℝ))) +
    A * ∫ z : Space n, ‖F z‖
  have hbound (ε : ℝ) (hε : 0 < ε) (x : Space n) :
      ‖truncated (hessianKernel i j) F ε x‖ ≤ C :=
    truncated_supremum_bound (by omega : 1 ≤ n) hα (kernelHypotheses hn i j) hc
      hKB.1 (fun u hu => (hKB.2.2 u hu).1) hFH hε x
  have hmeas (ε : ℝ) (hε : 0 < ε) :
      AEStronglyMeasurable (truncated (hessianKernel i j) F ε) volume := by
    rw [truncated_eq_functionConvolution]
    exact (P102.U4.functionConvolution_local_right _ F
      (truncatedKernel_locallyIntegrable (hessianKernel_smooth i j).continuousOn hε)
      hcont.locallyIntegrable ⟨tsupport F,hc⟩
      (Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx)).2.aestronglyMeasurable
  ext φ
  rw [P102.U4.rightCompactConvolution_apply,
    P102.U4.regular_pairing n ℝ ⊤ _ (hPVcont.locallyIntegrable.locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  have hL : Tendsto (fun ε => ∫ x, truncated (hessianKernel i j) F ε x * φ x)
      (𝓝[>] 0) (𝓝 (∫ x, hessianOperator i j F x * φ x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖φ x‖)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hmeas ε hε).mul φ.continuous.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound ε hε x) (norm_nonneg _)
    · exact (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.const_mul C
    · exact Eventually.of_forall fun x => ((hPV.2 x).2.2.1).mul_const (φ x)
  have hR := hT (P102.U4.convolutionInnerTest
    (regularDistribution (⊤ : Domain n) F) hS φ)
  apply tendsto_nhds_unique hR
  apply hL.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact truncated_pairing_convolutionInner hn i j hc hcont hS φ hε


/-- Quantitative assembly after the pointwise potential Hessian is identified. -/
lemma potentialEstimate_of_hessian (hess : potentialHessianStatement) : potentialEstimateStatement := by
  intro n hn α hα hα1 s hs a R hR
  by_cases hn1 : n = 1
  · subst n
    exact dimensionOnePotentialEstimate α hα hα1 s hs a R hR
  have hn2 : 2 ≤ n := by omega
  obtain ⟨C₀,hC₀,hbound⟩ := potentialLowerOrderBound hn α s hs a R
  choose C hC hEstimate using fun i j : Fin n => hessianDensityEstimate hn2 α hα hα1 i j a R hR
  let D := C₀ + (∑ _i : Fin n, C₀) + ∑ i : Fin n, ∑ j : Fin n, 2 * C i j
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (add_nonneg hC₀ (Finset.sum_nonneg (fun _ _ => hC₀)))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (by norm_num) (hC i j))))
  refine ⟨D,hD,?_⟩
  intro F hFc hsupp hFH
  have hF := P201.Elliptic.HolderCancellation.holder_continuous hα hFH
  have h := hess hn2 α hα hα1 F hFc hFH
  have hN := P201.Elliptic.HolderCancellation.bounds_by_holderNorm hn hFH
  have hu : sSup {r : ℝ | ∃ x ∈ s, r = ‖holderPotential F x‖} ≤ C₀ * holderNorm α F :=
    supNormOn_le (mul_nonneg hC₀ hN.1) (fun x hx => (hbound F hFc hsupp hFH hF x hx).1)
  have hgrad (i : Fin n) : sSup {r : ℝ | ∃ x ∈ s,
      r = ‖multiPartial (holderPotential F) {i} x‖} ≤ C₀ * holderNorm α F := by
    apply supNormOn_le (mul_nonneg hC₀ hN.1)
    intro x hx
    rw [holderPotential_firstPartial hn2 hFc hF i]
    exact (hbound F hFc hsupp hFH hF x hx).2 i
  have hhess (i j : Fin n) :
      holderNormOn α (multiPartial (holderPotential F) {i,j}) s ≤ (2 * C i j) * holderNorm α F := by
    have heq : multiPartial (holderPotential F) {i,j} =
        fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ) := (h.2.2 i j).2.1
    rw [heq]
    obtain ⟨hout,houtN⟩ := hEstimate i j F hFc hsupp hFH
    have hb := P201.Elliptic.HolderCancellation.bounds_by_holderNorm hn hout
    calc
      holderNormOn α (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) s ≤
          holderNorm α (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) +
          holderNorm α (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) :=
        holderNormOn_le hb.1 hb.2.1 (fun x _ => hb.2.2.1 x) (fun x _ y _ => hb.2.2.2 x y)
      _ ≤ C i j * holderNorm α F + C i j * holderNorm α F := add_le_add houtN houtN
      _ = _ := by ring
  refine ⟨h.2.1,?_⟩
  unfold c2HolderNormOn
  change sSup {r : ℝ | ∃ x ∈ s, r = ‖holderPotential F x‖} +
      (∑ i : Fin n, sSup {r : ℝ | ∃ x ∈ s, r = ‖multiPartial (holderPotential F) {i} x‖}) +
      (∑ i : Fin n, ∑ j : Fin n, holderNormOn α (multiPartial (holderPotential F) {i,j}) s) ≤ _
  calc
    _ ≤ C₀ * holderNorm α F + (∑ _i : Fin n, C₀ * holderNorm α F) +
        (∑ i : Fin n, ∑ j : Fin n, (2 * C i j) * holderNorm α F) :=
      add_le_add (add_le_add hu (Finset.sum_le_sum (fun i _ => hgrad i)))
        (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hhess i j)))
    _ = D * holderNorm α F := by
      simp only [D, Finset.sum_mul, add_mul]



lemma potential_distribution_hessian_of_identity (hDist : distributionIdentityStatement)
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (F : Space n → ℝ) (hc : HasCompactSupport F) (hF : IsHolder α F) (i j : Fin n) :
    distributionDerivative {i,j} (regularDistribution (⊤ : Domain n) (holderPotential F)) =
      regularDistribution (⊤ : Domain n)
        (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) := by
  have hcont := P201.Elliptic.HolderCancellation.holder_continuous hα hF
  have hOpcont := P201.Elliptic.HolderCancellation.holder_continuous hα
    (hessianOperatorHolder hn α hα hα1 F hc hF i j).1
  have hHcont : Continuous (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) :=
    hOpcont.sub ((continuous_const.mul hcont).div_const _)
  let hS := regularDistribution_compactSupport_of_continuous hc hcont
  obtain ⟨T,hT,hidentity⟩ := hDist hn i j
  rw [holderPotential_distributionPartial (by omega) hc hcont hS]
  change P102.U4.rightCompactConvolution
    (P201Specs.distributionDerivative ({i,j} : P201Specs.MultiIndex n)
      (P201Specs.regularDistribution (⊤ : P201Specs.Domain n) (P201Specs.fundamentalKernel n)))
    (P201Specs.regularDistribution (⊤ : P201Specs.Domain n) F) hS = _
  rw [hidentity]
  have hlinear : P102.U4.rightCompactConvolution
      (T - (kronecker i j / (n : ℝ)) • P201Specs.originDirac n)
      (regularDistribution (⊤ : Domain n) F) hS =
      P102.U4.rightCompactConvolution T (regularDistribution (⊤ : Domain n) F) hS -
      (kronecker i j / (n : ℝ)) • P102.U4.rightCompactConvolution (P201Specs.originDirac n)
        (regularDistribution (⊤ : Domain n) F) hS := by
    ext φ
    rfl
  rw [hlinear, hessianOperator_regular_convolution hn α hα hα1 i j hc hF T (fun φ => (hT φ).2) hS,
    P201.originDirac_rightCompactConvolution]
  ext φ
  change regularDistribution (⊤ : Domain n) (hessianOperator i j F) φ -
      (kronecker i j / (n : ℝ)) * regularDistribution (⊤ : Domain n) F φ = _
  rw [P102.U4.regular_pairing n ℝ ⊤ _ (hOpcont.locallyIntegrable.locallyIntegrableOn _),
    P102.U4.regular_pairing n ℝ ⊤ _ (hcont.locallyIntegrable.locallyIntegrableOn _),
    P102.U4.regular_pairing n ℝ ⊤ _ (hHcont.locallyIntegrable.locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  have hiOp : Integrable (fun x => hessianOperator i j F x * φ x) volume :=
    hOpcont.locallyIntegrable.integrable_smul_right_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  have hiF : Integrable (fun x => F x * φ x) volume :=
    hcont.locallyIntegrable.integrable_smul_right_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  rw [← integral_const_mul, ← integral_sub hiOp (hiF.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring


lemma hessianDensity_isHolder {n : ℕ} (hn : 2 ≤ n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {F : Space n → ℝ}
    (hc : HasCompactSupport F) (hF : IsHolder α F) (i j : Fin n) :
    IsHolder α (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) := by
  obtain ⟨M,H,hout⟩ := (hessianOperatorHolder hn α hα hα1 F hc hF i j).1
  obtain ⟨N,J,hFin⟩ := hF
  have hb := holderBounds_sub_const_mul hout hFin (kronecker i j / (n : ℝ))
  convert (show IsHolder α (fun x => hessianOperator i j F x -
    (kronecker i j / (n : ℝ)) * F x) from ⟨_,_,hb⟩) using 1
  funext x
  ring

/-- Classical and local Hölder assembly from the actual distributional densities. -/
lemma potentialHessian_of_distribution_density
    (hweak2 : ∀ {n : ℕ}, 2 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
      ∀ F : Space n → ℝ, HasCompactSupport F → IsHolder α F → ∀ i j : Fin n,
        distributionDerivative {i,j} (regularDistribution (⊤ : Domain n) (holderPotential F)) =
          regularDistribution (⊤ : Domain n)
            (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ))) :
    potentialHessianStatement := by
  intro n hn α hα hα1 F hc hFH
  have hF := P201.Elliptic.HolderCancellation.holder_continuous hα hFH
  have hH (i j : Fin n) : IsHolder α
      (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) :=
    hessianDensity_isHolder hn hα hα1 hc hFH i j
  have hHc (i j : Fin n) : Continuous
      (fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ)) :=
    P201.Elliptic.HolderCancellation.holder_continuous hα (hH i j)
  have hC2 : ContDiff ℝ 2 (holderPotential F) := continuous_weak_contDiff_two
    (holderPotential_continuous (by omega) hF hc)
    (gradientConvolution_continuous (by omega) hF hc) hHc
    (holderPotential_distribution_gradient hn hc hF) (hweak2 hn α hα hα1 F hc hFH)
  have hd (i j : Fin n) : multiPartial (holderPotential F) {i,j} =
      fun x => hessianOperator i j F x - kronecker i j * F x / (n : ℝ) :=
    continuous_weak_multiPartial_two
      (holderPotential_continuous (by omega) hF hc)
      (gradientConvolution_continuous (by omega) hF hc) hHc
      (holderPotential_distribution_gradient hn hc hF) (hweak2 hn α hα hα1 F hc hFH) i j
  refine ⟨holderPotential_integrable (by omega) hF hc,⟨hC2,?_⟩,?_⟩
  · intro s hs i j
    change IsHolderOn α (multiPartial (holderPotential F) {i,j}) s
    rw [hd i j]
    exact isHolderOn_of_isHolder (hH i j) s
  · intro i j
    refine ⟨?_,hd i j,hweak2 hn α hα hα1 F hc hFH i j⟩
    intro x
    exact ((hessianOperatorHolder hn α hα hα1 F hc hFH i j).2 x).2.2.1


end P201.Elliptic.NewtonHessian


noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff ENNReal
namespace P201.Elliptic.NewtonHessian
open P201Specs P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

lemma truncatedPairing_sub_smul {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ χ : Test ℝ (⊤ : Domain n)) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    truncatedPairing i j ε (φ - c • χ) =
      truncatedPairing i j ε φ - c * truncatedPairing i j ε χ := by
  have hφ := (truncatedPairing_limit hn i j φ).1 ε hε
  have hχ := (truncatedPairing_limit hn i j χ).1 ε hε
  have he (x : Space n) : hessianKernel i j x * (φ - c • χ) x =
      hessianKernel i j x * φ x - c * (hessianKernel i j x * χ x) := by
    change hessianKernel i j x * (φ x - c * χ x) = _
    ring
  unfold truncatedPairing
  simp_rw [he]
  rw [integral_sub hφ (hχ.const_mul c), integral_const_mul]

lemma hessianOperator_test_sub_smul {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ χ : Test ℝ (⊤ : Domain n)) (c : ℝ) :
    hessianOperator i j (fun x => (φ - c • χ) x) 0 =
      hessianOperator i j (fun x => φ x) 0 -
        c * hessianOperator i j (fun x => χ x) 0 := by
  have hψ := (truncatedPairing_limit hn i j (φ - c • χ)).2
  have hφ := (truncatedPairing_limit hn i j φ).2
  have hχ := (truncatedPairing_limit hn i j χ).2
  apply tendsto_nhds_unique hψ
  apply (hφ.sub (hχ.const_mul c)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (truncatedPairing_sub_smul hn i j φ χ c hε).symm

end P201.Elliptic.NewtonHessian

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff ENNReal
namespace P201.Elliptic.NewtonHessianContact
open P201Specs P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation
open P201.Elliptic.NewtonHessian

def radialCutoff (n : ℕ) : Test ℝ (⊤ : Domain n) where
  toFun x := (ContDiffBumpBase.ofInnerProductSpace (Space n)).toFun 2 x
  contDiff' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((ContDiffBumpBase.ofInnerProductSpace (Space n)).smooth.contDiffAt
      (prod_mem_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)) univ_mem)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  hasCompactSupport' := by
    change IsCompact (closure (Function.support _))
    rw [(ContDiffBumpBase.ofInnerProductSpace (Space n)).support 2 (by norm_num)]
    exact (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  tsupport_subset' := subset_univ _

lemma radialCutoff_apply (n : ℕ) (x : Space n) :
    radialCutoff n x = Real.smoothTransition (2 - ‖x‖) := by
  change Real.smoothTransition ((2 - ‖x‖) / (2 - 1)) = _
  norm_num

lemma radialCutoff_zero (n : ℕ) : radialCutoff n 0 = 1 := by
  rw [radialCutoff_apply]
  norm_num [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]

lemma radialCutoff_isometry {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (x : Space n) :
    radialCutoff n (e x) = radialCutoff n x := by
  simp only [radialCutoff_apply, e.norm_map]

lemma radialCutoff_derivative {n : ℕ} {x : Space n} (hx : x ≠ 0) (j : Fin n) :
    fderiv ℝ (radialCutoff n) x (coordinate n j) =
      -deriv Real.smoothTransition (2 - ‖x‖) * (x j / ‖x‖) := by
  have hd : HasFDerivAt (fun y : Space n => (2 : ℝ) - ‖y‖)
      (-fderiv ℝ (fun y : Space n => ‖y‖) x) x :=
    (differentiableAt_id.norm ℝ hx).hasFDerivAt.const_sub 2
  have ht := ((show ContDiff ℝ (1 : ℕ∞) Real.smoothTransition from Real.smoothTransition.contDiff).differentiable (by simp) (2 - ‖x‖)).hasDerivAt.comp_hasFDerivAt x hd
  have he : (fun y : Space n => Real.smoothTransition (2 - ‖y‖)) = radialCutoff n := by
    funext y
    exact (radialCutoff_apply n y).symm
  change HasFDerivAt (fun y : Space n => Real.smoothTransition (2 - ‖y‖)) _ x at ht
  rw [he] at ht
  rw [ht.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul, norm_fderiv_coordinate hx]
  ring

lemma radial_diagonal_integrals_equal {n : ℕ} (q : ℝ → ℝ) (i j : Fin n) :
    (∫ x : Space n, (x i) ^ 2 * q ‖x‖) = ∫ x : Space n, (x j) ^ 2 * q ‖x‖ := by
  let e : Space n ≃ₗᵢ[ℝ] Space n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => (x i) ^ 2 * q ‖x‖)
  simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using h.symm

lemma radial_mixed_integral_zero {n : ℕ} (q : ℝ → ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Space n, x i * x j * q ‖x‖) = 0 := by
  classical
  let e : Space n ≃ₗᵢ[ℝ] Space n := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin n => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => x i * x j * q ‖x‖)
  have he (x : Space n) : e x i * e x j * q ‖e x‖ = -(x i * x j * q ‖x‖) := by
    rw [e.norm_map]
    simp [e, LinearIsometryEquiv.piLpCongrRight_apply, hij.symm]
  simp_rw [he, integral_neg] at h
  linarith

lemma radialCutoff_gradient_pairing_integrand {n : ℕ} {x : Space n}
    (hx : x ≠ 0) (i j : Fin n) :
    gradientKernel i x * P102.U4.testPartialWord ⊤ [j] (radialCutoff n) x =
      x i * x j * (deriv Real.smoothTransition (2 - ‖x‖) / (omega n * ‖x‖ ^ (n + 1))) := by
  rw [P102.U4.testPartialWord_coe]
  change gradientKernel i x * fderiv ℝ (radialCutoff n) x (coordinate n j) = _
  rw [radialCutoff_derivative hx]
  unfold gradientKernel
  rw [pow_add]
  ring

lemma radialCutoff_gradient_pairing_mixed {n : ℕ} (hn : 1 ≤ n) (i j : Fin n)
    (hij : i ≠ j) :
    (∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [j] (radialCutoff n) x) = 0 := by
  let : NeZero n := ⟨by omega⟩
  have he : (fun x : Space n => gradientKernel i x * P102.U4.testPartialWord ⊤ [j] (radialCutoff n) x)
      =ᵐ[volume] (fun x => x i * x j *
      (deriv Real.smoothTransition (2 - ‖x‖) / (omega n * ‖x‖ ^ (n + 1)))) := by
    filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    exact radialCutoff_gradient_pairing_integrand hx i j
  rw [integral_congr_ae he]
  exact radial_mixed_integral_zero
    (fun r => deriv Real.smoothTransition (2 - r) / (omega n * r ^ (n + 1))) i j hij

lemma radialCutoff_gradient_pairing_diagonal {n : ℕ} (hn : 1 ≤ n) (i j : Fin n) :
    (∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [i] (radialCutoff n) x) =
    ∫ x, gradientKernel j x * P102.U4.testPartialWord ⊤ [j] (radialCutoff n) x := by
  let : NeZero n := ⟨by omega⟩
  have he (k : Fin n) : (fun x : Space n => gradientKernel k x * P102.U4.testPartialWord ⊤ [k] (radialCutoff n) x)
      =ᵐ[volume] (fun x => (x k) ^ 2 *
      (deriv Real.smoothTransition (2 - ‖x‖) / (omega n * ‖x‖ ^ (n + 1)))) := by
    filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    rw [radialCutoff_gradient_pairing_integrand hx, pow_two]
  rw [integral_congr_ae (he i), integral_congr_ae (he j)]
  exact radial_diagonal_integrals_equal
    (fun r => deriv Real.smoothTransition (2 - r) / (omega n * r ^ (n + 1))) i j

lemma gradient_trace_pairing {n : ℕ} (hn : 2 ≤ n) (φ : Test ℝ (⊤ : Domain n)) :
    (∑ i : Fin n, ∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [i] φ x) = φ 0 := by
  have hsecond (i : Fin n) :
      distributionDerivative ({i, i} : MultiIndex n)
        (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) =
      distributionDerivative {i} (regularDistribution (⊤ : Domain n) (gradientKernel i)) := by
    rw [show ({i, i} : MultiIndex n) = {i} + {i} by simp]
    change P102.U4.distributionPartial ({i} + {i}) _ = _
    rw [P102.U4.derivative_add n ℝ ⊤]
    rw [show P102.U4.distributionPartial {i}
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) = _ from
      fundamental_distribution_gradient hn i]
  have hscalar (i : Fin n) :
      distributionDerivative {i} (regularDistribution (⊤ : Domain n) (gradientKernel i)) φ =
      -(∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [i] φ x) := by
    rw [P102.U4.distributionPartial_singleton_apply,
      P102.U4.regular_pairing n ℝ ⊤ _
        ((gradientKernel_locallyIntegrable (by omega) i).locallyIntegrableOn _)]
    simp only [TopologicalSpace.Opens.coe_top, setIntegral_univ]
  have h := congrArg (fun T : Distribution ℝ (⊤ : Domain n) => T φ)
    (P201.fundamentalSolution n (by omega))
  change -(∑ i : Fin n, distributionDerivative ({i, i} : MultiIndex n)
    (regularDistribution (⊤ : Domain n) (fundamentalKernel n))) φ = φ 0 at h
  simp only [sum_apply, hsecond, hscalar,
    Finset.sum_neg_distrib, neg_neg] at h
  exact h

lemma radialCutoff_gradient_pairing {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [j] (radialCutoff n) x) =
      kronecker i j / (n : ℝ) := by
  by_cases hij : i = j
  · subst j
    have h := gradient_trace_pairing hn (radialCutoff n)
    simp_rw [radialCutoff_gradient_pairing_diagonal (by omega : 1 ≤ n) (j := i)] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      radialCutoff_zero] at h
    simp only [kronecker, ite_true]
    exact (eq_div_iff (by exact_mod_cast (show n ≠ 0 by omega))).mpr (by linarith)
  · rw [radialCutoff_gradient_pairing_mixed (by omega) i j hij]
    simp [kronecker, hij]

lemma radial_kernel_integral_zero {n : ℕ} (hn : 1 ≤ n) (K : Space n → ℝ)
    (hK : KernelHypotheses K) (q : ℝ → ℝ) :
    (∫ x, K x * q ‖x‖) = 0 := by
  rw [P201.Elliptic.HolderCancellation.integral_polar_product hn]
  have he (p : sphere (0 : Space n) 1 × Ioi (0 : ℝ)) :
      K (p.2.1 • p.1.1) * q ‖p.2.1 • p.1.1‖ =
        K p.1.1 * ((p.2.1 ^ n)⁻¹ * q p.2.1) := by
    have hθ : ‖p.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
    have hθ0 : p.1.1 ≠ 0 := norm_ne_zero_iff.mp (by rw [hθ]; norm_num)
    have hr : 0 < p.2.1 := p.2.2
    rw [hK.homogeneous _ hr _ hθ0]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one,
      smul_eq_mul]
    ring
  simp_rw [he]
  exact (integral_prod_mul (μ := (volume : Measure (Space n)).toSphere)
    (ν := Measure.volumeIoiPow (n - 1)) (fun θ : sphere (0 : Space n) 1 => K θ.1)
    (fun r : Ioi (0 : ℝ) => (r.1 ^ n)⁻¹ * q r.1)).trans
    (by rw [P201.Elliptic.HolderCancellation.polar_mean_zero hK, zero_mul])

lemma radialCutoff_truncatedPairing_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (ε : ℝ) : truncatedPairing i j ε (radialCutoff n) = 0 := by
  rw [truncatedPairing, ← integral_indicator (by measurability :
    MeasurableSet {x : Space n | ε < ‖x‖})]
  have he : {x : Space n | ε < ‖x‖}.indicator
      (fun x => P201Specs.Elliptic.NewtonHessian.hessianKernel i j x * radialCutoff n x) =
      (fun x => P201Specs.Elliptic.NewtonHessian.hessianKernel i j x *
        (if ε < ‖x‖ then Real.smoothTransition (2 - ‖x‖) else 0)) := by
    funext x
    by_cases hx : ε < ‖x‖ <;> simp [hx, radialCutoff_apply]
  rw [he]
  exact radial_kernel_integral_zero (by omega) _ (kernelHypotheses hn i j)
    (fun r => if ε < r then Real.smoothTransition (2 - r) else 0)

lemma radialCutoff_pv_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    hessianOperator i j (fun x => radialCutoff n x) 0 = 0 := by
  have h := (truncatedPairing_limit hn i j (radialCutoff n)).2
  simp_rw [radialCutoff_truncatedPairing_zero hn i j] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma fundamental_hessian_pairing {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) :
    distributionDerivative ({i, j} : MultiIndex n)
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) φ =
      -(∫ x, gradientKernel i x * P102.U4.testPartialWord ⊤ [j] φ x) := by
  rw [show ({i, j} : MultiIndex n) = {j} + {i} by simp only [Multiset.singleton_add]; exact Multiset.cons_swap _ _ _]
  change P102.U4.distributionPartial ({j} + {i}) _ φ = _
  rw [P102.U4.derivative_add n ℝ ⊤,
    show P102.U4.distributionPartial {i}
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) = _ from
      fundamental_distribution_gradient hn i,
    P102.U4.distributionPartial_singleton_apply,
    P102.U4.regular_pairing n ℝ ⊤ _
      ((gradientKernel_locallyIntegrable (by omega) i).locallyIntegrableOn _)]
  simp only [TopologicalSpace.Opens.coe_top, setIntegral_univ]

lemma pv_pairing_of_test_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) (hφ : φ 0 = 0) :
    hessianOperator i j (fun x => φ x) 0 = ∫ x, P201Specs.Elliptic.NewtonHessian.hessianKernel i j x * φ x := by
  have h := P201.Elliptic.HolderCancellation.principalValueExists (by omega : 1 ≤ n)
    (1 / 2 : ℝ) (by norm_num) (by norm_num) (P201Specs.Elliptic.NewtonHessian.hessianKernel i j)
    (fun x => φ x) (kernelHypotheses hn i j) φ.hasCompactSupport (test_isHolder_half φ) 0
  change P201Specs.Elliptic.HolderCancellation.principalValue _ _ _ = _
  rw [h.2.2.2]
  change (∫ z, P201Specs.Elliptic.NewtonHessian.hessianKernel i j z *
    (φ (0 - z) - (ball (0 : Space n) 1).indicator (fun _ => φ 0) z)) = _
  simp only [hφ, indicator_zero, sub_zero, zero_sub]
  simpa only [hessianKernel_neg] using
    (integral_neg_eq_self (fun z => P201Specs.Elliptic.NewtonHessian.hessianKernel i j z * φ z) volume)

lemma fundamental_hessian_pv_of_test_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    (φ : Test ℝ (⊤ : Domain n)) (hφ : φ 0 = 0) :
    distributionDerivative ({i, j} : MultiIndex n)
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) φ =
    hessianOperator i j (fun x => φ x) 0 := by
  rw [fundamental_hessian_pairing hn, gradient_pairing_of_test_zero hn i j φ hφ,
    neg_neg, pv_pairing_of_test_zero hn i j φ hφ]

lemma fundamental_hessian_radialCutoff {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    distributionDerivative ({i, j} : MultiIndex n)
      (regularDistribution (⊤ : Domain n) (fundamentalKernel n)) (radialCutoff n) =
      -(kronecker i j / (n : ℝ)) := by
  rw [fundamental_hessian_pairing hn, radialCutoff_gradient_pairing hn]

end P201.Elliptic.NewtonHessianContact

namespace P201.Elliptic.NewtonHessian
open P201Specs P201Specs.Elliptic.NewtonHessian
open P201.Elliptic.NewtonHessianContact

theorem distributionIdentity : distributionIdentityStatement := by
  intro n hn i j
  let S := distributionDerivative ({i, j} : MultiIndex n)
    (regularDistribution (⊤ : Domain n) (fundamentalKernel n))
  let c := kronecker i j / (n : ℝ)
  have hPair (φ : Test ℝ (⊤ : Domain n)) :
      S φ = hessianOperator i j (fun x => φ x) 0 - c * φ 0 := by
    let ψ := φ - φ 0 • radialCutoff n
    have hψ0 : ψ 0 = 0 := by simp [ψ, radialCutoff_zero]
    have hz := fundamental_hessian_pv_of_test_zero hn i j ψ hψ0
    rw [hessianOperator_test_sub_smul hn i j φ (radialCutoff n) (φ 0),
      radialCutoff_pv_zero hn i j, mul_zero, sub_zero] at hz
    change S (φ - φ 0 • radialCutoff n) = _ at hz
    rw [map_sub, map_smul, fundamental_hessian_radialCutoff hn] at hz
    simp only [smul_eq_mul] at hz
    change S φ - φ 0 * (-c) = _ at hz
    linarith
  let T := S + c • originDirac n
  refine ⟨T, ?_, ?_⟩
  · intro φ
    obtain ⟨hi, ht⟩ := truncatedPairing_limit hn i j φ
    refine ⟨hi, ?_⟩
    have hT : T φ = hessianOperator i j (fun x => φ x) 0 := by
      change S φ + c * φ 0 = _
      rw [hPair]
      ring
    rw [hT]
    exact ht
  · change S = (S + c • originDirac n) - c • originDirac n
    abel
end P201.Elliptic.NewtonHessian


namespace P201.Elliptic.NewtonHessian
open P201Specs.Elliptic.NewtonHessian

/-- The actual Newton integral gains two Hölder derivatives, with the negative contact term. -/
theorem potentialHessian : potentialHessianStatement := by
  apply potentialHessian_of_distribution_density
  intro n hn α hα hα1 F hc hF i j
  exact potential_distribution_hessian_of_identity distributionIdentity hn α hα hα1 F hc hF i j

/-- Full local ordinary C²,α bounds in every positive dimension. -/
theorem potentialEstimate : potentialEstimateStatement :=
  potentialEstimate_of_hessian potentialHessian

end P201.Elliptic.NewtonHessian
