import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.Deriv.Inv
import MathGenome.Internal.LinearPDE.P201Specs.Potential.BallPoisson
import MathGenome.Internal.LinearPDE.P201.Potential.MeanValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace P201.BallPoisson

abbrev kernel : P201Specs.BallPoisson.KernelType := @P201Specs.BallPoisson.kernel
abbrev boundaryValue : P201Specs.BallPoisson.BoundaryValueType :=
  @P201Specs.BallPoisson.boundaryValue
abbrev poissonIntegral : P201Specs.BallPoisson.PoissonIntegralType :=
  @P201Specs.BallPoisson.poissonIntegral
abbrev poissonExtension : P201Specs.BallPoisson.PoissonIntegralType :=
  @P201Specs.BallPoisson.poissonExtension

/-- The singularity of the kernel never meets its interior evaluation point. -/
theorem interior_ne_boundary {n : ℕ} {a x ζ : Space n} {r : ℝ}
    (hx : x ∈ ball a r) (hζ : ζ ∈ sphere a r) : x ≠ ζ := by
  intro h
  subst x
  have hlt := mem_ball.mp hx
  have heq := mem_sphere.mp hζ
  linarith

theorem kernel_positive : P201Specs.BallPoisson.KernelPositiveStatement := by
  intro n hn a r hr x hx ζ hζ
  have hxa : ‖x - a‖ < r := by simpa [mem_ball, dist_eq_norm] using hx
  have hnum : 0 < r ^ 2 - ‖x - a‖ ^ 2 := by
    nlinarith [norm_nonneg (x - a)]
  have hden : 0 < r * omega n * ‖x - ζ‖ ^ n :=
    mul_pos (mul_pos hr (MeanValues.omega_pos (by omega)))
      (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (interior_ne_boundary hx hζ))) n)
  exact div_pos hnum hden

/-- Surface measure on a positive-radius sphere is carried by that sphere. -/
theorem sphereSurface_ae_mem {n : ℕ} (a : Space n) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ζ ∂sphereSurface a r, ζ ∈ sphere a r := by
  apply Measure.ae_smul_measure (c := ENNReal.ofReal (r ^ (n - 1)))
  apply (MeasureTheory.ae_map_iff (by fun_prop) isClosed_sphere.measurableSet).mpr
  filter_upwards [MeanValues.unitSurface_ae_mem n] with θ hθ
  have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
  simp [mem_sphere, dist_eq_norm, norm_smul, hθn, abs_of_pos hr]

/-- A continuous function on the sphere is integrable for the shared surface measure. -/
theorem sphereSurface_integrable_of_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {a : Space n} {r : ℝ} (hr : 0 < r) {f : Space n → 𝕜}
    (hf : ContinuousOn f (sphere a r)) : Integrable f (sphereSurface a r) := by
  have hi := hf.integrableOn_compact (μ := sphereSurface a r) (isCompact_sphere a r)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (sphereSurface_ae_mem a hr)] at hi

/-- The boundary datum representative agrees with the original continuous map. -/
@[simp] theorem boundaryValue_coe {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ) (g : C(sphere a r, 𝕜)) (ζ : sphere a r) :
    boundaryValue a r g ζ = g ζ := by
  exact dite_eq_left ζ.property

theorem boundaryValue_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ) (g : C(sphere a r, 𝕜)) :
    ContinuousOn (boundaryValue a r g) (sphere a r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (sphere a r).domRestrict (boundaryValue a r g) = g := by
    funext ζ
    exact boundaryValue_coe a r g ζ
  rw [he]
  exact g.continuous

/-- The denominator stays nonzero throughout the integration sphere. -/
theorem kernel_continuousOn_boundary {n : ℕ} (hn : 1 ≤ n) {a x : Space n} {r : ℝ}
    (hx : x ∈ ball a r) : ContinuousOn (kernel a r x) (sphere a r) := by
  apply continuousOn_const.div
    ((continuousOn_const.mul continuousOn_const).mul
      ((continuousOn_const.sub continuousOn_id).norm.pow n))
  intro ζ hζ
  have hr : r ≠ 0 := ne_of_gt (lt_of_le_of_lt dist_nonneg (mem_ball.mp hx))
  exact mul_ne_zero (mul_ne_zero hr (ne_of_gt (MeanValues.omega_pos hn)))
      (pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (interior_ne_boundary hx hζ))))

/-- In the dimensions used in the theorem the kernel has a genuine Bochner integral. -/
theorem kernel_integrable {n : ℕ} (hn : 2 ≤ n) {a x : Space n} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ ball a r) : Integrable (kernel a r x) (sphereSurface a r) :=
  sphereSurface_integrable_of_continuousOn hr (kernel_continuousOn_boundary (by omega) hx)

/-- Products with arbitrary continuous real or complex boundary data are integrable. -/
theorem poisson_integrand_integrable {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {a x : Space n} {r : ℝ} (hr : 0 < r) (hx : x ∈ ball a r)
    (g : C(sphere a r, 𝕜)) : Integrable
      (fun ζ => kernel a r x ζ • boundaryValue a r g ζ) (sphereSurface a r) :=
  sphereSurface_integrable_of_continuousOn hr
    ((kernel_continuousOn_boundary (by omega) hx).smul (boundaryValue_continuousOn a r g))

/-- The exact value at the center, before surface integration. -/
theorem kernel_center {n : ℕ} (hn : 2 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {ζ : Space n} (hζ : ζ ∈ sphere a r) :
    kernel a r a ζ = (omega n * r ^ (n - 1))⁻¹ := by
  have hz : ‖a - ζ‖ = r := by
    simpa [mem_sphere, dist_eq_norm, norm_sub_rev] using hζ
  have hw : omega n ≠ 0 := (MeanValues.omega_pos (by omega)).ne'
  have hp : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [kernel, P201Specs.BallPoisson.kernel, sub_self, norm_zero, zero_pow
    (by decide : (2 : ℕ) ≠ 0), sub_zero, hz]
  rw [hp]
  field_simp

/-- Unit mass at the center with the source's exact dimension-dependent constant. -/
theorem kernel_mass_center {n : ℕ} (hn : 2 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) : (∫ ζ, kernel a r a ζ ∂sphereSurface a r) = 1 := by
  have he : (fun ζ => kernel a r a ζ) =ᵐ[sphereSurface a r]
      (fun _ => (omega n * r ^ (n - 1))⁻¹) := by
    filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
    exact kernel_center hn a hr hζ
  rw [integral_congr_ae he, integral_const]
  change (sphereSurface a r).real univ * (omega n * r ^ (n - 1))⁻¹ = 1
  rw [P201.sphereSurfaceMass a r hr.le]
  exact mul_inv_cancel₀ (mul_ne_zero (MeanValues.omega_pos (by omega)).ne'
    (pow_ne_zero _ hr.ne'))

/-- The kernel is smooth away from its pole, including across the sphere at
all other points. This statement does not assume harmonicity. -/
theorem kernel_contDiffAt {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {x ζ : Space n} (hne : x ≠ ζ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => kernel a r y ζ) x := by
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space n => ‖y - ζ‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hne)
  exact (contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)).div
    (contDiffAt_const.mul (hnorm.pow n))
    (mul_ne_zero (mul_ne_zero hr.ne' (MeanValues.omega_pos hn).ne')
      (pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))))

theorem kernel_contDiffOn {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {ζ : Space n} (hζ : ζ ∈ sphere a r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => kernel a r x ζ) (ball a r) :=
  fun _ hx => (kernel_contDiffAt hn a hr (interior_ne_boundary hx hζ)).contDiffWithinAt

/-- At a boundary point different from the pole, the kernel vanishes continuously. -/
theorem kernel_limit_off_diagonal {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {η ζ : Space n} (hη : η ∈ sphere a r) (hne : η ≠ ζ) :
    Tendsto (fun x => kernel a r x ζ) (𝓝 η) (𝓝 0) := by
  have hc := (kernel_contDiffAt hn a hr hne).continuousAt
  have hηn : ‖η - a‖ = r := by simpa [mem_sphere, dist_eq_norm] using hη
  have hz : kernel a r η ζ = 0 := by simp [kernel, P201Specs.BallPoisson.kernel, hηn]
  exact hz ▸ hc.tendsto

/-- The specified extension has exactly the prescribed boundary trace. -/
@[simp] theorem poissonExtension_boundary {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ) (g : C(sphere a r, 𝕜)) (ζ : sphere a r) :
    poissonExtension a r g ζ = g ζ := by
  classical
  have hnot : (ζ : Space n) ∉ ball a r := by
    intro h
    have he := mem_sphere.mp ζ.property
    have hl := mem_ball.mp h
    linarith
  change (if (ζ : Space n) ∈ ball a r then _ else _) = _
  rw [ite_eq_right hnot]
  exact boundaryValue_coe a r g ζ

theorem poissonExtension_interior {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ) (g : C(sphere a r, 𝕜)) {x : Space n}
    (hx : x ∈ ball a r) : poissonExtension a r g x = poissonIntegral a r g x :=
  ite_eq_left hx

/-- The value at the center is exactly the normalized surface average. -/
theorem poissonIntegral_center {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) {r : ℝ} (hr : 0 < r) (g : C(sphere a r, 𝕜)) :
    poissonIntegral a r g a = sphereAverage (boundaryValue a r g) a r := by
  change (∫ ζ, kernel a r a ζ • boundaryValue a r g ζ ∂sphereSurface a r) = _
  calc
    _ = ∫ ζ, (omega n * r ^ (n - 1))⁻¹ • boundaryValue a r g ζ ∂sphereSurface a r := by
      apply integral_congr_ae
      filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
      rw [kernel_center hn a hr hζ]
    _ = (omega n * r ^ (n - 1))⁻¹ •
        ∫ ζ, boundaryValue a r g ζ ∂sphereSurface a r := integral_smul _ _
    _ = _ := by rw [sphereAverage, P201Specs.sphereAverage, P201.sphereSurfaceMass a r hr.le]

/-- Uniform control away from a cap. It applies to every interior approach,
without any restriction to radial or nontangential approaches. -/
theorem kernel_le_off_cap {n : ℕ} (hn : 2 ≤ n) {a x η ζ : Space n} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (_hx : x ∈ ball a r) (_hζ : ζ ∈ sphere a r)
    (hnear : dist x η < δ / 2) (hfar : δ ≤ dist ζ η) :
    kernel a r x ζ ≤ r ^ 2 / (r * omega n * (δ / 2) ^ n) := by
  have hsep : δ / 2 ≤ ‖x - ζ‖ := by
    have ht := dist_triangle ζ x η
    rw [dist_comm ζ x, dist_eq_norm x ζ] at ht
    linarith
  have hω : 0 < omega n := MeanValues.omega_pos (by omega)
  have hden : 0 < r * omega n * (δ / 2) ^ n := by positivity
  have hpow : (δ / 2) ^ n ≤ ‖x - ζ‖ ^ n := pow_le_pow_left₀ (by positivity) hsep n
  exact div_le_div₀ (sq_nonneg r) (by nlinarith [sq_nonneg ‖x - a‖]) hden
    (mul_le_mul_of_nonneg_left hpow (mul_pos hr hω).le)

/-- The total kernel mass outside any fixed boundary cap tends to zero.
This is the approximate-identity property needed for continuous data. -/
theorem kernel_mass_off_cap_tendsto {n : ℕ} (hn : 2 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {η : Space n} (hη : η ∈ sphere a r) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x => ∫ ζ in {ζ : Space n | δ ≤ dist ζ η}, kernel a r x ζ
      ∂sphereSurface a r) (𝓝[ball a r] η) (𝓝 0) := by
  let S : Set (Space n) := {ζ | δ ≤ dist ζ η}
  have hS : MeasurableSet S := isClosed_le continuous_const (by fun_prop) |>.measurableSet
  have hint : ∀ᶠ x in 𝓝[ball a r] η, AEStronglyMeasurable (kernel a r x)
      ((sphereSurface a r).restrict S) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (kernel_integrable hn hr hx).aestronglyMeasurable.restrict
  have hbound : ∀ᶠ x in 𝓝[ball a r] η, ∀ᵐ ζ ∂(sphereSurface a r).restrict S,
      ‖kernel a r x ζ‖ ≤ r ^ 2 / (r * omega n * (δ / 2) ^ n) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds η (half_pos hδ))] with x hx hnear
    filter_upwards [ae_restrict_of_ae (sphereSurface_ae_mem a hr), ae_restrict_mem hS]
      with ζ hζ hfar
    rw [Real.norm_eq_abs, abs_of_pos (kernel_positive hn a r hr x hx ζ hζ)]
    exact kernel_le_off_cap hn hr hδ hx hζ (mem_ball.mp hnear) hfar
  have hlim : ∀ᵐ ζ ∂(sphereSurface a r).restrict S,
      Tendsto (fun x => kernel a r x ζ) (𝓝[ball a r] η) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem hS] with ζ hζ
    have hne : η ≠ ζ := by
      intro he
      have : δ ≤ 0 := by simpa [S, he] using hζ
      linarith
    exact (kernel_limit_off_diagonal (by omega) a hr hη hne).mono_left nhdsWithin_le_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Space n => r ^ 2 / (r * omega n * (δ / 2) ^ n)) hint hbound
    (integrable_const _) hlim
  simpa only [integral_zero] using ht

open scoped RealInnerProductSpace

/-- Derivative of an inverse distance power away from its pole. -/
theorem norm_inv_pow_hasFDerivAt {n : ℕ} (ζ x : Space n) (k : ℕ) (hne : x ≠ ζ) :
    HasFDerivAt (fun y : Space n => (‖y - ζ‖ ^ k)⁻¹)
      ((-(k : ℝ) / ‖x - ζ‖ ^ (k + 2)) • innerSL ℝ (x - ζ)) x := by
  have hnorm : ‖x - ζ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hd₀ := ((hasFDerivAt_id x).sub_const ζ).norm_sq.sqrt (pow_ne_zero 2 hnorm)
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at hd₀
  have hd := hd₀.pow k
  have hi := (hasFDerivAt_inv (pow_ne_zero k hnorm)).comp x hd
  convert! hi using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.toSpanSingleton_apply,
    id_eq, smul_eq_mul, nsmul_eq_mul]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ, pow_add]
    field_simp [hnorm]
    <;> ring <;> simp

/-- An explicit first derivative, used below to compute the coordinate Laplacian. -/
theorem kernel_fderiv_apply {n : ℕ} (a : Space n) (r : ℝ) {x ζ : Space n}
    (hne : x ≠ ζ) (v : Space n) :
    fderiv ℝ (fun y => kernel a r y ζ) x v =
      (r * omega n)⁻¹ *
        (-2 * inner ℝ (x - a) v * (‖x - ζ‖ ^ n)⁻¹ -
          (r ^ 2 - ‖x - a‖ ^ 2) * (n : ℝ) * inner ℝ (x - ζ) v *
            (‖x - ζ‖ ^ (n + 2))⁻¹) := by
  have hnum := (((hasFDerivAt_id x).sub_const a).norm_sq).const_sub (r ^ 2)
  have hprod := hnum.mul (norm_inv_pow_hasFDerivAt ζ x n hne)
  have hd := hprod.const_mul ((r * omega n)⁻¹)
  have he : (fun y : Space n => kernel a r y ζ) =
      fun y => (r * omega n)⁻¹ * ((r ^ 2 - ‖y - a‖ ^ 2) * (‖y - ζ‖ ^ n)⁻¹) := by
    funext y
    simp only [kernel, P201Specs.BallPoisson.kernel, div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [Pi.mul_apply, id_eq] at hd
  rw [he, hd.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  <;> ring <;> simp

private theorem inner_sub_hasFDerivAt {n : ℕ} (a x v : Space n) :
    HasFDerivAt (fun y => inner ℝ (y - a) v) (innerSL ℝ v) x := by
  have h := (innerSL ℝ v).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id,
    innerSL_apply_apply, real_inner_comm] using h

/-- Second directional derivative, before tracing over an orthonormal basis. -/
theorem kernel_second_fderiv_apply {n : ℕ} (a : Space n) (r : ℝ) {x ζ : Space n}
    (hne : x ≠ ζ) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => kernel a r z ζ) y v) x v =
      (r * omega n)⁻¹ *
        (-2 * ‖v‖ ^ 2 * (‖x - ζ‖ ^ n)⁻¹ +
          4 * (n : ℝ) * inner ℝ (x - a) v * inner ℝ (x - ζ) v *
            (‖x - ζ‖ ^ (n + 2))⁻¹ -
          (n : ℝ) * (r ^ 2 - ‖x - a‖ ^ 2) * ‖v‖ ^ 2 *
            (‖x - ζ‖ ^ (n + 2))⁻¹ +
          (n : ℝ) * (n + 2 : ℕ) * (r ^ 2 - ‖x - a‖ ^ 2) *
            (inner ℝ (x - ζ) v) ^ 2 * (‖x - ζ‖ ^ (n + 4))⁻¹) := by
  have hnum := (((hasFDerivAt_id x).sub_const a).norm_sq).const_sub (r ^ 2)
  have h₁ := (inner_sub_hasFDerivAt a x v).const_mul (-2 : ℝ)
  have h₂ := h₁.mul (norm_inv_pow_hasFDerivAt ζ x n hne)
  have h₃ := ((hnum.mul_const (n : ℝ)).mul (inner_sub_hasFDerivAt ζ x v)).mul
    (norm_inv_pow_hasFDerivAt ζ x (n + 2) hne)
  have hd := (h₂.sub h₃).const_mul ((r * omega n)⁻¹)
  have he : (fun y => fderiv ℝ (fun z => kernel a r z ζ) y v) =ᶠ[𝓝 x]
      (fun y => (r * omega n)⁻¹ *
        (-2 * inner ℝ (y - a) v * (‖y - ζ‖ ^ n)⁻¹ -
          (r ^ 2 - ‖y - a‖ ^ 2) * (n : ℝ) * inner ℝ (y - ζ) v *
            (‖y - ζ‖ ^ (n + 2))⁻¹)) := by
    filter_upwards [eventually_ne_nhds hne] with y hy
    exact kernel_fderiv_apply a r hy v
  rw [he.fderiv_eq]
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq] at hd
  rw [hd.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left, inner_self_eq_norm_sq,
    show n + 2 + 2 = n + 4 by omega]
  <;> ring <;> simp

private theorem kernel_iteratedFDeriv_two {n : ℕ} (hn : 1 ≤ n) (a : Space n)
    {r : ℝ} (hr : 0 < r) {x ζ : Space n} (hne : x ≠ ζ) (v : Space n) :
    iteratedFDeriv ℝ 2 (fun y => kernel a r y ζ) x ![v, v] =
      fderiv ℝ (fun y => fderiv ℝ (fun z => kernel a r z ζ) y v) x v := by
  have hc : ContDiffAt ℝ 2 (fun y => kernel a r y ζ) x :=
    (kernel_contDiffAt hn a hr hne).of_le (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => kernel a r y ζ)) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- The trace of the second derivative gives the source's Laplacian formula. -/
theorem kernel_laplacian {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) {x ζ : Space n} (hne : x ≠ ζ) :
    laplacian (fun y => kernel a r y ζ) x =
      (r * omega n)⁻¹ * (2 * n : ℝ) * (‖x - ζ‖ ^ (n + 2))⁻¹ *
        (r ^ 2 - ‖x - a‖ ^ 2 + 2 * inner ℝ (x - a) (x - ζ) - ‖x - ζ‖ ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hs (u v : Space n) :
      (∑ i : Fin n, inner ℝ u (b i) * inner ℝ v (b i)) = inner ℝ u v := by
    simpa only [real_inner_comm] using b.sum_inner_mul_inner u v
  have hsq (u : Space n) :
      (∑ i : Fin n, (inner ℝ u (b i)) ^ 2) = ‖u‖ ^ 2 := by
    simpa only [pow_two, real_inner_self_eq_norm_sq] using hs u u
  have hc : ContDiffAt ℝ 2 (fun y => kernel a r y ζ) x :=
    (kernel_contDiffAt hn a hr hne).of_le (by simp)
  change P201Specs.laplacian (fun y => kernel a r y ζ) x = _
  rw [MeanValues.laplacian_bridge _ _ hc,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp_rw [kernel_iteratedFDeriv_two hn a hr hne, kernel_second_fderiv_apply a r hne]
  simp only [b.orthonormal.norm_eq_one, one_pow, mul_one, Nat.cast_add, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_assoc (4 * n : ℝ) (inner ℝ (x - a) _) (inner ℝ (x - ζ) _)]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hs, hsq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : ‖x - ζ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  simp only [pow_add]
  field_simp [hd]
  <;> ring

/-- Harmonicity follows from the exact cancellation, in particular also for n=2. -/
theorem kernel_harmonic : P201Specs.BallPoisson.KernelHarmonicStatement := by
  intro n hn a r hr ζ hζ
  refine ⟨(kernel_contDiffOn (by omega) a hr hζ).of_le (by simp), ?_⟩
  intro x hx
  change laplacian (fun y => kernel a r y ζ) x = 0
  rw [kernel_laplacian (by omega) a hr (interior_ne_boundary hx hζ)]
  have hζn : ‖ζ - a‖ = r := by simpa [mem_sphere, dist_eq_norm] using hζ
  have he : (x - a) - (x - ζ) = ζ - a := by abel
  have hi := norm_sub_sq_real (x - a) (x - ζ)
  rw [he, hζn] at hi
  have hz : r ^ 2 - ‖x - a‖ ^ 2 + 2 * inner ℝ (x - a) (x - ζ) - ‖x - ζ‖ ^ 2 = 0 := by
    linarith
  rw [hz, mul_zero]

/-- Symmetry of the two distances appearing in the normalization argument. -/
theorem poisson_distance_symmetry {n : ℕ} {u θ : Space n} {r : ℝ}
    (hu : u ≠ 0) (hθ : ‖θ‖ = 1) (hr : 0 < r) :
    ‖u - r • θ‖ = ‖‖u‖ • θ - (r / ‖u‖) • u‖ := by
  have ht : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he : ‖u - r • θ‖ ^ 2 = ‖‖u‖ • θ - (r / ‖u‖) • u‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_pos ht, abs_of_pos (div_pos hr ht), hθ, mul_one,
      inner_smul_left, inner_smul_right, real_inner_comm θ u,
      starRingEnd_apply, star_trivial]
    field_simp
    <;> ring
  nlinarith [norm_nonneg (u - r • θ), norm_nonneg (‖u‖ • θ - (r / ‖u‖) • u)]

/-- Unit mass is obtained from kernel harmonicity and the mean identity.
The distance symmetry avoids any assumed rotational-invariance bridge. -/
theorem kernel_mass : P201Specs.BallPoisson.KernelMassStatement := by
  intro n hn a r hr x hx
  refine ⟨kernel_integrable hn hr hx, ?_⟩
  by_cases hxa : x = a
  · subst x
    exact kernel_mass_center hn a hr
  let t : ℝ := ‖x - a‖
  have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have htr : t < r := by simpa [t, mem_ball, dist_eq_norm] using hx
  let η : Space n := a + (r / t) • (x - a)
  have hη : η ∈ sphere a r := by
    simp only [η, mem_sphere, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr ht)]
    dsimp [t]
    exact div_mul_cancel₀ r ht.ne'
  have hsym (θ : Space n) (hθ : θ ∈ sphere (0 : Space n) 1) :
      kernel a r x (a + r • θ) = kernel a r (a + t • θ) η := by
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    have hd : ‖x - (a + r • θ)‖ = ‖(a + t • θ) - η‖ := by
      have h₁ : x - (a + r • θ) = (x - a) - r • θ := by abel
      have h₂ : (a + t • θ) - η = t • θ - (r / t) • (x - a) := by dsimp [η]; abel
      rw [h₁, h₂]
      exact poisson_distance_symmetry (sub_ne_zero.mpr hxa) hθn hr
    have hnorm : ‖a + t • θ - a‖ = t := by
      simp [norm_smul, hθn, abs_of_pos ht]
    simp only [kernel, P201Specs.BallPoisson.kernel, hd, hnorm]
    rfl
  have hball : closedBall a t ⊆ ball a r := closedBall_subset_ball htr
  have hmean := (MeanValues.mean_values (by omega) ⟨ball a r, isOpen_ball⟩
    (fun y => kernel a r y η) (kernel_harmonic hn a r hr η hη) a t ht hball).1
  rw [MeanValues.sphere_mean_normalization (by omega) _ a t ht] at hmean
  change kernel a r a η = (omega n)⁻¹ *
    (∫ θ, kernel a r (a + t • θ) η ∂unitSurface n) at hmean
  have hcoord : Topology.IsClosedEmbedding (fun θ : Space n => a + r • θ) :=
    ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft a)).isClosedEmbedding
  change (∫ ζ, kernel a r x ζ ∂P201Specs.sphereSurface a r) = 1
  simp only [P201Specs.sphereSurface, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rw [hcoord.integral_map]
  have heq : (fun θ => kernel a r x (a + r • θ)) =ᵐ[unitSurface n]
      (fun θ => kernel a r (a + t • θ) η) := by
    filter_upwards [MeanValues.unitSurface_ae_mem n] with θ hθ
    exact hsym θ hθ
  rw [integral_congr_ae heq]
  have hw : omega n ≠ 0 := (MeanValues.omega_pos (by omega)).ne'
  rw [kernel_center hn a hr hη] at hmean
  change r ^ (n - 1) * (∫ θ, kernel a r (a + t • θ) η ∂unitSurface n) = 1
  have he := congrArg (fun z : ℝ => omega n * z) hmean
  simp only [← mul_assoc, mul_inv_cancel₀ hw, one_mul] at he
  rw [← he]
  field_simp

/-- Compact-surface integration preserves continuity in an open parameter domain. -/
theorem surface_integral_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (a : Space n) {r : ℝ} (hr : 0 < r)
    (f : Space n → Space n → 𝕜)
    (hf : ContinuousOn (Function.uncurry f) ((Ω : Set _) ×ˢ sphere a r)) :
    ContinuousOn (fun x => ∫ ζ, f x ζ ∂sphereSurface a r) Ω := by
  intro x hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hx)
  have hKΩ : closedBall x (ε / 2) ⊆ (Ω : Set _) :=
    (closedBall_subset_ball (by linarith)).trans hεΩ
  have hcompact := (isCompact_closedBall x (ε / 2)).prod (isCompact_sphere a r)
  have hc := hf.mono (Set.prod_mono hKΩ Subset.rfl)
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hc.norm
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [Metric.ball_mem_nhds x (half_pos hε)] with y hy
    exact (sphereSurface_integrable_of_continuousOn hr
      (hf.comp (continuousOn_const.prodMk continuousOn_id)
        (fun ζ hζ => ⟨hKΩ (ball_subset_closedBall hy), hζ⟩))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x (half_pos hε)] with y hy
    filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
    exact hC (mem_image_of_mem _ (show (y, ζ) ∈ closedBall x (ε / 2) ×ˢ sphere a r from
      ⟨ball_subset_closedBall hy, hζ⟩))
  · exact integrable_const C
  · filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
    exact (hf.comp (continuousOn_id.prodMk continuousOn_const)
      (fun y hy => ⟨hy, hζ⟩)).continuousAt (Ω.isOpen.mem_nhds hx)

/-- Fubini and the mean-value converse allow harmonicity to pass under a
compact surface integral without imposing regularity on the boundary datum. -/
theorem surface_integral_harmonic {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (a : Space n) {r : ℝ} (hr : 0 < r)
    (f : Space n → Space n → 𝕜)
    (hf : ContinuousOn (Function.uncurry f) ((Ω : Set _) ×ˢ sphere a r))
    (hh : ∀ ζ ∈ sphere a r, MeanValues.IsHarmonic Ω (fun y => f y ζ)) :
    MeanValues.IsHarmonic Ω (fun x => ∫ ζ, f x ζ ∂sphereSurface a r) := by
  apply (MeanValues.ball_converse hn Ω _ (surface_integral_continuousOn Ω a hr f hf) ?_).2
  intro b s hs hball
  have hcompact := (isCompact_closedBall b s).prod (isCompact_sphere a r)
  have hc := hf.mono (Set.prod_mono hball Subset.rfl)
  have hi := hc.integrableOn_compact
    (μ := (volume.restrict (ball b s)).prod (sphereSurface a r)) hcompact
  have hsupport : ∀ᵐ p ∂(volume.restrict (ball b s)).prod (sphereSurface a r),
      p ∈ closedBall b s ×ˢ sphere a r := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (isClosed_closedBall.measurableSet.prod isClosed_sphere.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
    exact ⟨ball_subset_closedBall hy, hζ⟩
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsupport] at hi
  change (∫ ζ, f b ζ ∂sphereSurface a r) =
    (volume.real (ball b s))⁻¹ • ∫ y in ball b s, ∫ ζ, f y ζ ∂sphereSurface a r
  rw [integral_integral_swap hi, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
  exact (MeanValues.mean_values hn Ω _ (hh ζ hζ) b s hs hball).2

/-- Joint continuity on the interior times the integration sphere. -/
theorem kernel_joint_continuousOn {n : ℕ} (hn : 1 ≤ n) (a : Space n) {r : ℝ}
    (hr : 0 < r) : ContinuousOn
      (fun p : Space n × Space n => kernel a r p.1 p.2) (ball a r ×ˢ sphere a r) := by
  apply (continuousOn_const.sub
    ((continuousOn_fst.sub continuousOn_const).norm.pow 2)).div
    ((continuousOn_const.mul continuousOn_const).mul
      ((continuousOn_fst.sub continuousOn_snd).norm.pow n))
  intro p hp
  exact mul_ne_zero (mul_ne_zero hr.ne' (MeanValues.omega_pos hn).ne')
    (pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (interior_ne_boundary hp.1 hp.2))))

theorem poisson_harmonic : P201Specs.BallPoisson.PoissonHarmonicStatement := by
  intro n hn 𝕜 _ a r hr g
  refine ⟨fun x hx => poisson_integrand_integrable hn hr hx g, ?_⟩
  apply surface_integral_harmonic (by omega) ⟨ball a r, isOpen_ball⟩ a hr
    (fun x ζ => kernel a r x ζ • boundaryValue a r g ζ)
  · exact (kernel_joint_continuousOn (by omega) a hr).smul
      ((boundaryValue_continuousOn a r g).comp continuousOn_snd (fun _ hp => hp.2))
  · intro ζ hζ
    apply (MeanValues.harmonic_bridge _ _).mpr
    exact ((MeanValues.harmonic_bridge _ _).mp (kernel_harmonic hn a r hr ζ hζ)).comp_CLM
      (ContinuousLinearMap.toSpanSingleton ℝ (boundaryValue a r g ζ))

/-- Error estimate separating a small boundary cap from its complement. -/
theorem poisson_error_bound {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) {r : ℝ} (hr : 0 < r) (g : C(sphere a r, 𝕜))
    (η : sphere a r) {δ ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hsmall : ∀ ζ ∈ sphere a r, dist ζ η < δ → ‖boundaryValue a r g ζ - g η‖ ≤ ε)
    (hbound : ∀ ζ ∈ sphere a r, ‖boundaryValue a r g ζ - g η‖ ≤ C)
    {x : Space n} (hx : x ∈ ball a r) :
    ‖poissonIntegral a r g x - g η‖ ≤ ε + C *
      ∫ ζ in {ζ : Space n | δ ≤ dist ζ η}, kernel a r x ζ ∂sphereSurface a r := by
  classical
  let S : Set (Space n) := {ζ | δ ≤ dist ζ η}
  have hS : MeasurableSet S := isClosed_le continuous_const (by fun_prop) |>.measurableSet
  have hk := kernel_integrable hn hr hx
  have herr : poissonIntegral a r g x - g η =
      ∫ ζ, kernel a r x ζ • (boundaryValue a r g ζ - g η) ∂sphereSurface a r := by
    simp_rw [smul_sub]
    rw [integral_sub (poisson_integrand_integrable hn hr hx g) (hk.smul_const (g η)),
      integral_smul_const, (kernel_mass hn a r hr x hx).2, one_smul]
    rfl
  rw [herr]
  calc
    _ ≤ ∫ ζ, ε * kernel a r x ζ + C * S.indicator (kernel a r x) ζ ∂sphereSurface a r := by
      apply norm_integral_le_of_norm_le ((hk.const_mul ε).add ((hk.indicator hS).const_mul C))
      filter_upwards [sphereSurface_ae_mem a hr] with ζ hζ
      have hpos := (kernel_positive hn a r hr x hx ζ hζ).le
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
      simp only [Pi.add_apply]
      by_cases hfar : ζ ∈ S
      · rw [Set.indicator_of_mem hfar]
        nlinarith [mul_le_mul_of_nonneg_left (hbound ζ hζ) hpos]
      · rw [Set.indicator_of_notMem hfar, mul_zero, add_zero]
        exact (mul_le_mul_of_nonneg_left (hsmall ζ hζ (lt_of_not_ge hfar)) hpos).trans_eq
          (mul_comm _ _)
    _ = _ := by
      rw [integral_add (hk.const_mul ε) ((hk.indicator hS).const_mul C),
        integral_const_mul, integral_const_mul, integral_indicator hS,
        (kernel_mass hn a r hr x hx).2, mul_one]

theorem boundary_limit : P201Specs.BallPoisson.BoundaryLimitStatement := by
  intro n hn 𝕜 _ a r hr g η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc := (boundaryValue_continuousOn a r g).continuousWithinAt η.property
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hsmall⟩ := hc (ε / 2) (half_pos hε)
  have hgη : boundaryValue a r g η = g η := boundaryValue_coe a r g η
  obtain ⟨M, hM⟩ := (isCompact_sphere a r).bddAbove_image
    ((boundaryValue_continuousOn a r g).sub continuousOn_const).norm
  let C : ℝ := max M 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hbound : ∀ ζ ∈ sphere a r, ‖boundaryValue a r g ζ - g η‖ ≤ C := by
    intro ζ hζ
    exact (hM (mem_image_of_mem _ hζ)).trans (le_max_left _ _)
  have ht := (kernel_mass_off_cap_tendsto hn a hr η.property hδ).const_mul C
  have hevent : ∀ᶠ x in 𝓝[ball a r] (η : Space n),
      C * (∫ ζ in {ζ : Space n | δ ≤ dist ζ η}, kernel a r x ζ ∂sphereSurface a r) < ε / 2 := by
    exact (tendsto_order.mp (by simpa using ht)).2 _ (half_pos hε)
  filter_upwards [self_mem_nhdsWithin, hevent] with x hx he
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (poisson_error_bound hn a hr g η (δ := δ) (half_pos hε).le hC.le ?_ hbound hx)
  · linarith
  · intro ζ hζ hdist
    have hh := hsmall hζ hdist
    simpa only [hgη, dist_eq_norm] using hh.le

theorem continuous_extension : P201Specs.BallPoisson.ContinuousExtensionStatement := by
  intro n hn 𝕜 _ a r hr g
  refine ⟨?_, poissonExtension_boundary a r g⟩
  intro x hx
  by_cases hxi : x ∈ ball a r
  · have hc := (poisson_harmonic hn a r hr g).2.1.continuousOn.continuousAt
      (isOpen_ball.mem_nhds hxi)
    apply ContinuousAt.continuousWithinAt
    apply hc.congr
    filter_upwards [isOpen_ball.mem_nhds hxi] with y hy
    exact (poissonExtension_interior a r g hy).symm
  · have hxs : x ∈ sphere a r := by
      rw [mem_sphere]
      exact le_antisymm (mem_closedBall.mp hx) (le_of_not_gt hxi)
    let η : sphere a r := ⟨x, hxs⟩
    have htrace : poissonExtension a r g x = g η := poissonExtension_boundary a r g η
    have hball : ContinuousWithinAt (poissonExtension a r g) (ball a r) x := by
      rw [ContinuousWithinAt, htrace]
      apply (boundary_limit hn a r hr g η).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (poissonExtension_interior a r g hy).symm
    have hsphere : ContinuousWithinAt (poissonExtension a r g) (sphere a r) x := by
      apply ((boundaryValue_continuousOn a r g) x hxs).congr
      · intro y hy
        exact (poissonExtension_boundary a r g ⟨y, hy⟩).trans
          (boundaryValue_coe a r g ⟨y, hy⟩).symm
      · exact htrace.trans (boundaryValue_coe a r g η).symm
    simpa only [ball_union_sphere] using hball.union hsphere

/-- The specified extension agrees locally with the harmonic integral at every
interior point, so it has the same harmonicity there. -/
theorem poissonExtension_harmonic {n : ℕ} (hn : 2 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) {r : ℝ} (hr : 0 < r) (g : C(sphere a r, 𝕜)) :
    MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (poissonExtension a r g) := by
  apply (MeanValues.harmonic_bridge _ _).mpr
  intro x hx
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₁ := poissonIntegral a r g)
    (f₂ := poissonExtension a r g) ?_).mp
      (((MeanValues.harmonic_bridge _ _).mp (poisson_harmonic hn a r hr g).2) x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact (poissonExtension_interior a r g hy).symm

/-- A real harmonic function attaining an interior global maximum is locally
constant, by positivity of volume and its ball mean identity. -/
theorem harmonic_constant_near_max {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u : Space n → ℝ) (hu : MeanValues.IsHarmonic Ω u) {x : Space n} (hx : x ∈ Ω)
    (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∃ ε > 0, ball x ε ⊆ (Ω : Set _) ∧ EqOn u (fun _ => u x) (ball x ε) := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hx)
  let ε := R / 2
  have hε : 0 < ε := half_pos hR
  have hclosed : closedBall x ε ⊆ (Ω : Set _) :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hRΩ
  have hopen : ball x ε ⊆ (Ω : Set _) := ball_subset_closedBall.trans hclosed
  have hc := hu.1.continuousOn.mono hclosed
  have hi : IntegrableOn u (ball x ε) :=
    (hc.integrableOn_compact (isCompact_closedBall x ε)).mono_set ball_subset_closedBall
  have hmean := (MeanValues.mean_values hn Ω u hu x ε hε hclosed).2
  change u x = (volume.real (ball x ε))⁻¹ * ∫ y in ball x ε, u y at hmean
  have hV : volume.real (ball x ε) ≠ 0 :=
    (ENNReal.toReal_pos (measure_ball_pos volume x hε).ne' measure_ball_lt_top.ne).ne'
  have he := congrArg (fun z : ℝ => volume.real (ball x ε) * z) hmean
  simp only [← mul_assoc, mul_inv_cancel₀ hV, one_mul] at he
  haveI : IsFiniteMeasure (volume.restrict (ball x ε)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Space n))) (x := x) (r := ε))⟩
  have hzero : (∫ y in ball x ε, u x - u y) = 0 := by
    rw [integral_sub (integrable_const _) hi, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change volume.real (ball x ε) * u x - (∫ y in ball x ε, u y) = 0
    exact sub_eq_zero.mpr he
  have hnonneg : ∀ᵐ y ∂volume.restrict (ball x ε), 0 ≤ u x - u y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact sub_nonneg.mpr (hmax y (hopen hy))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    ((integrable_const _).sub hi)).mp hzero
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    (continuousOn_const.sub (hu.1.continuousOn.mono hopen)) continuousOn_const
  refine ⟨ε, hε, hopen, fun y hy => ?_⟩
  exact (sub_eq_zero.mp (heq hy)).symm

/-- Strong maximum principle on a ball, derived independently from mean values. -/
theorem harmonic_eqOn_ball_of_max {n : ℕ} (hn : 1 ≤ n) (a : Space n) (r : ℝ)
    (u : Space n → ℝ) (hu : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ u)
    {x : Space n} (hx : x ∈ ball a r) (hmax : ∀ y ∈ ball a r, u y ≤ u x) :
    EqOn u (fun _ => u x) (ball a r) := by
  let S : Set (ball a r) := {y | u y = u x}
  have hc : Continuous (fun y : ball a r => u y) := hu.1.continuousOn.domRestrict
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨ε, hε, _, heq⟩ := harmonic_constant_near_max hn ⟨ball a r, isOpen_ball⟩
      u hu y.property (fun z hz => (hmax z hz).trans_eq hy.symm)
    have hnhds : {z : ball a r | (z : Space n) ∈ ball (y : Space n) ε} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    apply mem_of_superset hnhds
    intro z hz
    exact (heq hz).trans hy
  haveI : PreconnectedSpace (ball a r) := Subtype.preconnectedSpace isPreconnected_ball
  have hevery := (IsClopen.eq_univ ⟨hclosed, hopen⟩ (show S.Nonempty from ⟨⟨x, hx⟩, rfl⟩))
  intro y hy
  have : (⟨y, hy⟩ : ball a r) ∈ S := by rw [hevery]; trivial
  exact this


/-- The weak maximum principle needs only continuity on the closed ball. -/
theorem harmonic_nonpos_closedBall {n : ℕ} (hn : 1 ≤ n) (a : Space n) (r : ℝ)
    (hr : 0 < r) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ u)
    (hc : ContinuousOn u (closedBall a r))
    (hb : ∀ ζ ∈ sphere a r, u ζ ≤ 0) :
    ∀ x ∈ closedBall a r, u x ≤ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨y, hy, hmax⟩ := (isCompact_closedBall a r).exists_isMaxOn
    (nonempty_closedBall.mpr hr.le) hc
  have hmy : u y ≤ 0 := by
    by_cases hyi : y ∈ ball a r
    · have heqi := harmonic_eqOn_ball_of_max hn a r u hu hyi
        (fun z hz => hmax (ball_subset_closedBall hz))
      have heq : EqOn u (fun _ => u y) (closedBall a r) :=
        heqi.of_subset_closure hc continuousOn_const ball_subset_closedBall
          (by rw [closure_ball a hr.ne'])
      obtain ⟨ζ, hζ⟩ := (NormedSpace.sphere_nonempty (x := a)).mpr hr.le
      calc u y = u ζ := (heq (sphere_subset_closedBall hζ)).symm
           _ ≤ 0 := hb ζ hζ
    · exact hb y (by rw [mem_sphere]; exact le_antisymm (mem_closedBall.mp hy) (le_of_not_gt hyi))
  intro x hx
  exact (hmax hx).trans hmy

/-- Apply the real maximum principle to both signs. -/
theorem harmonic_zero_closedBall_real {n : ℕ} (hn : 1 ≤ n) (a : Space n) (r : ℝ)
    (hr : 0 < r) (u : Space n → ℝ)
    (hu : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ u)
    (hc : ContinuousOn u (closedBall a r))
    (hb : ∀ ζ ∈ sphere a r, u ζ = 0) :
    EqOn u (fun _ => 0) (closedBall a r) := by
  have hle := harmonic_nonpos_closedBall hn a r hr u hu hc (fun ζ hζ => (hb ζ hζ).le)
  have hneg : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ (-u) :=
    (MeanValues.harmonic_bridge _ _).mpr ((MeanValues.harmonic_bridge _ _).mp hu).neg
  have hge := harmonic_nonpos_closedBall hn a r hr (-u) hneg hc.neg
    (fun ζ hζ => by simp [hb ζ hζ])
  intro x hx
  exact le_antisymm (hle x hx) (by simpa using hge x hx)

/-- Harmonic functions continuous on the closed ball are determined by their trace. -/
theorem harmonic_eqOn_closedBall {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (a : Space n) (r : ℝ) (hr : 0 < r) (u v : Space n → 𝕜)
    (hu : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ u)
    (hv : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ v)
    (hcu : ContinuousOn u (closedBall a r)) (hcv : ContinuousOn v (closedBall a r))
    (hb : ∀ ζ ∈ sphere a r, u ζ = v ζ) : EqOn u v (closedBall a r) := by
  let w : Space n → 𝕜 := u - v
  have hw : InnerProductSpace.HarmonicOnNhd w (ball a r) :=
    ((MeanValues.harmonic_bridge _ _).mp hu).sub ((MeanValues.harmonic_bridge _ _).mp hv)
  have hcw : ContinuousOn w (closedBall a r) := hcu.sub hcv
  have hbw : ∀ ζ ∈ sphere a r, w ζ = 0 := by
    intro ζ hζ
    exact sub_eq_zero.mpr (hb ζ hζ)
  have hre : EqOn (fun x => RCLike.re (w x)) (fun _ => 0) (closedBall a r) :=
    harmonic_zero_closedBall_real hn a r hr _
      ((MeanValues.harmonic_bridge _ _).mpr (hw.comp_CLM RCLike.reCLM))
      (RCLike.continuous_re.comp_continuousOn hcw)
      (fun ζ hζ => by rw [hbw ζ hζ, map_zero])
  have him : EqOn (fun x => RCLike.im (w x)) (fun _ => 0) (closedBall a r) :=
    harmonic_zero_closedBall_real hn a r hr _
      ((MeanValues.harmonic_bridge _ _).mpr (hw.comp_CLM RCLike.imCLM))
      (RCLike.continuous_im.comp_continuousOn hcw)
      (fun ζ hζ => by rw [hbw ζ hζ, map_zero])
  intro x hx
  apply sub_eq_zero.mp
  change w x = 0
  apply RCLike.ext
  · simpa only [map_zero] using hre hx
  · simpa only [map_zero] using him hx

/-- The Poisson extension is the unique solution for the given continuous trace. -/
theorem uniqueness : P201Specs.BallPoisson.UniquenessStatement := by
  intro n hn 𝕜 _ a r hr g v hv hc htrace
  apply harmonic_eqOn_closedBall (by omega) a r hr v (poissonExtension a r g)
    hv (poissonExtension_harmonic hn a hr g) hc (continuous_extension hn a r hr g).1
  intro ζ hζ
  exact (htrace ⟨ζ, hζ⟩).trans (poissonExtension_boundary a r g ⟨ζ, hζ⟩).symm

/-- Restrict a harmonic function to the sphere and apply continuous-data uniqueness. -/
theorem representation : P201Specs.BallPoisson.RepresentationStatement := by
  intro n hn 𝕜 _ a r hr Ω u hΩ hu
  let g : C(sphere a r, 𝕜) :=
    ⟨fun ζ => u ζ, (hu.1.continuousOn.mono (sphere_subset_closedBall.trans hΩ)).domRestrict⟩
  have hball : ball a r ⊆ (Ω : Set _) := ball_subset_closedBall.trans hΩ
  have huB : MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ u :=
    ⟨hu.1.mono hball, fun x hx => hu.2 x (hball hx)⟩
  have hext := uniqueness hn a r hr g u huB (hu.1.continuousOn.mono hΩ) (fun _ => rfl)
  refine ⟨g, fun _ => rfl, ?_, hext⟩
  intro x hx
  exact (hext (ball_subset_closedBall hx)).trans (poissonExtension_interior a r g hx)

end P201.BallPoisson
