import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SphereAreaFlux
import MathGenome.Internal.MultivariableAnalysis.D04.C10.NegligibleSeams
import MathGenome.Internal.MultivariableAnalysis.D04.C14.ChartIndependentTangentSpaces
import MathGenome.Internal.MultivariableAnalysis.D04.C14.RegularLevelsAndGraphs
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Regular spherical coordinates, the omitted compact meridian, and outward
normal for the canonical surface integral. -/
noncomputable section
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff Matrix
namespace D04.SphereAreaFlux
open Specs.D04.C10.SphereAreaFlux.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C10.SurfaceAssembly.Model
open Specs.D04.C10.NegligibleSeams.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model

 theorem parametrization_smooth : Specs.D04.C10.SphereAreaFlux.parametrization_smoothType := by
  intro R
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> simp only [parametrization, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · exact ((contDiff_const.mul (contDiff_piLp_apply 2 (i := (0 : Fin 2))).sin).mul
      (contDiff_piLp_apply 2 (i := (1 : Fin 2))).cos)
  · exact ((contDiff_const.mul (contDiff_piLp_apply 2 (i := (0 : Fin 2))).sin).mul
      (contDiff_piLp_apply 2 (i := (1 : Fin 2))).sin)
  · exact contDiff_const.mul (contDiff_piLp_apply 2 (i := (0 : Fin 2))).cos

lemma parametrization_norm_sq (R : ℝ) (u : E 2) :
    ‖parametrization R u‖ ^ 2 = R ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, D04.inner_coordinates]
  simp only [Fin.sum_univ_three, ← pow_two]
  change (R * Real.sin (u 0) * Real.cos (u 1)) ^ 2 +
    (R * Real.sin (u 0) * Real.sin (u 1)) ^ 2 + (R * Real.cos (u 0)) ^ 2 = R ^ 2

  calc
    _ = R ^ 2 * (Real.sin (u 0) ^ 2 *
        (Real.cos (u 1) ^ 2 + Real.sin (u 1) ^ 2) + Real.cos (u 0) ^ 2) := by ring
    _ = R ^ 2 := by simp only [Real.cos_sq_add_sin_sq, mul_one, Real.sin_sq_add_cos_sq]

theorem parametrization_norm : Specs.D04.C10.SphereAreaFlux.parametrization_normType := by
  intro R hR u
  have h := parametrization_norm_sq R u
  nlinarith [norm_nonneg (parametrization R u)]

/-- The ordered tangent vectors, valid even at singular parameters. -/
def thetaTangent (R : ℝ) (u : E 2) : E 3 :=
  WithLp.toLp 2 ![R * Real.cos (u 0) * Real.cos (u 1),
    R * Real.cos (u 0) * Real.sin (u 1), -R * Real.sin (u 0)]
def phiTangent (R : ℝ) (u : E 2) : E 3 :=
  WithLp.toLp 2 ![-R * Real.sin (u 0) * Real.sin (u 1),
    R * Real.sin (u 0) * Real.cos (u 1), 0]

def parametrizationDerivative (R : ℝ) (u : E 2) : E 2 →L[ℝ] E 3 :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).smulRight (thetaTangent R u) +
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).smulRight (phiTangent R u)

lemma hasFDerivAt_parametrization (R : ℝ) (u : E 2) :
    HasFDerivAt (parametrization R) (parametrizationDerivative R u) u := by
  apply HasStrictFDerivAt.hasFDerivAt
  apply (hasStrictFDerivAt_piLp 2).mpr
  intro i
  have ht := PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 u (0 : Fin 2)
  have hp := PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 u (1 : Fin 2)
  fin_cases i
  · convert (ht.sin.const_mul R).mul hp.cos using 1 <;>
      first | rfl | (ext v; simp [parametrizationDerivative, thetaTangent, phiTangent]; ring)
  · convert (ht.sin.const_mul R).mul hp.sin using 1 <;>
      first | rfl | (ext v; simp [parametrizationDerivative, thetaTangent, phiTangent]; ring)
  · convert ht.cos.const_mul R using 1 <;>
      first | rfl | (ext v; simp [parametrizationDerivative, thetaTangent, phiTangent]; ring)

lemma tangent_columns (R : ℝ) (u : E 2) :
    columns (fderiv ℝ (parametrization R) u).toLinearMap 0 = thetaTangent R u ∧
    columns (fderiv ℝ (parametrization R) u).toLinearMap 1 = phiTangent R u := by
  rw [(hasFDerivAt_parametrization R u).fderiv]
  constructor <;> ext i <;>
    simp [columns, parametrizationDerivative,
      Specs.D04.C01.EuclideanInterfaces.Model.standardBasis, EuclideanSpace.basisFun_apply]

lemma cross_tangents (R : ℝ) (u : E 2) :
    cross (thetaTangent R u) (phiTangent R u) =
      (R * Real.sin (u 0)) • parametrization R u := by
  ext i
  fin_cases i <;>
    simp [cross, thetaTangent, phiTangent, parametrization, crossProduct,
      PiLp.smul_apply, smul_eq_mul]
  calc
    _ = R ^ 2 * Real.cos (u 0) * Real.sin (u 0) *
      (Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem ordered_area_vector : Specs.D04.C10.SphereAreaFlux.ordered_area_vectorType := by
  intro R hR u
  simp only [areaVector, (tangent_columns R u).1, (tangent_columns R u).2,
    cross_tangents, radialNormal, smul_smul]
  congr 1
  field_simp
  <;> ring

lemma parameterDomain_open : IsOpen parameterDomain := by
  have ht : Continuous (fun u : E 2 => u 0) := (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).continuous
  have hp : Continuous (fun u : E 2 => u 1) := (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).continuous
  exact (isOpen_lt continuous_const ht).inter
    ((isOpen_lt ht continuous_const).inter
      ((isOpen_lt continuous_const hp).inter (isOpen_lt hp continuous_const)))

lemma radialNormal_norm (R : ℝ) (hR : 0 < R) (x : E 3) (hx : x ∈ sphere R) :
    ‖radialNormal R x‖ = 1 := by
  change ‖x‖ = R at hx
  simp [radialNormal, norm_smul, abs_of_pos hR, hx, ne_of_gt hR]

lemma radialNormal_inner (R : ℝ) (hR : 0 < R) (x : E 3) (hx : x ∈ sphere R) :
    ⟪x, radialNormal R x⟫ = R := by
  change ‖x‖ = R at hx
  rw [radialNormal, inner_smul_right, real_inner_self_eq_norm_sq, hx]
  field_simp

lemma areaVector_norm (R : ℝ) (hR : 0 < R) (u : E 2) (hu : u ∈ parameterDomain) :
    ‖areaVector (parametrization R) u‖ = R ^ 2 * Real.sin (u 0) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2.1
  rw [ordered_area_vector R hR, norm_smul,
    radialNormal_norm R hR _ (parametrization_norm R hR u)]
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (sq_pos_of_pos hR) hs), mul_one]

theorem regular_parametrization : Specs.D04.C10.SphereAreaFlux.regular_parametrizationType := by
  intro R hR
  refine ⟨parameterDomain_open, (parametrization_smooth R).contDiffOn.of_le (by norm_num), ?_⟩
  intro u hu
  apply (D04.PatchGeometryGram.cross_rank _).mp
  change areaVector (parametrization R) u ≠ 0
  intro hz
  have hn := areaVector_norm R hR u hu
  rw [hz, norm_zero] at hn
  have hs := Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2.1
  exact (ne_of_gt (mul_pos (sq_pos_of_pos hR) hs)) hn.symm

theorem density_formula : Specs.D04.C10.SphereAreaFlux.density_formulaType := by
  intro R hR u hu
  change gramFactor _ = _
  exact (D04.PatchGeometryGram.gram_cross _).trans (areaVector_norm R hR u hu)

lemma sphere_compact (R : ℝ) : IsCompact (sphere R) := by
  have he : sphere R = Metric.sphere (0 : E 3) R := by
    ext x; simp [sphere, Metric.mem_sphere, dist_zero_right]
  rw [he]
  exact isCompact_sphere _ _

lemma meridian_subset (R : ℝ) (hR : 0 < R) : meridian R ⊆ sphere R := by
  rintro x ⟨t, ht, rfl⟩
  exact parametrization_norm R hR _

lemma meridian_curve_smooth (R : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => parametrization R (WithLp.toLp 2 ![t, 0])) := by
  apply (parametrization_smooth R).comp
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

lemma meridian_finiteSeam (R : ℝ) : FiniteSeam (meridian R) := by
  let γ : CompactCurve 3 :=
    { lower := 0, upper := Real.pi, ordered := Real.pi_pos.le,
      toFun := fun t => parametrization R (WithLp.toLp 2 ![t, 0]),
      regular := (meridian_curve_smooth R).contDiffOn.of_le (by norm_num) }
  refine ⟨1, fun _ => γ, ∅, ?_⟩
  ext x
  constructor
  · intro hx
    exact Or.inl (mem_iUnion.mpr ⟨0, hx⟩)
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hi
    · exact False.elim (Finset.notMem_empty x hx)

lemma meridian_compact (R : ℝ) : IsCompact (meridian R) :=
  isCompact_Icc.image (meridian_curve_smooth R).continuous

lemma parametrization_injOn (R : ℝ) (hR : 0 < R) :
    InjOn (parametrization R) parameterDomain := by
  intro u hu v hv huv
  have hz := congrArg (fun x : E 3 => x 2) huv
  have ht : u 0 = v 0 := by
    apply Real.injOn_cos ⟨hu.1.le, hu.2.1.le⟩ ⟨hv.1.le, hv.2.1.le⟩
    apply mul_left_cancel₀ (ne_of_gt hR)
    exact hz
  have hx := congrArg (fun x : E 3 => x 0) huv
  have hy := congrArg (fun x : E 3 => x 1) huv
  have hn : R * Real.sin (u 0) ≠ 0 :=
    mul_ne_zero (ne_of_gt hR) (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2.1))
  have hc : Real.cos (u 1) = Real.cos (v 1) := by
    apply mul_left_cancel₀ hn
    change R * Real.sin (u 0) * Real.cos (u 1) =
      R * Real.sin (v 0) * Real.cos (v 1) at hx
    rwa [← ht] at hx
  have hs : Real.sin (u 1) = Real.sin (v 1) := by
    apply mul_left_cancel₀ hn
    change R * Real.sin (u 0) * Real.sin (u 1) =
      R * Real.sin (v 0) * Real.sin (v 1) at hy
    rwa [← ht] at hy
  have hp : u 1 = v 1 := by
    have hc1 : Real.cos (u 1 - v 1) = 1 := by
      rw [Real.cos_sub, hc, hs]
      nlinarith [Real.sin_sq_add_cos_sq (v 1)]
    have hdiff : u 1 - v 1 = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hu.2.2.1, hv.2.2.2])
        (by linarith [hu.2.2.2, hv.2.2.1])).mp hc1
    linarith
  ext i
  fin_cases i
  · exact ht
  · exact hp

def sphereDefining (R : ℝ) (x : E 3) : E 1 :=
  (‖x‖ ^ 2 - R ^ 2) • WithLp.toLp 2 ![1]

lemma sphereDefining_hasFDerivAt (R : ℝ) (x : E 3) :
    HasFDerivAt (sphereDefining R)
      (((2 : ℕ) • innerSL ℝ x).smulRight (WithLp.toLp 2 ![1])) x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (R ^ 2)).smul_const _

lemma sphereDefining_zero (R : ℝ) (hR : 0 < R) (x : E 3) :
    sphereDefining R x = 0 ↔ x ∈ sphere R := by
  constructor
  · intro hx
    have hh := congrArg (fun z : E 1 => z 0) hx
    simp [sphereDefining] at hh
    change ‖x‖ = R
    nlinarith [norm_nonneg x]
  · intro hx
    change ‖x‖ = R at hx
    simp [sphereDefining, hx]

lemma sphereDefining_surjective (R : ℝ) (hR : 0 < R) (x : E 3)
    (hx : sphereDefining R x = 0) : Function.Surjective (fderiv ℝ (sphereDefining R) x) := by
  have hn : ‖x‖ = R := (sphereDefining_zero R hR x).mp hx
  rw [(sphereDefining_hasFDerivAt R x).fderiv]
  intro y
  refine ⟨(y 0 / (2 * R ^ 2)) • x, ?_⟩
  ext i
  fin_cases i
  simp [ContinuousLinearMap.smulRight_apply, real_inner_self_eq_norm_sq, hn]
  field_simp

theorem sphere_manifold : Specs.D04.C10.SphereAreaFlux.sphere_manifoldType := by
  intro R hR
  refine ⟨sphere_compact R, ?_⟩
  have hm := D04.RegularLevels.regular_zero_set (r := 1) (k := 2) (n := 3)
    univ (sphereDefining R) ⟨le_rfl, by norm_num⟩ (by omega) isOpen_univ
    (((contDiff_norm_sq ℝ).sub contDiff_const).smul contDiff_const).contDiffOn
    (fun x _ hx => ?_)
  · have he : univ ∩ (sphereDefining R) ⁻¹' {0} = sphere R := by
      ext x
      simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_singleton_iff]
      exact sphereDefining_zero R hR x
    rwa [he] at hm
  · have hr : LinearMap.range (fderiv ℝ (sphereDefining R) x).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr (sphereDefining_surjective R hR x hx)
    rw [hr]
    simp

lemma sphere_embedded (R : ℝ) (hR : 0 < R) : IsEmbeddedManifold 1 2 (sphere R) :=
  (D04.boundaryless_iff.mp (sphere_manifold R hR).2).1

lemma sphere_level_set (R : ℝ) (hR : 0 < R) :
    univ ∩ (sphereDefining R) ⁻¹' {0} = sphere R := by
  ext x
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_singleton_iff]
  exact sphereDefining_zero R hR x

theorem outward_normal : Specs.D04.C10.SphereAreaFlux.outward_normalType := by
  intro R hR
  refine ⟨?_, ?_⟩
  · change Continuous (fun x : sphere R => R⁻¹ • (x : E 3))
    exact (continuous_const (y := R⁻¹)).smul
      (continuous_subtype_val (p := sphere R))
  · intro x
    refine ⟨⟨radialNormal_norm R hR x x.property, ?_⟩, radialNormal_inner R hR x x.property⟩
    have hk := D04.tangentSpace_regular_level (r := 1) (k := 2) (n := 3)
      univ (sphereDefining R) ⟨le_rfl, by norm_num⟩ (by omega) isOpen_univ
      (((contDiff_norm_sq ℝ).sub contDiff_const).smul contDiff_const).contDiffOn
      (fun y _ hy => sphereDefining_surjective R hR y hy)
    rw [sphere_level_set R hR] at hk
    intro v hv
    have hz : fderiv ℝ (sphereDefining R) x v = 0 := by
      rw [hk x x.property] at hv
      exact hv
    rw [(sphereDefining_hasFDerivAt R x).fderiv] at hz
    have hh := congrArg (fun y : E 1 => y 0) hz
    simp at hh
    have ho : ⟪(x : E 3), v⟫ = 0 := by linarith
    simp [radialNormal, inner_smul_left, ho]

theorem negligible_meridian : Specs.D04.C10.SphereAreaFlux.negligible_meridianType := by
  intro R hR
  have h := D04.NegligibleSeams.finite_seam_areaNull
    (sphere_embedded R hR) (meridian_finiteSeam R) (meridian_subset R hR)
  exact ⟨meridian_finiteSeam R, meridian_subset R hR, h.1, h.2⟩

def rotatedEquatorial (x : E 3) : ℂ := -((x 0 : ℂ) + (x 1 : ℂ) * Complex.I)

def angularInverse (R : ℝ) (x : E 3) : E 2 :=
  WithLp.toLp 2 ![Real.arccos (x 2 / R),
    Complex.arg (rotatedEquatorial x) + Real.pi]

lemma rotatedEquatorial_parametrization (R : ℝ) (u : E 2) :
    rotatedEquatorial (parametrization R u) =
      ((R * Real.sin (u 0) : ℝ) : ℂ) *
        (Complex.cos ((u 1 - Real.pi : ℝ) : ℂ) +
          Complex.sin ((u 1 - Real.pi : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [rotatedEquatorial, parametrization, Complex.cos_sub, Complex.sin_sub] <;> ring

lemma azimuth_recovery (R : ℝ) (hR : 0 < R) (u : E 2) (hu : u ∈ parameterDomain) :
    Complex.arg (rotatedEquatorial (parametrization R u)) = u 1 - Real.pi := by
  rw [rotatedEquatorial_parametrization]
  apply Complex.arg_mul_cos_add_sin_mul_I
  · exact mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2.1)
  · exact ⟨by linarith [hu.2.2.1], by linarith [hu.2.2.2]⟩

lemma angularInverse_left (R : ℝ) (hR : 0 < R) (u : E 2) (hu : u ∈ parameterDomain) :
    angularInverse R (parametrization R u) = u := by
  ext i
  fin_cases i
  · change Real.arccos ((R * Real.cos (u 0)) / R) = u 0
    rw [mul_div_cancel_left₀ _ hR.ne', Real.arccos_cos hu.1.le hu.2.1.le]
  · change Complex.arg (rotatedEquatorial (parametrization R u)) + Real.pi = u 1
    rw [azimuth_recovery R hR u hu]
    ring

lemma rotatedEquatorial_slit (R : ℝ) (hR : 0 < R) (u : E 2)
    (hu : u ∈ parameterDomain) : rotatedEquatorial (parametrization R u) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg, azimuth_recovery R hR u hu]
  refine ⟨by linarith [hu.2.2.2], ?_⟩
  rw [rotatedEquatorial_parametrization]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (mul_ne_zero hR.ne'
      (Real.sin_pos_of_pos_of_lt_pi hu.1 hu.2.1).ne')
  · intro hz
    have h := Complex.norm_cos_add_sin_mul_I (u 1 - Real.pi)
    rw [hz, norm_zero] at h
    norm_num at h

lemma rotatedEquatorial_continuous : Continuous rotatedEquatorial := by
  unfold rotatedEquatorial
  fun_prop

lemma angularInverse_continuousOn (R : ℝ) :
    ContinuousOn (angularInverse R) (rotatedEquatorial ⁻¹' Complex.slitPlane) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · change ContinuousOn (fun x : E 3 => Real.arccos (x 2 / R)) _
    have hc : Continuous (fun x : E 3 => x 2 / R) := by fun_prop
    exact Real.continuous_arccos.comp_continuousOn hc.continuousOn
  · change ContinuousOn (fun x : E 3 => Complex.arg (rotatedEquatorial x) + Real.pi) _
    exact (Complex.continuousOn_arg.comp rotatedEquatorial_continuous.continuousOn
      (fun x hx => hx)).add_const _

lemma parametrization_embedding (R : ℝ) (hR : 0 < R) :
    Topology.IsEmbedding (fun u : parameterDomain => parametrization R u) := by
  let image := parametrization R '' parameterDomain
  let f : parameterDomain → image := fun u => ⟨parametrization R u, ⟨u, u.property, rfl⟩⟩
  have hmap : ∀ x : image, angularInverse R x ∈ parameterDomain := by
    rintro ⟨x, u, hu, rfl⟩
    rw [angularInverse_left R hR u hu]
    exact hu
  let g : image → parameterDomain := fun x => ⟨angularInverse R x, hmap x⟩
  have hl : Function.LeftInverse g f := by
    intro u
    apply Subtype.ext
    exact angularInverse_left R hR u u.property
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (parametrization_smooth R).continuous.comp continuous_subtype_val
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    apply (angularInverse_continuousOn R).comp_continuous continuous_subtype_val
    rintro ⟨x, u, hu, rfl⟩
    exact rotatedEquatorial_slit R hR u hu
  exact Topology.IsEmbedding.subtypeVal.comp (hl.isEmbedding hg hf)

/-- A numerical iterated integral. Identification with the project's surface
integral still requires the regular compact truncation bridge. -/
lemma truncation_angle_pos (j : ℕ) : 0 < Real.pi / (j + 3 : ℝ) := by positivity
lemma truncation_angle_lt_half_pi (j : ℕ) : Real.pi / (j + 3 : ℝ) < Real.pi / 2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < j + 3) (by norm_num)).mpr
  nlinarith [Real.pi_pos]

lemma truncationDomain_subset (j : ℕ) : truncationDomain j ⊆ parameterDomain := by
  intro u hu
  have hδ := truncation_angle_pos j
  change Real.pi / (j + 3 : ℝ) ≤ u 0 ∧ u 0 ≤ Real.pi - Real.pi / (j + 3 : ℝ) ∧
    Real.pi / (j + 3 : ℝ) ≤ u 1 ∧ u 1 ≤ 2 * Real.pi - Real.pi / (j + 3 : ℝ) at hu
  exact ⟨by linarith [hu.1], by linarith [hu.2.1],
    by linarith [hu.2.2.1], by linarith [hu.2.2.2]⟩

lemma truncation_angle_tendsto :
    Tendsto (fun j : ℕ => Real.pi / (j + 3 : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_const_div_atTop_nhds_zero_nat Real.pi).comp (tendsto_add_atTop_nat 3)

lemma truncated_values_tendsto (R : ℝ) :
    Tendsto (fun j : ℕ => 2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
      Real.cos (Real.pi / (j + 3 : ℝ))) atTop (𝓝 (4 * Real.pi * R ^ 2)) := by
  have h := ((tendsto_const_nhds (x := 2 * R ^ 2)).mul
    ((tendsto_const_nhds (x := 2 * Real.pi)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul truncation_angle_tendsto))).mul
    (Real.continuous_cos.continuousAt.tendsto.comp truncation_angle_tendsto)
  convert h using 1 <;> simp <;> ring

lemma sphere_coordinate_sq (R : ℝ) (x : E 3) (hx : x ∈ sphere R) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = R ^ 2 := by
  calc
    _ = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, D04.inner_coordinates, Fin.sum_univ_three]
      ring
    _ = R ^ 2 := by rw [hx]

lemma meridian_coordinates (R : ℝ) (hR : 0 < R) :
    meridian R = {x ∈ sphere R | x 1 = 0 ∧ 0 ≤ x 0} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨parametrization_norm R hR _, ?_, ?_⟩
    · simp [parametrization]
    · change 0 ≤ R * Real.sin t * Real.cos 0
      simpa using mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
  · rintro ⟨hx, hy, hp⟩
    have hsq := sphere_coordinate_sq R x hx
    have hlo : -1 ≤ x 2 / R := (le_div_iff₀ hR).mpr (by nlinarith [sq_nonneg (x 0)])
    have hhi : x 2 / R ≤ 1 := (div_le_iff₀ hR).mpr (by nlinarith [sq_nonneg (x 0)])
    let t := Real.arccos (x 2 / R)
    have ht : t ∈ Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hz : (parametrization R (WithLp.toLp 2 ![t, 0])) 2 = x 2 := by
      change R * Real.cos t = x 2
      rw [Real.cos_arccos hlo hhi]
      field_simp
    have hnorm := sphere_coordinate_sq R (parametrization R (WithLp.toLp 2 ![t, 0]))
      (parametrization_norm R hR _)
    have hz0 : (parametrization R (WithLp.toLp 2 ![t, 0])) 1 = 0 := by simp [parametrization]
    have hp0 : 0 ≤ (parametrization R (WithLp.toLp 2 ![t, 0])) 0 := by
      change 0 ≤ R * Real.sin t * Real.cos 0
      simpa using mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
    refine ⟨t, ht, ?_⟩
    ext i
    fin_cases i
    · rw [hz, hz0] at hnorm
      rw [hy] at hsq
      change (parametrization R (WithLp.toLp 2 ![t, 0])) 0 = x 0
      nlinarith [sq_nonneg (x 0)]
    · exact hz0.trans hy.symm
    · exact hz

lemma sphere_off_meridian (R : ℝ) (hR : 0 < R) :
    sphere R \ meridian R = sphere R ∩ rotatedEquatorial ⁻¹' Complex.slitPlane := by
  rw [meridian_coordinates R hR]
  ext x
  simp only [mem_diff, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [Complex.mem_slitPlane_iff]
  simp only [rotatedEquatorial, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, zero_sub, add_zero, zero_add]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    by_cases hy : x 1 = 0
    · left
      have : ¬ 0 ≤ x 0 := fun hp => hn ⟨hx, hy, hp⟩
      linarith
    · right
      exact neg_ne_zero.mpr hy
  · rintro ⟨hx, ha⟩
    refine ⟨hx, ?_⟩
    rintro ⟨_, hy, hp⟩
    rcases ha with ha | ha
    · linarith
    · exact ha (by simp [hy])

lemma angularInverse_right (R : ℝ) (hR : 0 < R) (x : E 3)
    (hx : x ∈ sphere R) (hs : rotatedEquatorial x ∈ Complex.slitPlane) :
    angularInverse R x ∈ parameterDomain ∧ parametrization R (angularInverse R x) = x := by
  let z := rotatedEquatorial x
  let t := Real.arccos (x 2 / R)
  have hz : z ≠ 0 := Complex.slitPlane_ne_zero hs
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsq := sphere_coordinate_sq R x hx
  have hzs : ‖z‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, rotatedEquatorial]
    ring
  have hlo : -1 ≤ x 2 / R := (le_div_iff₀ hR).mpr
    (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])
  have hhi : x 2 / R ≤ 1 := (div_le_iff₀ hR).mpr
    (by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)])
  have ht0 : 0 ≤ t := Real.arccos_nonneg _
  have htπ : t ≤ Real.pi := Real.arccos_le_pi _
  have hcos : R * Real.cos t = x 2 := by
    rw [Real.cos_arccos hlo hhi]
    field_simp
  have hsin : R * Real.sin t = ‖z‖ := by
    have htrig := congrArg (fun a : ℝ => R ^ 2 * a) (Real.sin_sq_add_cos_sq t)
    have hc2 := congrArg (fun a : ℝ => a ^ 2) hcos
    have hp := mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi ht0 htπ)
    nlinarith
  have ht0' : 0 < t := lt_of_le_of_ne ht0 (by
    intro ht
    rw [← ht, Real.sin_zero, mul_zero] at hsin
    linarith)
  have htπ' : t < Real.pi := lt_of_le_of_ne htπ (by
    intro ht
    rw [ht, Real.sin_pi, mul_zero] at hsin
    linarith)
  have ha0 : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
  have haπ : Complex.arg z < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hs)
  constructor
  · change 0 < t ∧ t < Real.pi ∧ 0 < Complex.arg z + Real.pi ∧
      Complex.arg z + Real.pi < 2 * Real.pi
    exact ⟨ht0', htπ', by linarith, by linarith⟩
  · ext i
    fin_cases i
    · change R * Real.sin t * Real.cos (Complex.arg z + Real.pi) = x 0
      rw [hsin, Real.cos_add_pi]
      have hr := Complex.norm_mul_cos_arg z
      have hzre : z.re = -x 0 := by simp [z, rotatedEquatorial]
      rw [hzre] at hr
      nlinarith
    · change R * Real.sin t * Real.sin (Complex.arg z + Real.pi) = x 1
      rw [hsin, Real.sin_add_pi]
      have hi := Complex.norm_mul_sin_arg z
      have hzim : z.im = -x 1 := by simp [z, rotatedEquatorial]
      rw [hzim] at hi
      nlinarith
    · exact hcos

theorem embedded_patch (R : ℝ) (hR : 0 < R) :
    EmbeddedPatch parameterDomain (parametrization R) :=
  ⟨regular_parametrization R hR, parametrization_embedding R hR⟩

lemma parametrization_image (R : ℝ) (hR : 0 < R) :
    parametrization R '' parameterDomain = sphere R \ meridian R := by
  rw [sphere_off_meridian R hR]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨parametrization_norm R hR u, rotatedEquatorial_slit R hR u hu⟩
  · rintro ⟨hx, hs⟩
    exact ⟨angularInverse R x, (angularInverse_right R hR x hx hs).1,
      (angularInverse_right R hR x hx hs).2⟩

def sphericalChart (R : ℝ) (hR : 0 < R) : EmbeddedChart 1 2 3 (sphere R) where
  half := false
  half_pos := by simp
  source := parameterDomain
  source_open := ⟨parameterDomain, parameterDomain_open, by
    simp [Specs.D04.C14.EmbeddedManifoldCharts.Model.parameterSpace]⟩
  ambient := rotatedEquatorial ⁻¹' Complex.slitPlane
  ambient_open := Complex.isOpen_slitPlane.preimage rotatedEquatorial_continuous
  toFun := parametrization R
  invFun := angularInverse R
  map_source := by
    intro u hu
    exact ⟨parametrization_norm R hR u, rotatedEquatorial_slit R hR u hu⟩
  map_target := by
    intro x hx
    exact (angularInverse_right R hR x hx.1 hx.2).1
  left_inv := angularInverse_left R hR
  right_inv := by
    intro x hx
    exact (angularInverse_right R hR x hx.1 hx.2).2
  continuous_toFun := (parametrization_smooth R).continuous.continuousOn
  continuous_invFun := (angularInverse_continuousOn R).mono inter_subset_right
  regular := (D04.open_fullRankLocalExtension_iff _ _ parameterDomain_open).mpr
    (regular_parametrization R hR).2

theorem embedded_spherical_chart : Specs.D04.C10.SphereAreaFlux.embedded_spherical_chartType := by
  intro R hR
  exact ⟨embedded_patch R hR, parametrization_image R hR,
    sphericalChart R hR, rfl, rfl, rfl⟩

def truncationBox (j : ℕ) : Darboux.Box 2 where
  lower := WithLp.toLp 2 ![Real.pi / (j + 3 : ℝ), Real.pi / (j + 3 : ℝ)]
  upper := WithLp.toLp 2 ![Real.pi - Real.pi / (j + 3 : ℝ),
    2 * Real.pi - Real.pi / (j + 3 : ℝ)]
  ordered i := by
    have hp := truncation_angle_lt_half_pi j
    fin_cases i <;> simp <;> linarith [Real.pi_pos]

lemma truncationBox_carrier (j : ℕ) : Darboux.carrier (truncationBox j) = truncationDomain j := by
  ext u
  simp only [Darboux.carrier, truncationBox, truncationDomain, mem_ofPred_eq, mem_Icc]
  constructor
  · intro h
    exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩ i
    fin_cases i
    · exact ⟨h₁,h₂⟩
    · exact ⟨h₃,h₄⟩

lemma box_carrier_compact {n : ℕ} (Q : Darboux.Box n) : IsCompact (Darboux.carrier Q) := by
  have hc := (isCompact_pi_infinite (fun i : Fin n =>
    isCompact_Icc (a := Q.lower i) (b := Q.upper i))).image (PiLp.continuous_toLp 2 _)
  convert hc using 1
  ext u
  simp only [Darboux.carrier, mem_ofPred_eq, mem_image]
  exact ⟨fun h => ⟨WithLp.ofLp u, h, rfl⟩, fun ⟨v, hv, he⟩ => he ▸ hv⟩

def sphericalPiece (R : ℝ) (hR : 0 < R) (j : ℕ) : ChartPiece (sphere R) where
  chart := sphericalChart R hR
  domain := truncationDomain j
  compact := truncationBox_carrier j ▸ box_carrier_compact (truncationBox j)
  jordan := truncationBox_carrier j ▸ OneCoordinate.Boxes.jordan_carrier (truncationBox j)
  subset_source := truncationDomain_subset j

def sphericalTruncation (R : ℝ) (hR : 0 < R) (j : ℕ) :
    SurfaceTruncation (sphere R) (meridian R) where
  count := 1
  piece _ := sphericalPiece R hR j
  avoids _ := by
    rintro x ⟨u, hu, rfl⟩
    rw [← parametrization_image R hR]
    exact ⟨u, truncationDomain_subset j hu, rfl⟩
  overlaps i k hik := by
    exact (hik (Subsingleton.elim _ _)).elim

lemma truncationSet_eq (R : ℝ) (hR : 0 < R) (j : ℕ) :
    truncationSet (sphericalTruncation R hR j) = parametrization R '' truncationDomain j := by
  change (⋃ _ : Fin 1, parametrization R '' truncationDomain j) = _
  exact iUnion_const _

def angularMargin (u : E 2) : ℝ :=
  min (min (u 0) (Real.pi - u 0)) (min (u 1) (2 * Real.pi - u 1))

lemma angularMargin_continuous : Continuous angularMargin := by
  unfold angularMargin
  fun_prop

lemma angularMargin_pos {u : E 2} (hu : u ∈ parameterDomain) : 0 < angularMargin u := by
  exact lt_min (lt_min hu.1 (sub_pos.mpr hu.2.1))
    (lt_min hu.2.2.1 (sub_pos.mpr hu.2.2.2))

lemma margin_truncation {u : E 2} {j : ℕ}
    (h : Real.pi / (j + 3 : ℝ) ≤ angularMargin u) : u ∈ truncationDomain j := by
  simp only [angularMargin, le_min_iff] at h
  exact ⟨h.1.1, by linarith [h.1.2], h.2.1, by linarith [h.2.2]⟩

lemma sphericalTruncation_exhausts (R : ℝ) (hR : 0 < R) :
    ExhaustsComplement (sphericalTruncation R hR) := by
  intro K hK hsub
  by_cases he : K.Nonempty
  · have hslit : K ⊆ rotatedEquatorial ⁻¹' Complex.slitPlane := by
      intro x hx
      have h := hsub hx
      rw [sphere_off_meridian R hR] at h
      exact h.2
    have hcont := (angularInverse_continuousOn R).mono hslit
    let L := angularInverse R '' K
    have hL : IsCompact L := hK.image_of_continuousOn hcont
    have hLd : L ⊆ parameterDomain := by
      rintro u ⟨x,hx,rfl⟩
      exact (angularInverse_right R hR x (hsub hx).1 (hslit hx)).1
    obtain ⟨u, hu, hmin⟩ := hL.exists_isMinOn (he.image (angularInverse R))
      angularMargin_continuous.continuousOn
    have hpos := angularMargin_pos (hLd hu)
    filter_upwards [truncation_angle_tendsto.eventually_le_const hpos] with j hj
    intro x hx
    rw [truncationSet_eq]
    refine ⟨angularInverse R x, margin_truncation (hj.trans (hmin ?_)), ?_⟩
    · exact ⟨x,hx,rfl⟩
    · exact (angularInverse_right R hR x (hsub hx).1 (hslit hx)).2
  · have hzero : K = ∅ := not_nonempty_iff_eq_empty.mp he
    simp [hzero]

lemma sphericalTruncation_area_converges (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j => truncationIntegral (sphericalTruncation R hR j) (fun _ => 1)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun _ => 1))) := by
  exact D04.NegligibleSeams.seam_truncation_convergence (sphere_embedded R hR)
    (sphere_compact R) (meridian_finiteSeam R) (meridian_subset R hR) _ continuous_const _
    (sphericalTruncation_exhausts R hR)

lemma sphericalTruncation_flux_converges (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j => truncationIntegral (sphericalTruncation R hR j)
      (fun x => ⟪(x : E 3), radialNormal R x⟫)) atTop
      (𝓝 (surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫))) := by
  apply D04.NegligibleSeams.seam_truncation_convergence (sphere_embedded R hR)
    (sphere_compact R) (meridian_finiteSeam R) (meridian_subset R hR)
  · exact continuous_subtype_val.inner (outward_normal R hR).1
  · exact sphericalTruncation_exhausts R hR

theorem cofinal_truncations : Specs.D04.C10.SphereAreaFlux.cofinal_truncationsType := by
  intro R hR
  exact ⟨sphericalTruncation R hR, fun _ => ⟨rfl, fun _ => ⟨rfl,rfl⟩⟩,
    sphericalTruncation_exhausts R hR, sphericalTruncation_area_converges R hR,
    sphericalTruncation_flux_converges R hR⟩

theorem flux_area_relation : Specs.D04.C10.SphereAreaFlux.flux_area_relationType := by
  intro R hR
  calc
    surfaceIntegral (sphere R) (fun x => ⟪(x : E 3), radialNormal R x⟫) =
        surfaceIntegral (sphere R) (R • fun _ => (1 : ℝ)) := by
      congr 1
      funext x
      simpa using radialNormal_inner R hR x x.property
    _ = R * surfaceIntegral (sphere R) (fun _ => 1) :=
      D04SurfaceAssembly.scalar_smul (sphere_embedded R hR) (sphere_compact R) R _ continuous_const

lemma sphere_area_of_truncation_values (R : ℝ) (hR : 0 < R)
    (hv : ∀ j, truncationIntegral (sphericalTruncation R hR j) (fun _ => 1) =
      2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
        Real.cos (Real.pi / (j + 3 : ℝ))) :
    surfaceIntegral (sphere R) (fun _ => 1) = 4 * Real.pi * R ^ 2 := by
  have hc := sphericalTruncation_area_converges R hR
  simp_rw [hv] at hc
  exact tendsto_nhds_unique hc (truncated_values_tendsto R)

open Darboux JordanRegions NullCovers

lemma regionIntegral_closedBox {n : ℕ} (hn : 0 < n) (Q : Box n) (hq : Nondegenerate Q)
    (f : E n → ℝ) (hf : RegionIntegrable (fun x : carrier Q => f x)) :
    regionIntegral (fun x : carrier Q => f x) = lowerIntegral f Q := by
  let g := zeroExtension (fun x : carrier Q => f x)
  let R := enclosingBox (carrier Q)
  have hj := OneCoordinate.Boxes.jordan_carrier Q
  have hR : Encloses (carrier Q) R := enclosingBox_encloses (jordan_bounded hj)
  have hi : Integrable g R := (region_integrable_iff_box _ hR).mp hf
  have hlo (i) : R.lower i < Q.lower i :=
    ((encloses_open hR) (subset_closure (show Q.lower ∈ carrier Q from
      fun k => ⟨le_rfl, Q.ordered k⟩)) i).1
  have hhi (i) : Q.upper i < R.upper i :=
    ((encloses_open hR) (subset_closure (show Q.upper ∈ carrier Q from
      fun k => ⟨Q.ordered k, le_rfl⟩)) i).2
  let P : Grid R := fun i => threePartition (R.lower i) (Q.lower i) (Q.upper i)
    (R.upper i) (hlo i) (hq i) (hhi i)
  let c₀ : CellIndex P := fun _ => (1 : Fin 3)
  have hmid : cellBox P c₀ = Q := by
    apply Subdivision.box_ext <;> ext i <;> rfl
  have hc (c : CellIndex P) : Integrable g (cellBox P c) :=
    (subdivision_integrable g R hi.1 P).mp hi c
  have hnull : Null (frontier (carrier Q)) := contentZero_null
    ((jordan_iff_boundary hn _ (jordan_bounded hj)).mp hj)
  have hother (c : CellIndex P) (hcc : c ≠ c₀) :
      integral g (cellBox P c) (hc c) = 0 := by
    apply ExceptionalSets.integral_zero_off_null (hc c) hnull
    intro x hx hxf
    by_cases hxQ : x ∈ carrier Q
    · have hxin : x ∈ interior (carrier Q) := by
        rw [← closure_sdiff_frontier]
        exact ⟨subset_closure hxQ, hxf⟩
      rw [interior_carrier] at hxin
      obtain ⟨i, hci⟩ : ∃ i, c i ≠ (1 : Fin 3) := by
        by_contra! he
        exact hcc (funext he)
      have hxc := hx i
      change ![R.lower i,Q.lower i,Q.upper i,R.upper i] (c i).castSucc ≤ x i ∧
        x i ≤ ![R.lower i,Q.lower i,Q.upper i,R.upper i] (c i).succ at hxc
      generalize hci' : c i = k at hxc hci
      fin_cases k
      · norm_num at hxc
        exact ((not_lt_of_ge hxc.2) (hxin i).1).elim
      · exact (hci rfl).elim
      · norm_num at hxc
        exact ((not_lt_of_ge hxc.1) (hxin i).2).elim
    · exact zeroExtension_of_not_mem _ hxQ
  rw [integral_eq_on_enclosing_box _ hf hR hi, subdivision_integral g R P hi hc]
  rw [Finset.sum_eq_single c₀]
  · change lowerIntegral g _ = lowerIntegral f Q
    rw [hmid]
    apply lowerIntegral_congr
    intro x hx
    exact zeroExtension_apply (fun x : carrier Q => f x) ⟨x,hx⟩
  · intro c _ hcc
    exact hother c hcc
  · simp

lemma scalar_sin_integral (C a b : ℝ) (hab : a ≤ b) :
    lowerIntegral (fun u : E 1 => C * Real.sin (u 0)) (intervalBox a b hab) =
      C * (Real.cos a - Real.cos b) := by
  have hi := SlicingAndMoments.continuous_box_integrable
    (fun u : E 1 => C * Real.sin (u 0)) (by fun_prop) (intervalBox a b hab)
  obtain ⟨hs,hv⟩ := (Darboux.scalar_integral _ a b hab).2 hi
  have hftc := SingleVariableAnalysis.Riemann.real_ftc_second
    (fun t => -C * Real.cos t) (fun t => C * Real.sin t) a b hab
    (by fun_prop) (fun t _ => by
      convert (Real.hasDerivAt_cos t).const_mul (-C) using 1 <;> ring) hs
  exact hv.trans (hftc.trans (by ring))

lemma truncationBox_nondegenerate (j : ℕ) : Nondegenerate (truncationBox j) := by
  intro i
  have hp := truncation_angle_lt_half_pi j
  fin_cases i <;> change _ < _ <;> dsimp [truncationBox] <;> linarith [Real.pi_pos]

lemma truncated_darboux_integral (R : ℝ) (j : ℕ) :
    lowerIntegral (fun u : E 2 => R ^ 2 * Real.sin (u 0)) (truncationBox j) =
      2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
        Real.cos (Real.pi / (j + 3 : ℝ)) := by
  let δ := Real.pi / (j + 3 : ℝ)
  have hp := truncation_angle_lt_half_pi j
  have ha : δ ≤ Real.pi - δ := by dsimp [δ]; linarith
  have hb : δ ≤ 2 * Real.pi - δ := by dsimp [δ]; linarith [Real.pi_pos]
  let A := intervalBox δ (Real.pi - δ) ha
  let B := intervalBox δ (2 * Real.pi - δ) hb
  let f : E 2 → ℝ := fun u => R ^ 2 * Real.sin (u 0)
  let g : E 1 → ℝ := fun u => (R ^ 2 * (2 * Real.pi - 2 * δ)) * Real.sin (u 0)
  have he : productBox A B = truncationBox j := by
    apply Subdivision.box_ext <;> ext i <;> fin_cases i <;> rfl
  have hf : Integrable f (productBox A B) :=
    SlicingAndMoments.continuous_box_integrable f (by dsimp [f]; fun_prop) _
  have hs (x : E 1) (_hx : x ∈ carrier A) :
      Integrable (fun y => f (productPoint x y)) B := by
    change Integrable (fun _ => R ^ 2 * Real.sin (x 0)) B
    exact integrable_const _ _
  obtain ⟨hg,hv⟩ := Darboux.fubini_slices A B f hf hs g (by
    intro x hx
    change g x = lowerIntegral (fun _ => R ^ 2 * Real.sin (x 0)) B
    rw [(constant_integrals B (R ^ 2 * Real.sin (x 0))).1]
    simp only [Specs.D04.C06.DarbouxIntegral.Model.content, B,
      Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
      Specs.D04.C06.DarbouxIntegral.Model.scalarPoint, Fin.prod_univ_one]
    dsimp [g]
    ring)
  change lowerIntegral g A = lowerIntegral f (productBox A B) at hv
  change lowerIntegral f (truncationBox j) = _
  rw [← he, ← hv]
  change lowerIntegral (fun u : E 1 => (R ^ 2 * (2 * Real.pi - 2 * δ)) *
    Real.sin (u 0)) (intervalBox δ (Real.pi - δ) ha) = _
  rw [scalar_sin_integral, Real.cos_pi_sub]
  dsimp [δ]
  ring

lemma sphericalChart_density (R : ℝ) (hR : 0 < R) (u : E 2) (hu : u ∈ parameterDomain) :
    chartDensity (sphericalChart R hR) u = R ^ 2 * Real.sin (u 0) := by
  have hd : Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential (sphericalChart R hR) u = fderiv ℝ (parametrization R) u := by
    change fderivWithin ℝ (parametrization R) parameterDomain u = _
    exact fderivWithin_of_isOpen parameterDomain_open hu
  rw [D04MetricDensity.chartDensity_matrix, hd]
  exact density_formula R hR u hu

lemma sphericalPiece_coefficient (R : ℝ) (hR : 0 < R) (j : ℕ)
    (u : (sphericalPiece R hR j).domain) :
    pieceCoefficient (sphericalPiece R hR j) (fun _ => 1) u = R ^ 2 * Real.sin ((u : E 2) 0) := by
  change 1 * chartDensity (sphericalChart R hR) u = _
  rw [one_mul, sphericalChart_density R hR u (truncationDomain_subset j u.property)]

lemma sphericalPiece_integral (R : ℝ) (hR : 0 < R) (j : ℕ) :
    pieceIntegral (sphericalPiece R hR j) (fun _ => 1) =
      2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
        Real.cos (Real.pi / (j + 3 : ℝ)) := by
  have hcoef : pieceCoefficient (sphericalPiece R hR j) (fun _ => 1) =
      (fun u : (sphericalPiece R hR j).domain => R ^ 2 * Real.sin ((u : E 2) 0)) := funext (sphericalPiece_coefficient R hR j)
  change regionIntegral _ = _
  rw [hcoef]
  have hj : Jordan (truncationDomain j) := (sphericalPiece R hR j).jordan
  have hi : RegionIntegrable (fun u : truncationDomain j => R ^ 2 * Real.sin ((u : E 2) 0)) := by
    simpa using integrable_continuous_on_closure (by norm_num) hj
      (fun u => R ^ 2 * Real.sin ((u : E 2) 0)) (by fun_prop)
  have hbox := regionIntegral_closedBox (by norm_num) (truncationBox j)
    (truncationBox_nondegenerate j) (fun u => R ^ 2 * Real.sin (u 0))
  rw [truncationBox_carrier] at hbox
  exact (hbox hi).trans (truncated_darboux_integral R j)

lemma sphericalTruncation_integral (R : ℝ) (hR : 0 < R) (j : ℕ) :
    truncationIntegral (sphericalTruncation R hR j) (fun _ => 1) =
      2 * R ^ 2 * (2 * Real.pi - 2 * (Real.pi / (j + 3 : ℝ))) *
        Real.cos (Real.pi / (j + 3 : ℝ)) := by
  change (∑ _ : Fin 1, pieceIntegral (sphericalPiece R hR j) (fun _ => 1)) = _
  simpa using sphericalPiece_integral R hR j


theorem regular_truncations : Specs.D04.C10.SphereAreaFlux.regular_truncationsType := by
  intro R hR
  exact ⟨sphericalTruncation R hR, fun _ => ⟨rfl, fun _ => ⟨rfl,rfl⟩⟩,
    sphericalTruncation_exhausts R hR, sphericalTruncation_integral R hR,
    sphericalTruncation_area_converges R hR, sphericalTruncation_flux_converges R hR⟩

theorem sphere_area : Specs.D04.C10.SphereAreaFlux.sphere_areaType := by
  intro R hR
  exact sphere_area_of_truncation_values R hR (sphericalTruncation_integral R hR)

theorem sphere_flux : Specs.D04.C10.SphereAreaFlux.sphere_fluxType := by
  intro R hR
  rw [flux_area_relation R hR, sphere_area R hR]
  ring

end D04.SphereAreaFlux
