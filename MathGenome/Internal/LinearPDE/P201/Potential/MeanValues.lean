import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import MathGenome.Internal.LinearPDE.P201.Common.SmoothFlux
import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Set Metric MeasureTheory Filter
open MeasureTheory.Measure
open scoped ContDiff Topology Pointwise Convolution InnerProductSpace NNReal

namespace P201.MeanValues

abbrev IsHarmonic : P201Specs.MeanValues.IsHarmonicType :=
  @P201Specs.MeanValues.IsHarmonic
abbrev HasBallMeanValue : P201Specs.MeanValues.HasBallMeanValueType :=
  @P201Specs.MeanValues.HasBallMeanValue
abbrev HasSphereMeanValue : P201Specs.MeanValues.HasSphereMeanValueType :=
  @P201Specs.MeanValues.HasSphereMeanValue
abbrev unitSphereMean : P201Specs.MeanValues.UnitSphereMeanType :=
  @P201Specs.MeanValues.unitSphereMean

theorem omega_pos : P201Specs.MeanValues.OmegaPositiveStatement := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  change 0 < (P201Specs.unitSurface n).real univ
  rw [P201.unitSurfaceMass]
  exact mul_pos (by exact_mod_cast hn) (ENNReal.toReal_pos (measure_ball_pos volume (0 : Space n) zero_lt_one).ne'
    measure_ball_lt_top.ne)

theorem sphere_mean_normalization : P201Specs.MeanValues.SphereMeanNormalizationStatement := by
  intro n hn 𝕜 _ u a r hr
  have hp : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  have he : Topology.IsClosedEmbedding (fun θ : Space n => a + r • θ) := by
    exact ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft a)).isClosedEmbedding
  change ((P201Specs.sphereSurface a r).real univ)⁻¹ •
    (∫ x, u x ∂P201Specs.sphereSurface a r) = _
  rw [P201.sphereSurfaceMass a r hr.le]
  simp only [P201Specs.sphereSurface, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rw [he.integral_map]
  change (P201Specs.omega n * r ^ (n - 1))⁻¹ •
    (r ^ (n - 1) • ∫ θ, u (a + r • θ) ∂P201Specs.unitSurface n) = _
  rw [smul_smul]
  have hc : (P201Specs.omega n * r ^ (n - 1))⁻¹ * r ^ (n - 1) =
      (P201Specs.omega n)⁻¹ := by field_simp
  rw [hc]
  rfl

theorem sphere_mean_one : P201Specs.MeanValues.SphereMeanOneStatement := by
  intro 𝕜 _ u a r hr
  rw [sphere_mean_normalization (by omega) u a r hr]
  have ho : P201Specs.omega 1 = 2 := by
    change (P201Specs.unitSurface 1).real univ = 2
    rw [P201.unitSurfaceDimensionOne]
    norm_num [Measure.real]
  simp only [P201Specs.MeanValues.unitSphereMean, ho]
  rw [P201.unitSurfaceDimensionOne]
  rw [integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
  simp only [integral_dirac]
  congr 2
  · congr 2
    ext i
    fin_cases i
    simp [P102.Trace.Ordinary.linePoint, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  · congr 1
    rw [sub_eq_add_neg, ← smul_neg]
    congr 2
    ext i
    fin_cases i
    simp [P102.Trace.Ordinary.linePoint, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single]

theorem laplacian_bridge : P201Specs.MeanValues.LaplacianBridgeStatement := by
  intro n 𝕜 _ u x hu
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  change (∑ i : Fin n, P201Specs.multiPartial u ({i, i} : P201Specs.MultiIndex n) x) = _
  apply Finset.sum_congr rfl
  intro i _
  have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, hs, P102.U4.partialWord]
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [iteratedFDeriv_two_apply, P102.U4.coordinateVector]

theorem harmonic_bridge : P201Specs.MeanValues.HarmonicBridgeStatement := by
  intro n 𝕜 _ Ω u
  constructor
  · rintro ⟨hc, hl⟩ x hx
    have hcx := hc.contDiffAt (Ω.isOpen.mem_nhds hx)
    refine ⟨hcx, ?_⟩
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    change Laplacian.laplacian u y = 0
    rw [← laplacian_bridge u y (hc.contDiffAt (Ω.isOpen.mem_nhds hy))]
    exact hl y hy
  · intro h
    refine ⟨h.contDiffOn, fun x hx => ?_⟩
    rw [laplacian_bridge u x (h x hx).1]
    exact (h x hx).2.eq_of_nhds

/-- Unit surface measure is carried by the actual unit sphere, including S⁰. -/
theorem unitSurface_ae_mem (n : ℕ) :
    ∀ᵐ θ ∂P201Specs.unitSurface n, θ ∈ sphere (0 : Space n) 1 := by
  by_cases hn : n = 1
  · subst n
    rw [P201.unitSurfaceDimensionOne, ae_add_measure_iff]
    constructor <;>
      simp [ae_dirac_eq, P102.Trace.Ordinary.linePoint,
        PiLp.norm_eq_of_L2]
  · simp only [P201Specs.unitSurface, ite_eq_right hn]
    change ∀ᵐ θ ∂Measure.map (fun θ : sphere (0 : Space n) 1 => (θ : Space n))
        (volume : Measure (Space n)).toSphere, θ ∈ sphere (0 : Space n) 1
    apply (MeasureTheory.ae_map_iff
      (f := fun θ : sphere (0 : Space n) 1 => (θ : Space n))
      (p := fun θ : Space n => θ ∈ sphere 0 1)
      (by fun_prop) isClosed_sphere.measurableSet).mpr
    exact Eventually.of_forall fun θ => θ.property

theorem unitSphereMean_zero {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (u : Space n → 𝕜) (a : Space n) : unitSphereMean u a 0 = u a := by
  simp only [unitSphereMean, P201Specs.MeanValues.unitSphereMean, zero_smul, add_zero,
    integral_const]
  change (P201Specs.omega n)⁻¹ • (P201Specs.omega n • u a) = u a
  rw [smul_smul, inv_mul_cancel₀ (omega_pos hn).ne', one_smul]

theorem unitSphereMean_limit : P201Specs.MeanValues.UnitSphereMeanLimitStatement := by
  intro n hn 𝕜 _ Ω u a hc ha
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds ha)
  have hKΩ : closedBall a (ε / 2) ⊆ (Ω : Set _) := by
    exact (closedBall_subset_ball (by linarith)).trans hεΩ
  have hmem (s : ℝ) (hs : |s| ≤ ε / 2) (θ : Space n)
      (hθ : θ ∈ sphere (0 : Space n) 1) : a + s • θ ∈ closedBall a (ε / 2) := by
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    simpa [mem_closedBall, dist_eq_norm, norm_smul, hθn] using hs
  obtain ⟨C, hC⟩ := (isCompact_closedBall a (ε / 2)).bddAbove_image (hc.mono hKΩ).norm
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ ε / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < ε / 2)] with s hs
    exact le_of_lt (by simpa [mem_ball, Real.dist_eq] using hs)
  have hm : ∀ᶠ s : ℝ in 𝓝 0,
      AEStronglyMeasurable (fun θ : Space n => u (a + s • θ)) (P201Specs.unitSurface n) := by
    filter_upwards [hsmall] with s hs
    have hc' : ContinuousOn (fun θ : Space n => u (a + s • θ)) (sphere 0 1) :=
      hc.comp (by fun_prop) (fun θ hθ => hKΩ (hmem s hs θ hθ))
    have hm' := hc'.aestronglyMeasurable (μ := P201Specs.unitSurface n)
      isClosed_sphere.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (unitSurface_ae_mem n)] at hm'
  have hb : ∀ᶠ s : ℝ in 𝓝 0,
      ∀ᵐ θ ∂P201Specs.unitSurface n, ‖u (a + s • θ)‖ ≤ C := by
    filter_upwards [hsmall] with s hs
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    exact hC (mem_image_of_mem _ (hmem s hs θ hθ))
  have hlim : ∀ᵐ θ ∂P201Specs.unitSurface n,
      ContinuousAt (fun s : ℝ => u (a + s • θ)) 0 := by
    apply Eventually.of_forall
    intro θ
    have hcu : ContinuousAt u (a + (0 : ℝ) • θ) := by
      simpa using hc.continuousAt (Ω.isOpen.mem_nhds ha)
    have hmap : ContinuousAt (fun s : ℝ => a + s • θ) 0 := by fun_prop
    exact hcu.comp (f := fun s : ℝ => a + s • θ) hmap
  have hi : ContinuousAt
      (fun s : ℝ => ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) 0 :=
    continuousAt_of_dominated hm hb (integrable_const C) hlim
  have hh : ContinuousAt (unitSphereMean u a) 0 :=
    hi.const_smul ((P201Specs.omega n)⁻¹)
  rw [← unitSphereMean_zero hn u a]
  exact hh

theorem unitSurface_integrable_of_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n → 𝕜} (hf : ContinuousOn f (sphere 0 1)) :
    Integrable f (P201Specs.unitSurface n) := by
  have hi := hf.integrableOn_compact (μ := P201Specs.unitSurface n) (isCompact_sphere 0 1)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (unitSurface_ae_mem n)] at hi

theorem angular_derivative : P201Specs.MeanValues.AngularDerivativeStatement := by
  intro n 𝕜 _ Ω u hc a r hr hball
  obtain ⟨δ, hδ, hKΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  let K := cthickening δ (closedBall a r)
  have hK : IsCompact K := (isCompact_closedBall a r).cthickening
  have hd := hc.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hd.mono hKΩ).norm
  have hmem (s : ℝ) (hs : s ∈ ball r δ) (θ : Space n)
      (hθ : θ ∈ sphere (0 : Space n) 1) : a + s • θ ∈ K := by
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    have hbase : a + r • θ ∈ closedBall a r := by
      simp [mem_closedBall, dist_eq_norm, norm_smul, hθn, abs_of_nonneg hr]
    apply mem_cthickening_of_dist_le (a + s • θ) (a + r • θ) δ (closedBall a r) hbase
    have hdist : dist (a + s • θ) (a + r • θ) = dist s r := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθn, mul_one]
      exact (Real.dist_eq s r).symm
    rw [hdist]
    exact le_of_lt hs
  have hu_sphere (s : ℝ) (hs : s ∈ ball r δ) :
      ContinuousOn (fun θ : Space n => u (a + s • θ)) (sphere 0 1) :=
    hc.continuousOn.comp (by fun_prop) (fun θ hθ => hKΩ (hmem s hs θ hθ))
  have hd_sphere : ContinuousOn
      (fun θ : Space n => fderiv ℝ u (a + r • θ) θ) (sphere 0 1) := by
    exact (hd.comp (by fun_prop)
      (fun θ hθ => hKΩ (hmem r (mem_ball_self hδ) θ hθ))).clm_apply continuousOn_id
  have hmeas : ∀ᶠ s : ℝ in 𝓝 r,
      AEStronglyMeasurable (fun θ : Space n => u (a + s • θ)) (P201Specs.unitSurface n) := by
    filter_upwards [Metric.ball_mem_nhds r hδ] with s hs
    exact (unitSurface_integrable_of_continuousOn (hu_sphere s hs)).aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂P201Specs.unitSurface n,
      ∀ s ∈ ball r δ, ‖fderiv ℝ u (a + s • θ) θ‖ ≤ C := by
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    intro s hs
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    calc
      ‖fderiv ℝ u (a + s • θ) θ‖ ≤ ‖fderiv ℝ u (a + s • θ)‖ * ‖θ‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa [hθn] using hC (mem_image_of_mem _ (hmem s hs θ hθ))
  have hdiff : ∀ᵐ θ ∂P201Specs.unitSurface n, ∀ s ∈ ball r δ,
      HasDerivAt (fun t : ℝ => u (a + t • θ)) (fderiv ℝ u (a + s • θ) θ) s := by
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    intro s hs
    have hx := hKΩ (hmem s hs θ hθ)
    have hdu : DifferentiableAt ℝ u (a + s • θ) :=
      (hc.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt one_ne_zero
    have hmap : HasDerivAt (fun t : ℝ => a + t • θ) θ s := by
      simpa using ((hasDerivAt_id s).smul_const θ).const_add a
    exact hdu.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => a + t • θ) s hmap
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P201Specs.unitSurface n) (bound := fun _ => C)
    (Metric.ball_mem_nhds r hδ) hmeas
    (unitSurface_integrable_of_continuousOn (hu_sphere r (mem_ball_self hδ)))
    (unitSurface_integrable_of_continuousOn hd_sphere).aestronglyMeasurable
    hbound (integrable_const C) hdiff
  exact hi.2.const_smul ((P201Specs.omega n)⁻¹)

open P102.Trace.Ordinary

theorem sphere_one_eq_pair : sphere (0 : Space 1) 1 = {linePoint 1, linePoint (-1)} := by
  ext x
  have hx : lineIsometry (lineIsometry.symm x) = x := lineIsometry.apply_symm_apply x
  rw [← hx]
  simp only [mem_sphere, dist_zero_right, lineIsometry.norm_map, Real.norm_eq_abs,
    mem_insert_iff, mem_singleton_iff, ← lineIsometry_apply, lineIsometry.injective.eq_iff]
  exact abs_eq (by norm_num)

theorem cone_linePoint (t : ℝ) :
    Ioo (0 : ℝ) 1 • ({linePoint t} : Set (Space 1)) =
      lineIsometry '' (Ioo (0 : ℝ) 1 • ({t} : Set ℝ)) := by
  simp only [Set.smul_singleton, ← lineIsometry_apply, ← map_smul,
    Set.image_image]

theorem unitSurface_eq_map_toSphere (n : ℕ) :
    P201Specs.unitSurface n = Measure.map
      (Subtype.val : sphere (0 : Space n) 1 → Space n) (volume : Measure (Space n)).toSphere := by
  by_cases hn : n = 1
  · subst n
    let μ := Measure.map (Subtype.val : sphere (0 : Space 1) 1 → Space 1)
      (volume : Measure (Space 1)).toSphere
    have ha (t : ℝ) (ht : |t| = 1) : μ {linePoint t} = 1 := by
      have hm : MeasurableSet ((Subtype.val : sphere (0 : Space 1) 1 → Space 1) ⁻¹' {linePoint t}) := by measurability
      change (Measure.map _ _) _ = _
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _), Measure.toSphere_apply' _ hm]
      have hi : (Subtype.val : sphere (0 : Space 1) 1 → Space 1) ''
          ((Subtype.val : sphere (0 : Space 1) 1 → Space 1) ⁻¹' {linePoint t}) = {linePoint t} := by
        rw [image_preimage_eq_inter_range, Subtype.range_coe]
        apply inter_eq_left.mpr
        simpa [← lineIsometry_apply, mem_sphere, dist_zero_right] using ht
      rw [hi, cone_linePoint]
      have hvol : volume (lineIsometry '' (Ioo (0 : ℝ) 1 • ({t} : Set ℝ))) =
          volume (Ioo (0 : ℝ) 1 • ({t} : Set ℝ)) := by
        have hm' : MeasurableSet (Ioo (0 : ℝ) 1 • ({t} : Set ℝ)) := by
          rcases (abs_eq (by norm_num)).mp ht with rfl | rfl <;>
            simp [smul_eq_mul, image_neg_eq_neg]
        have hm'' : MeasurableSet (lineIsometry '' (Ioo (0 : ℝ) 1 • ({t} : Set ℝ))) :=
          lineIsometry.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hm'
        have hh := lineIsometry.measurePreserving.measure_preimage hm''.nullMeasurableSet
        simpa only [Set.preimage_image_eq _ lineIsometry.injective] using hh.symm
      rw [hvol]
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_one, one_mul]
      rcases (abs_eq (by norm_num)).mp ht with rfl | rfl <;>
        norm_num [Set.smul_singleton, smul_eq_mul, Real.volume_Ioo, image_neg_eq_neg, neg_Ioo]
    have hmem : ∀ᵐ x ∂μ, x ∈ sphere (0 : Space 1) 1 := by
      apply (ae_map_iff (by fun_prop) isClosed_sphere.measurableSet).mpr
      exact .of_forall fun θ => θ.property
    have hne : linePoint (1 : ℝ) ≠ linePoint (-1) := by
      exact lineIsometry.injective.ne (by norm_num)
    rw [P201.unitSurfaceDimensionOne]
    change _ = μ
    rw [← Measure.restrict_eq_self_of_ae_mem hmem, sphere_one_eq_pair,
      show ({linePoint (1 : ℝ), linePoint (-1)} : Set (Space 1)) =
        {linePoint 1} ∪ {linePoint (-1)} by rfl,
      Measure.restrict_union (by simpa using hne) (measurableSet_singleton _)]
    simp only [Measure.restrict_singleton, ha 1 (by norm_num), ha (-1) (by norm_num), one_smul]
  · simp [P201Specs.unitSurface, hn]

/-- Polar coordinates for the canonical Euclidean volume, with scalar-valued
integrands and with the explicit counting surface in dimension one included. -/
theorem integral_polar_product {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (f : Space n → 𝕜) :
    (∫ x, f x) = ∫ p : sphere (0 : Space n) 1 × Ioi (0 : ℝ),
      f (p.2.1 • p.1.1)
      ∂(volume : Measure (Space n)).toSphere.prod (Measure.volumeIoiPow (n - 1)) := by
  let : NeZero n := ⟨by omega⟩
  calc
    (∫ x, f x) = ∫ x : ({0}ᶜ : Set (Space n)), f x.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd (Space n)).symm p).1))
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace_fin] using h

theorem integrable_polar_product {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {f : Space n → 𝕜} (hf : Integrable f volume) :
    Integrable (fun p : sphere (0 : Space n) 1 × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
      ((volume : Measure (Space n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
  let : NeZero n := ⟨by omega⟩
  have hi : Integrable (fun x : ({0}ᶜ : Set (Space n)) => f x.1)
      (volume.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have h := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (g := fun p => f (((homeomorphUnitSphereProd (Space n)).symm p).1))
    (Homeomorph.measurableEmbedding _)
  simp only [Function.comp_def, Homeomorph.symm_apply_apply] at h
  simpa only [homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace_fin] using h.mp hi

theorem integral_polar {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {f : Space n → 𝕜} (hf : Integrable f volume) :
    (∫ x, f x) = ∫ s in Ioi (0 : ℝ), s ^ (n - 1) •
      ∫ θ, f (s • θ) ∂P201Specs.unitSurface n := by
  rw [integral_polar_product hn f, integral_prod_symm _ (integrable_polar_product hn hf)]
  have he : Topology.IsClosedEmbedding
      (Subtype.val : sphere (0 : Space n) 1 → Space n) :=
    isClosed_sphere.isClosedEmbedding_subtypeVal
  simp_rw [unitSurface_eq_map_toSphere, he.integral_map]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun s : ℝ => Real.toNNReal (s ^ (n - 1)) •
        ∫ θ : sphere (0 : Space n) 1, f (s • θ.1) ∂(volume : Measure (Space n)).toSphere)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hs.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Radial integration in a ball with the project's actual unit surface. -/
theorem integral_ball_polar {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {u : Space n → 𝕜} (a : Space n) (r : ℝ) (hu : IntegrableOn u (ball a r)) :
    (∫ x in ball a r, u x) = ∫ s in Ioo (0 : ℝ) r, s ^ (n - 1) •
      ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n := by
  have hi : Integrable ((ball a r).indicator u) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hu
  rw [← integral_indicator measurableSet_ball,
    ← integral_add_left_eq_self ((ball a r).indicator u) a,
    integral_polar hn (hi.comp_add_left a)]
  have hh (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ (n - 1) • ∫ θ, (ball a r).indicator u (a + s • θ) ∂P201Specs.unitSurface n =
        (Iio r).indicator (fun s : ℝ => s ^ (n - 1) •
          ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) s := by
    have he : (∫ θ, (ball a r).indicator u (a + s • θ) ∂P201Specs.unitSurface n) =
        if s < r then ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n else 0 := by
      split_ifs with h
      · apply integral_congr_ae
        filter_upwards [unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        apply indicator_of_mem
        simpa [mem_ball, dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out] using h
      · rw [← integral_zero (μ := P201Specs.unitSurface n) (G := 𝕜)]
        apply integral_congr_ae
        filter_upwards [unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        apply indicator_of_notMem
        simpa [mem_ball, dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out] using h
    rw [he]
    by_cases h : s < r <;> simp [h, Set.indicator]
  rw [setIntegral_congr_fun measurableSet_Ioi hh, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
    exact and_comm
  rw [hs]

theorem integral_radial_power {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in Ioo (0 : ℝ) r, s ^ (n - 1)) = r ^ n / n := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
    integral_pow, Nat.sub_add_cancel hn]
  simp only [zero_pow (by omega : n ≠ 0), sub_zero]
  congr 1
  exact_mod_cast Nat.sub_add_cancel hn

theorem sphere_implies_ball {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (hs : HasSphereMeanValue Ω u) : HasBallMeanValue Ω u := by
  intro a r hr hball
  have ho := (omega_pos hn).ne'
  have hI (s : ℝ) (hs' : s ∈ Ioo (0 : ℝ) r) :
      (∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) = P201Specs.omega n • u a := by
    have hmean := hs a s hs'.1 ((closedBall_subset_closedBall hs'.2.le).trans hball)
    rw [sphere_mean_normalization hn u a s hs'.1] at hmean
    calc
      _ = P201Specs.omega n • unitSphereMean u a s := by
        simp only [unitSphereMean, P201Specs.MeanValues.unitSphereMean, smul_smul,
          mul_inv_cancel₀ ho, one_smul]
      _ = _ := congrArg (P201Specs.omega n • ·) hmean.symm
  have hi : IntegrableOn u (ball a r) :=
    ((hc.mono hball).integrableOn_compact (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hrad : (∫ x in ball a r, u x) = (r ^ n / n) • (P201Specs.omega n • u a) := by
    rw [integral_ball_polar hn a r hi]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun s hs => congrArg (s ^ (n - 1) • ·) (hI s hs))]
    rw [integral_smul_const, integral_radial_power hn hr.le]
  change u a = (volume.real (ball a r))⁻¹ • _
  rw [hrad, P201.ballVolumeNormalization hn a r hr.le, smul_smul, smul_smul]
  have hcoef : (P201Specs.omega n * r ^ n / n)⁻¹ * (r ^ n / n * P201Specs.omega n) = 1 := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  rw [mul_assoc, hcoef, one_smul]

/-- Continuity of the unnormalized angular integral at an interior radius. -/
theorem angularIntegral_continuousAt {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (a : Space n) (r : ℝ) (hr : 0 ≤ r) (hball : closedBall a r ⊆ (Ω : Set _)) :
    ContinuousAt (fun s : ℝ => ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n) r := by
  obtain ⟨δ, hδ, hKΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  let K := cthickening δ (closedBall a r)
  have hK : IsCompact K := (isCompact_closedBall a r).cthickening
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.mono hKΩ).norm
  have hmem (s : ℝ) (hs : s ∈ ball r δ) (θ : Space n)
      (hθ : θ ∈ sphere (0 : Space n) 1) : a + s • θ ∈ K := by
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    have hbase : a + r • θ ∈ closedBall a r := by
      simp [mem_closedBall, dist_eq_norm, norm_smul, hθn, abs_of_nonneg hr]
    apply mem_cthickening_of_dist_le (a + s • θ) (a + r • θ) δ (closedBall a r) hbase
    have hdist : dist (a + s • θ) (a + r • θ) = dist s r := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθn, mul_one]
      exact (Real.dist_eq s r).symm
    rw [hdist]
    exact le_of_lt hs
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [Metric.ball_mem_nhds r hδ] with s hs
    exact (unitSurface_integrable_of_continuousOn
      (hc.comp (by fun_prop) (fun θ hθ => hKΩ (hmem s hs θ hθ)))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds r hδ] with s hs
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    exact hC (mem_image_of_mem _ (hmem s hs θ hθ))
  · exact integrable_const C
  · filter_upwards [unitSurface_ae_mem n] with θ hθ
    have hx := hKΩ (hmem r (mem_ball_self hδ) θ hθ)
    exact (hc.continuousAt (Ω.isOpen.mem_nhds hx)).comp (f := fun s : ℝ => a + s • θ) (by fun_prop)

/-- FTC for the radius of the ball integral, requiring continuity only. -/
theorem ballIntegral_hasDerivAt {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (a : Space n) (r : ℝ) (hr : 0 < r) (hball : closedBall a r ⊆ (Ω : Set _)) :
    HasDerivAt (fun s : ℝ => ∫ x in ball a s, u x)
      (r ^ (n - 1) • ∫ θ, u (a + r • θ) ∂P201Specs.unitSurface n) r := by
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  rw [cthickening_closedBall hδ.le hr.le] at hδΩ
  let R := δ + r
  let F := fun s : ℝ => s ^ (n - 1) • ∫ θ, u (a + s • θ) ∂P201Specs.unitSurface n
  have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) : ContinuousAt F s := by
    exact (continuousAt_id.pow _).smul (angularIntegral_continuousAt Ω u hc a s hs.1
      ((closedBall_subset_closedBall hs.2).trans hδΩ))
  have hFi : IntervalIntegrable F volume 0 r :=
    (continuousOn_of_forall_continuousAt (fun s hs => hF s ⟨hs.1, hs.2.trans (by dsimp [R]; linarith)⟩)).intervalIntegrable_of_Icc hr.le
  have hFr : ContinuousAt F r := hF r ⟨hr.le, by dsimp [R]; linarith⟩
  have hnhds : Icc (0 : ℝ) R ∈ 𝓝 r := Icc_mem_nhds hr (by dsimp [R]; linarith)
  have hmeas : StronglyMeasurableAtFilter F (𝓝 r) volume :=
    ⟨Icc 0 R, hnhds, (continuousOn_of_forall_continuousAt hF).aestronglyMeasurable
      measurableSet_Icc⟩
  have hder := intervalIntegral.integral_hasDerivAt_right hFi hmeas hFr
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr (by dsimp [R]; linarith : r < R)] with s hs
  rw [intervalIntegral.integral_of_le hs.1.le, integral_Ioc_eq_integral_Ioo]
  exact (integral_ball_polar hn a s
    (((hc.mono ((closedBall_subset_closedBall hs.2.le).trans hδΩ)).integrableOn_compact
      (isCompact_closedBall a s)).mono_set ball_subset_closedBall))

theorem ball_implies_sphere {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (hb : HasBallMeanValue Ω u) : HasSphereMeanValue Ω u := by
  intro a r hr hball
  let : NeZero n := ⟨by omega⟩
  have ho := (omega_pos hn).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  rw [cthickening_closedBall hδ.le hr.le] at hδΩ
  let G : ℝ → 𝕜 := fun s => (P201Specs.omega n / n * s ^ n) • u a
  have hG : HasDerivAt G ((P201Specs.omega n * r ^ (n - 1)) • u a) r := by
    have h := ((hasDerivAt_pow n r).const_mul (P201Specs.omega n / n)).smul_const (u a)
    convert h using 1
    congr 1
    field_simp
  have he : (fun s : ℝ => ∫ x in ball a s, u x) =ᶠ[𝓝 r] G := by
    filter_upwards [Ioo_mem_nhds hr (by linarith : r < δ + r)] with s hs
    have hbs : closedBall a s ⊆ (Ω : Set _) := (closedBall_subset_closedBall hs.2.le).trans hδΩ
    have hm := hb a s hs.1 hbs
    have hv : volume.real (ball a s) ≠ 0 :=
      (ENNReal.toReal_pos (measure_ball_pos volume a hs.1).ne' measure_ball_lt_top.ne).ne'
    change u a = (volume.real (ball a s))⁻¹ • _ at hm
    calc
      _ = volume.real (ball a s) • u a := by
        rw [hm, smul_smul, mul_inv_cancel₀ hv, one_smul]
      _ = G s := by
        dsimp [G]
        rw [P201.ballVolumeNormalization hn a s hs.1.le]
        congr 1
        ring
  have hd := ballIntegral_hasDerivAt hn Ω u hc a r hr hball
  have hEq := hd.unique (hG.congr_of_eventuallyEq he)
  have hI : (∫ θ, u (a + r • θ) ∂P201Specs.unitSurface n) = P201Specs.omega n • u a := by
    apply smul_right_injective 𝕜 (pow_ne_zero (n - 1) hr.ne')
    simpa only [smul_smul, mul_comm] using hEq
  rw [sphere_mean_normalization hn u a r hr]
  change u a = (P201Specs.omega n)⁻¹ • _
  rw [hI, smul_smul, inv_mul_cancel₀ ho, one_smul]


theorem ballAverage_limit {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (a : Space n)
    (hc : ContinuousOn u Ω) (ha : a ∈ Ω) :
    Tendsto (ballAverage u a) (𝓝[>] 0) (𝓝 (u a)) := by
  let : NeZero n := ⟨by omega⟩
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousAt_iff.mp
    (hc.continuousAt (Ω.isOpen.mem_nhds ha)) (ε / 2) (by linarith)
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds ha)
  refine ⟨min δ (R / 2), lt_min hδ (by linarith), ?_⟩
  intro r hr hsmall
  change 0 < r at hr
  have hrd : r < δ := by simpa [Real.dist_eq, abs_of_pos hr] using lt_of_lt_of_le hsmall (min_le_left _ _)
  have hrr : r < R / 2 := by simpa [Real.dist_eq, abs_of_pos hr] using lt_of_lt_of_le hsmall (min_le_right _ _)
  have hball : closedBall a r ⊆ (Ω : Set _) :=
    (closedBall_subset_ball (by linarith : r < R)).trans hRΩ
  have hi : IntegrableOn u (ball a r) :=
    ((hc.mono hball).integrableOn_compact (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hv : 0 < volume.real (ball a r) :=
    ENNReal.toReal_pos (measure_ball_pos volume a hr).ne' measure_ball_lt_top.ne
  have he : ballAverage u a r - u a = (volume.real (ball a r))⁻¹ •
      ∫ x in ball a r, u x - u a := by
    rw [integral_sub hi (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hv.ne', one_smul]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv)]
  have hbound : ‖∫ x in ball a r, u x - u a‖ ≤ (ε / 2) * volume.real (ball a r) := by
    apply norm_setIntegral_le_of_norm_le_const measure_ball_lt_top
    intro x hx
    exact le_of_lt (by simpa only [dist_eq_norm] using hδu (hx.trans hrd))
  calc
    (volume.real (ball a r))⁻¹ * ‖∫ x in ball a r, u x - u a‖ ≤
      (volume.real (ball a r))⁻¹ * ((ε / 2) * volume.real (ball a r)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hv.le)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith





theorem laplacian_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : ContDiffOn ℝ 2 u Ω) :
    ContinuousOn (P201Specs.laplacian u) Ω := by
  have hi : ContinuousOn (iteratedFDeriv ℝ 2 u) Ω :=
    ContinuousOn.continuousOn_iteratedFDeriv hu Ω.isOpen (by norm_num)
  have he : EqOn (P201Specs.laplacian u) (fun x => ∑ i : Fin n,
      iteratedFDeriv ℝ 2 u x ![coordinate n i, coordinate n i]) Ω := by
    intro x hx
    rw [laplacian_bridge u x (hu.contDiffAt (Ω.isOpen.mem_nhds hx)),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
        (EuclideanSpace.basisFun (Fin n) ℝ)]
    rfl
  apply ContinuousOn.congr _ he
  apply continuousOn_finsetSum
  intro i _
  exact (continuous_eval_const _).comp_continuousOn hi





/-- A continuous function whose integrals on all interior balls vanish is zero. -/
theorem eq_zero_of_ball_integrals_eq_zero {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (f : Space n → 𝕜)
    (hf : ContinuousOn f Ω)
    (hz : ∀ (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
      (∫ x in ball a r, f x) = 0) : ∀ a ∈ Ω, f a = 0 := by
  intro a ha
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds ha)
  have he : ballAverage f a =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [(nhdsGT_basis 0).mem_of_mem (by linarith : 0 < R / 2)] with r hr
    change 0 < r ∧ r < R / 2 at hr
    have hball : closedBall a r ⊆ (Ω : Set _) :=
      (closedBall_subset_ball (by linarith : r < R)).trans hRΩ
    change (volume.real (ball a r))⁻¹ • _ = 0
    rw [hz a r hr.1 hball, smul_zero]
  exact tendsto_nhds_unique (ballAverage_limit hn Ω f a hf ha)
    (tendsto_const_nhds.congr' he.symm)



def radialKernel {n : ℕ} (r : ℝ) (x : Space n) : ℝ := expNegInvGlue (r ^ 2 - ‖x‖ ^ 2)

theorem radialKernel_contDiff {n : ℕ} (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (radialKernel (n := n) r) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem radialKernel_support {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Function.support (radialKernel (n := n) r) = ball 0 r := by
  ext x
  simp only [Function.mem_support, radialKernel, Ne, expNegInvGlue.zero_iff_nonpos,
    not_le, mem_ball_zero_iff]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    nlinarith [norm_nonneg x]

theorem radialKernel_hasCompactSupport {n : ℕ} {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialKernel (n := n) r) := by
  rw [HasCompactSupport, tsupport, radialKernel_support hr, closure_ball 0 hr.ne']
  exact isCompact_closedBall _ _

theorem radialKernel_integrable {n : ℕ} {r : ℝ} (hr : 0 < r) :
    Integrable (radialKernel (n := n) r) :=
  (radialKernel_contDiff r).continuous.integrable_of_hasCompactSupport
    (radialKernel_hasCompactSupport hr)

theorem radialKernel_integral_pos {n : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < ∫ x : Space n, radialKernel r x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => expNegInvGlue.nonneg _)
    (radialKernel_integrable hr)).mpr
  change 0 < volume (Function.support (radialKernel (n := n) r))
  rw [radialKernel_support hr]
  exact measure_ball_pos volume 0 hr

theorem radialKernel_neg {n : ℕ} (r : ℝ) (x : Space n) :
    radialKernel r (-x) = radialKernel r x := by simp [radialKernel]

theorem radialKernel_convolution_eq {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    {f : Space n → 𝕜} (hf : LocallyIntegrable f volume) (a : Space n) {r : ℝ} (hr : 0 < r)
    (hm : ∀ s : ℝ, 0 < s → s < r →
      (∫ θ, f (a + s • θ) ∂P201Specs.unitSurface n) = P201Specs.omega n • f a) :
    (radialKernel r ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) a =
      (∫ t : Space n, radialKernel r t) • f a := by
  have hi := (radialKernel_hasCompactSupport hr).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
    (radialKernel_contDiff r).continuous hf a
  have hip : Integrable (fun t => radialKernel r t • f (a + t)) volume := by
    simpa only [ContinuousLinearMap.lsmul_apply, radialKernel_neg, sub_neg_eq_add] using hi.integrable.comp_neg
  rw [convolution_def]
  change (∫ t, radialKernel r t • f (a - t)) = _
  rw [← integral_neg_eq_self]
  simp only [radialKernel_neg, sub_neg_eq_add]
  rw [integral_polar hn hip, integral_polar hn (radialKernel_integrable hr),
    ← integral_smul_const]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  have hek : ∀ᵐ θ ∂P201Specs.unitSurface n,
      radialKernel r (s • θ) = expNegInvGlue (r ^ 2 - s ^ 2) := by
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    simp [radialKernel, norm_smul, hθn, Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae (hek.mono (fun θ hθ => congrArg (fun k => k • f (a + s • θ)) hθ)),
    integral_smul, integral_congr_ae hek, integral_const]
  by_cases hsr : s < r
  · rw [hm s hs hsr]
    simp only [Measure.real, P201Specs.omega, smul_smul, smul_eq_mul]
    congr 1
    ring
  · have hk : expNegInvGlue (r ^ 2 - s ^ 2) = 0 :=
      expNegInvGlue.zero_of_nonpos (by nlinarith [hs.out])
    simp [hk]

theorem sphere_mean_implies_contDiffOn {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (hs : HasSphereMeanValue Ω u) : ContDiffOn ℝ (⊤ : ℕ∞) u Ω := by
  intro a ha
  obtain ⟨R, hR, hRΩ⟩ : ∃ R : ℝ, 0 < R ∧ closedBall a R ⊆ (Ω : Set _) :=
    Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds ha)
  let f : Space n → 𝕜 := (closedBall a R).indicator u
  have hfi : Integrable f volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      ((hc.mono hRΩ).integrableOn_compact (isCompact_closedBall a R))
  let K : Space n → ℝ := radialKernel (R / 2)
  let m : ℝ := ∫ t, K t
  have hm : m ≠ 0 := (radialKernel_integral_pos (half_pos hR)).ne'
  let g : Space n → 𝕜 := fun y => m⁻¹ • (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) y
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g :=
    ((radialKernel_hasCompactSupport (half_pos hR)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (radialKernel_contDiff (R / 2))
      hfi.locallyIntegrable).const_smul _
  have heq : ∀ y ∈ ball a (R / 2), u y = g y := by
    intro y hy
    have hyR : y ∈ closedBall a R :=
      mem_closedBall.mpr (hy.le.trans (half_le_self hR.le))
    have hball : closedBall y (R / 2) ⊆ closedBall a R :=
      closedBall_subset_closedBall' (by have hdist : dist y a < R / 2 := hy; linarith)
    have hyf : f y = u y := indicator_of_mem hyR u
    have hmean (s : ℝ) (hs0 : 0 < s) (hsR : s < R / 2) :
        (∫ θ, f (y + s • θ) ∂P201Specs.unitSurface n) = P201Specs.omega n • f y := by
      have hsmall : closedBall y s ⊆ (Ω : Set _) :=
        ((closedBall_subset_closedBall hsR.le).trans hball).trans hRΩ
      have htheta : (∫ θ, f (y + s • θ) ∂P201Specs.unitSurface n) =
          ∫ θ, u (y + s • θ) ∂P201Specs.unitSurface n := by
        apply integral_congr_ae
        filter_upwards [unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        apply indicator_of_mem
        apply hball
        simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, hθn, mul_one, abs_of_pos hs0]
        exact hsR.le
      rw [htheta, hyf]
      have hv := hs y s hs0 hsmall
      rw [sphere_mean_normalization hn u y s hs0] at hv
      calc
        _ = P201Specs.omega n • unitSphereMean u y s := by
          simp only [unitSphereMean, P201Specs.MeanValues.unitSphereMean, smul_smul,
            mul_inv_cancel₀ (omega_pos hn).ne', one_smul]
        _ = _ := congrArg (P201Specs.omega n • ·) hv.symm
    have hv := radialKernel_convolution_eq hn hfi.locallyIntegrable y (half_pos hR) hmean
    change u y = m⁻¹ • (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) y
    rw [hv, ← hyf, smul_smul, inv_mul_cancel₀ hm, one_smul]
  exact (hgc.contDiffAt.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds a (half_pos hR)) heq)).contDiffWithinAt


/-- The ball-mean assumption also gives local smoothness. -/
theorem ball_mean_implies_contDiffOn {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hc : ContinuousOn u Ω)
    (hb : HasBallMeanValue Ω u) : ContDiffOn ℝ (⊤ : ℕ∞) u Ω :=
  sphere_mean_implies_contDiffOn hn Ω u hc (ball_implies_sphere hn Ω u hc hb)


private def radialTent {n : ℕ} (a : Space n) (r ε : ℝ) (x : Space n) : ℝ :=
  min 1 (max 0 ((r + ε - dist x a) / ε))

private theorem radialTent_nonneg {n : ℕ} (a : Space n) (r ε : ℝ) (x : Space n) :
    0 ≤ radialTent a r ε x := by simp [radialTent]
private theorem radialTent_le_one {n : ℕ} (a : Space n) (r ε : ℝ) (x : Space n) :
    radialTent a r ε x ≤ 1 := min_le_left _ _
private theorem radialTent_eq_one {n : ℕ} (a : Space n) (r ε : ℝ) (hε : 0 < ε)
    {x : Space n} (hx : dist x a ≤ r) : radialTent a r ε x = 1 := by
  dsimp [radialTent]
  rw [min_eq_left]
  exact le_max_of_le_right ((le_div_iff₀ hε).mpr (by linarith))
private theorem radialTent_eq_zero {n : ℕ} (a : Space n) (r ε : ℝ) (hε : 0 < ε)
    {x : Space n} (hx : r + ε ≤ dist x a) : radialTent a r ε x = 0 := by
  dsimp [radialTent]
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)]
  norm_num
private theorem radialTent_eq_transition {n : ℕ} (a : Space n) (r ε : ℝ) (hε : 0 < ε)
    {x : Space n} (hx : r ≤ dist x a) (hx' : dist x a ≤ r + ε) :
    radialTent a r ε x = (r + ε - dist x a) / ε := by
  dsimp [radialTent]
  rw [max_eq_right (div_nonneg (by linarith) hε.le), min_eq_right]
  exact (div_le_one hε).mpr (by linarith)

private theorem radialTent_lipschitz {n : ℕ} (a : Space n) (r ε : ℝ) :
    LipschitzWith ‖ε⁻¹‖₊ (radialTent a r ε) := by
  have h := (lipschitzWith_smul ε⁻¹).comp ((LipschitzWith.const (r + ε)).sub (LipschitzWith.dist_left a))
  convert (h.const_max 0).const_min 1 using 1 <;> try simp
  funext x
  simp [radialTent, div_eq_mul_inv, mul_comm]

private theorem lipschitz_mul_bounded {n : ℕ} {f g : Space n → ℝ}
    {A B C D : ℝ≥0} (hf : LipschitzWith A f) (hg : LipschitzWith B g)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) :
    LipschitzWith (C * B + D * A) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x * g x) (f y * g y) = ‖f x * (g x - g y) + g y * (f x - f y)‖ := by
      rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by
      grw [norm_add_le, norm_mul, norm_mul]
    _ ≤ C * (B * dist x y) + D * (A * dist x y) := by
      gcongr
      · exact hC x
      · exact hg.norm_sub_le x y
      · exact hD y
      · exact hf.norm_sub_le x y
    _ = (↑(C * B + D * A) : ℝ) * dist x y := by push_cast; ring

private theorem radialTent_mul_lipschitz {n : ℕ} (a : Space n) (r ε : ℝ)
    (g : Space n → ℝ) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    ∃ L, LipschitzWith L (fun x => radialTent a r ε x * g x) := by
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hg one_ne_zero
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuous hg.continuous
  let D' : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  exact ⟨1 * B + D' * ‖ε⁻¹‖₊,
    lipschitz_mul_bounded (radialTent_lipschitz a r ε) hB
      (fun x => by simpa only [NNReal.coe_one, Real.norm_eq_abs, abs_of_nonneg (radialTent_nonneg a r ε x)]
        using radialTent_le_one a r ε x)
      (fun x => (hD x).trans (le_max_left _ _))⟩

private theorem hasFDerivAt_distance {n : ℕ} (a x : Space n) (hx : x ≠ a) :
    HasFDerivAt (fun y : Space n => dist y a)
      (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have h := (((hasFDerivAt_id x).sub_const a).norm_sq).sqrt (pow_ne_zero 2 hn)
  convert h using 1
  · simp [dist_eq_norm]
  · ext e
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, Real.sqrt_sq (norm_nonneg _), smul_eq_mul]
    simp [innerSL]
    field_simp

private theorem radialTent_hasFDerivAt {n : ℕ} (a : Space n) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (x : Space n)
    (hx : dist x a ≠ r) (hx' : dist x a ≠ r + ε) :
    HasFDerivAt (radialTent a r ε)
      (if r < dist x a ∧ dist x a < r + ε then
        (-ε⁻¹ * ‖x - a‖⁻¹) • innerSL ℝ (x - a) else 0) x := by
  by_cases hi : dist x a < r
  · rw [ite_eq_right (by rintro ⟨h, _⟩; linarith : ¬ (r < dist x a ∧ dist x a < r + ε))]
    apply (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq
    filter_upwards [(continuousAt_id.dist continuousAt_const).eventually (gt_mem_nhds hi)] with y hy
    exact radialTent_eq_one a r ε hε hy.le
  · have hi : r < dist x a := lt_of_le_of_ne (not_lt.mp hi) hx.symm
    by_cases ho : dist x a < r + ε
    · rw [ite_eq_left ⟨hi, ho⟩]
      have hxa : x ≠ a := by intro he; simp [he] at hi; linarith
      have hd := ((hasFDerivAt_distance a x hxa).const_sub (r + ε)).mul_const ε⁻¹
      have hd' : HasFDerivAt (fun y : Space n => (r + ε - dist y a) / ε)
          ((-ε⁻¹ * ‖x - a‖⁻¹) • innerSL ℝ (x - a)) x := by
        convert hd using 1
        · simp [div_eq_mul_inv]
        · ext e; simp; ring
      apply hd'.congr_of_eventuallyEq
      filter_upwards [(continuousAt_id.dist continuousAt_const).eventually (Ioo_mem_nhds hi ho)] with y hy
      exact radialTent_eq_transition a r ε hε hy.1.le hy.2.le
    · rw [ite_eq_right (by intro h; exact ho h.2 : ¬ (r < dist x a ∧ dist x a < r + ε))]
      have ho : r + ε < dist x a := lt_of_le_of_ne (not_lt.mp ho) hx'.symm
      apply (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq
      filter_upwards [(continuousAt_id.dist continuousAt_const).eventually (lt_mem_nhds ho)] with y hy
      exact radialTent_eq_zero a r ε hε hy.le

private theorem gradient_radialTent {n : ℕ} (a : Space n) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (x : Space n)
    (hx : dist x a ≠ r) (hx' : dist x a ≠ r + ε) :
    P201.gradient (radialTent a r ε) x =
      if r < dist x a ∧ dist x a < r + ε then
        (-ε⁻¹ * ‖x - a‖⁻¹) • (x - a) else 0 := by
  have hd := (radialTent_hasFDerivAt a r ε hr hε x hx hx').fderiv
  ext i
  change fderiv ℝ (radialTent a r ε) x (coordinate n i) = _
  rw [hd]
  split_ifs <;> simp [innerSL, P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.inner_apply,
    RCLike.inner_apply]

private theorem radialTent_divergence_integral {n : ℕ}
    (W : Space n → Space n) (hW : ContDiff ℝ 1 W) (hcW : HasCompactSupport W)
    (a : Space n) (r ε : ℝ) :
    Integrable (P201.divergence (fun x => radialTent a r ε x • W x)) ∧
      (∫ x, P201.divergence (fun y => radialTent a r ε y • W y) x) = 0 := by
  have hci (i : Fin n) : HasCompactSupport (fun x => W x i) :=
    hcW.comp_left (g := fun z : Space n => z i) (by simp)
  have hdi (i : Fin n) : ContDiff ℝ 1 (fun x => W x i) :=
    by exact (PiLp.proj 2 (fun _ : Fin n => ℝ) i).contDiff.comp hW
  have hI (i : Fin n) :
      Integrable (fun x => fderiv ℝ (fun y => radialTent a r ε y * W y i) x (coordinate n i)) ∧
      (∫ x, fderiv ℝ (fun y => radialTent a r ε y * W y i) x (coordinate n i)) = 0 := by
    obtain ⟨L, hL⟩ := radialTent_mul_lipschitz a r ε (fun x => W x i) (hdi i) (hci i)
    exact P201.SmoothFlux.integral_fderiv_eq_zero_of_lipschitz_compact hL
      ((hci i).mul_left (f := radialTent a r ε)) (coordinate n i)
  change Integrable (fun x => ∑ i : Fin n,
      fderiv ℝ (fun y => radialTent a r ε y * W y i) x (coordinate n i)) ∧ _
  refine ⟨integrable_finsetSum _ (fun i _ => (hI i).1), ?_⟩
  change (∫ x, ∑ i : Fin n,
    fderiv ℝ (fun y => radialTent a r ε y * W y i) x (coordinate n i)) = 0
  rw [integral_finsetSum _ (fun i _ => (hI i).1)]
  simp only [(hI _).2, Finset.sum_const_zero]

private theorem radialTent_divergence_ae {n : ℕ}
    (W : Space n → Space n) (hW : ContDiff ℝ 1 W)
    (a : Space n) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    P201.divergence (fun x => radialTent a r ε x • W x) =ᵐ[volume]
      (fun x => radialTent a r ε x * P201.divergence W x - ε⁻¹ *
        ({x : Space n | r < dist x a ∧ dist x a < r + ε}.indicator
          (fun x => inner ℝ (W x) ((dist x a)⁻¹ • (x - a))) x)) := by
  have hs (t : ℝ) (ht : t ≠ 0) : ∀ᵐ x : Space n ∂volume, dist x a ≠ t := by
    rw [ae_iff]
    simp only [not_not]
    change volume (sphere a t) = 0
    exact addHaar_sphere_of_ne_zero (volume : Measure (Space n)) a ht
  filter_upwards [hs r hr.ne', hs (r + ε) (by positivity)] with x hx hx'
  calc
    _ = inner ℝ (W x) (P201.gradient (radialTent a r ε) x) + P201.divergence W x * radialTent a r ε x :=
      P201.SmoothFlux.divergence_product W (radialTent a r ε) x
        (hW.differentiable one_ne_zero x)
        (radialTent_hasFDerivAt a r ε hr hε x hx hx').differentiableAt
    _ = _ := by
      rw [gradient_radialTent a r ε hr hε x hx hx']
      by_cases hm : r < dist x a ∧ dist x a < r + ε
      · rw [ite_eq_left hm, Set.indicator_of_mem (show x ∈ {y : Space n | r < dist y a ∧ dist y a < r + ε} from hm)]
        simp only [inner_smul_right, ← dist_eq_norm]
        ring
      · rw [ite_eq_right hm, Set.indicator_of_notMem (show x ∉ {y : Space n | r < dist y a ∧ dist y a < r + ε} from hm)]
        simp only [inner_zero_right, mul_zero, sub_zero, zero_add, mul_comm]

private theorem radialTent_tendsto_ae {n : ℕ} (a : Space n) {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ x ∂volume, Tendsto (fun ε : ℝ => radialTent a r ε x)
      (𝓝[>] 0) (𝓝 ((ball a r).indicator (fun _ => (1 : ℝ)) x)) := by
  have hs : ∀ᵐ x ∂volume, x ∉ sphere a r := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using addHaar_sphere_of_ne_zero volume a hr
  filter_upwards [hs] with x hx
  by_cases hxr : dist x a < r
  · have hmem : x ∈ ball a r := hxr
    rw [indicator_of_mem hmem]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (radialTent_eq_one a r ε hε hxr.le).symm
  · have hgt : r < dist x a := lt_of_le_of_ne (not_lt.mp hxr) (by
      intro h; exact hx (by simpa only [mem_sphere] using h.symm))
    rw [indicator_of_notMem (show x ∉ ball a r from hxr)]
    apply tendsto_const_nhds.congr'
    have ht : Iio (dist x a - r) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (sub_pos.mpr hgt)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ht] with ε hε hε'
    exact (radialTent_eq_zero a r ε hε (by have he : ε < dist x a - r := hε'; linarith)).symm

private theorem radialTent_integral_tendsto {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (a : Space n) {r : ℝ} (hr : r ≠ 0)
    {f : Space n → F} (hf : Integrable f volume) :
    Tendsto (fun ε : ℝ => ∫ x, radialTent a r ε x • f x ∂volume)
      (𝓝[>] 0) (𝓝 (∫ x in ball a r, f x ∂volume)) := by
  rw [← integral_indicator measurableSet_ball]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · apply Eventually.of_forall
    intro ε
    have hm : Measurable (radialTent a r ε) := by unfold radialTent; fun_prop
    exact hm.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    apply Eventually.of_forall
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialTent_nonneg a r ε x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (radialTent_le_one a r ε x)
  · exact hf.norm
  · filter_upwards [radialTent_tendsto_ae a hr] with x hx
    convert hx.smul_const (f x) using 1
    by_cases hm : x ∈ ball a r <;> simp [hm]


theorem integral_polar_shell {n : ℕ} (hn : 1 ≤ n)
    (W : Space n → Space n) (hW : Continuous W) (hcW : HasCompactSupport W)
    (a : Space n) (r R : ℝ) (hr : 0 ≤ r) :
    (∫ x in {x : Space n | r < dist x a ∧ dist x a < R},
      inner ℝ (W x) ((dist x a)⁻¹ • (x - a))) =
    ∫ s in Ioo r R, s ^ (n - 1) *
      ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n := by
  let S := {x : Space n | r < dist x a ∧ dist x a < R}
  let G : Space n → ℝ := fun x => inner ℝ (W x) ((dist x a)⁻¹ • (x - a))
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hdir (x : Space n) : ‖(dist x a)⁻¹ • (x - a)‖ ≤ 1 := by
    by_cases hx : x = a
    · simp [hx]
    · have hd : dist x a ≠ 0 := dist_ne_zero.mpr hx
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg dist_nonneg,
        ← dist_eq_norm, inv_mul_cancel₀ hd]
  have hGm : Measurable G := by dsimp [G]; fun_prop
  have hGi : Integrable G volume := by
    apply (hW.integrable_of_hasCompactSupport hcW).norm.mono hGm.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [norm_norm] using (norm_inner_le_norm (W x) ((dist x a)⁻¹ • (x-a))).trans
      (mul_le_of_le_one_right (norm_nonneg (W x)) (hdir x))
  have hI : Integrable (S.indicator G) volume := hGi.indicator hS
  rw [← integral_indicator hS, ← integral_add_left_eq_self (S.indicator G) a,
    integral_polar hn (hI.comp_add_left a)]
  have hh (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ (n - 1) • ∫ θ, S.indicator G (a + s • θ) ∂P201Specs.unitSurface n =
      (Ioo r R).indicator (fun s : ℝ => s ^ (n - 1) *
        ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n) s := by
    have he : (∫ θ, S.indicator G (a + s • θ) ∂P201Specs.unitSurface n) =
        if s ∈ Ioo r R then ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n else 0 := by
      split_ifs with h
      · apply integral_congr_ae
        filter_upwards [unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        have hd : dist (a + s • θ) a = s := by simp [dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out]
        have hmem : a + s • θ ∈ S := by simpa only [S, mem_ofPred_eq, hd, mem_Ioo] using h
        rw [indicator_of_mem hmem]
        dsimp [G]
        rw [hd]
        simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.out.ne', one_smul]
      · rw [← integral_zero (μ := P201Specs.unitSurface n) (G := ℝ)]
        apply integral_congr_ae
        filter_upwards [unitSurface_ae_mem n] with θ hθ
        have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
        have hd : dist (a + s • θ) a = s := by simp [dist_eq_norm, norm_smul, hθn, abs_of_pos hs.out]
        apply indicator_of_notMem
        simpa only [S, mem_ofPred_eq, hd, mem_Ioo] using h
    rw [he]
    by_cases h : s ∈ Ioo r R <;> simp [h, Set.indicator, smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hh, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo r R ∩ Ioi (0 : ℝ) = Ioo r R := by
    apply inter_eq_left.mpr
    intro s hs
    exact hr.trans_lt hs.1
  rw [hs]

/-- Compact continuous fields have continuous angular radial flux integrals. -/
theorem angularFlux_continuous {n : ℕ} (W : Space n → Space n)
    (hW : Continuous W) (hcW : HasCompactSupport W) (a : Space n) :
    Continuous (fun s : ℝ => ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n) := by
  obtain ⟨C, hC⟩ := hcW.exists_bound_of_continuous hW
  apply continuous_of_dominated (bound := fun _ => C)
  · intro s
    have h : Continuous (fun θ : Space n => inner ℝ (W (a + s • θ)) θ) := by fun_prop
    exact h.aestronglyMeasurable
  · intro s
    filter_upwards [unitSurface_ae_mem n] with θ hθ
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    calc
      ‖inner ℝ (W (a + s • θ)) θ‖ ≤ ‖W (a + s • θ)‖ * ‖θ‖ := norm_inner_le_norm _ _
      _ ≤ C := by simpa only [hθn, mul_one] using hC (a + s • θ)
  · exact integrable_const C
  · apply Eventually.of_forall
    intro θ
    fun_prop


private theorem radialFlux_integrable {n : ℕ}
    (W : Space n → Space n) (hW : Continuous W) (hcW : HasCompactSupport W) (a : Space n) :
    Integrable (fun x => inner ℝ (W x) ((dist x a)⁻¹ • (x - a))) volume := by
  have hdir (x : Space n) : ‖(dist x a)⁻¹ • (x - a)‖ ≤ 1 := by
    by_cases hx : x = a
    · simp [hx]
    · have hd : dist x a ≠ 0 := dist_ne_zero.mpr hx
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg dist_nonneg,
        ← dist_eq_norm, inv_mul_cancel₀ hd]
  have hGm : Measurable (fun x => inner ℝ (W x) ((dist x a)⁻¹ • (x - a))) := by fun_prop
  apply (hW.integrable_of_hasCompactSupport hcW).norm.mono hGm.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [norm_norm] using (norm_inner_le_norm (W x) ((dist x a)⁻¹ • (x-a))).trans
    (mul_le_of_le_one_right (norm_nonneg (W x)) (hdir x))

private theorem tendsto_right_set_average {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} {r : ℝ}
    (hm : StronglyMeasurableAtFilter f (𝓝 r) volume) (hc : ContinuousAt f r) :
    Tendsto (fun ε : ℝ => ε⁻¹ • ∫ s in Ioo r (r+ε), f s) (𝓝[>] 0) (𝓝 (f r)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right (a := r)
    (by simp : IntervalIntegrable f volume r r) hm hc
  apply (show Tendsto (fun ε : ℝ => ε⁻¹ • ∫ s in r..r+ε, f s)
    (𝓝[>] 0) (𝓝 (f r)) by simpa using hd.tendsto_slope_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hε.le : r ≤ r + ε), integral_Ioc_eq_integral_Ioo]

/-- The canonical cone-surface divergence identity on a Euclidean ball, proved
from radial Lipschitz cutoffs and coordinate integration by parts. -/
theorem integral_ball_divergence {n : ℕ} (hn : 1 ≤ n)
    (W : Space n → Space n) (hW : ContDiff ℝ 1 W) (hcW : HasCompactSupport W)
    (a : Space n) (r : ℝ) (hr : 0 < r) :
    (∫ x in ball a r, P201.divergence W x) = r ^ (n - 1) *
      ∫ θ, inner ℝ (W (a + r • θ)) θ ∂P201Specs.unitSurface n := by
  have hdiv : Integrable (P201.divergence W) volume := by
    have h := (P201.SmoothFlux.interior_divergence ⟨univ, isOpen_univ⟩ W hW hcW (subset_univ _)).1
    change IntegrableOn (P201.divergence W) univ volume at h
    simpa only [IntegrableOn, Measure.restrict_univ] using h
  have hflux := radialFlux_integrable W hW.continuous hcW a
  have heq (ε : ℝ) (hε : 0 < ε) :
      (∫ x, radialTent a r ε x * P201.divergence W x) =
      ε⁻¹ * ∫ s in Ioo r (r+ε), s ^ (n-1) *
        ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n := by
    have htent : Integrable (fun x => radialTent a r ε x * P201.divergence W x) volume := by
      apply hdiv.norm.mono' ((show Measurable (radialTent a r ε) by unfold radialTent; fun_prop).aestronglyMeasurable.mul hdiv.aestronglyMeasurable)
      filter_upwards [] with x
      change ‖radialTent a r ε x * P201.divergence W x‖ ≤ ‖P201.divergence W x‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (radialTent_nonneg a r ε x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (radialTent_le_one a r ε x)
    let S := {x : Space n | r < dist x a ∧ dist x a < r + ε}
    have hS : MeasurableSet S := by dsimp [S]; measurability
    have hz := (radialTent_divergence_integral W hW hcW a r ε).2
    rw [integral_congr_ae (radialTent_divergence_ae W hW a r ε hr hε),
      integral_sub htent ((hflux.indicator hS).const_mul ε⁻¹), integral_const_mul,
      integral_indicator hS, integral_polar_shell hn W hW.continuous hcW a r (r+ε) hr.le] at hz
    linarith
  have ht := radialTent_integral_tendsto a hr.ne' hdiv
  let Q : ℝ → ℝ := fun s => s ^ (n-1) *
    ∫ θ, inner ℝ (W (a + s • θ)) θ ∂P201Specs.unitSurface n
  have hQc : Continuous Q := (continuous_id.pow _).mul (angularFlux_continuous W hW.continuous hcW a)
  have ha := tendsto_right_set_average (f := Q) (r := r)
    (hQc.stronglyMeasurable.stronglyMeasurableAtFilter) hQc.continuousAt
  have he : (fun ε : ℝ => ∫ x, radialTent a r ε x * P201.divergence W x) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ε⁻¹ • ∫ s in Ioo r (r+ε), Q s) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [smul_eq_mul, Q] using heq ε hε
  exact tendsto_nhds_unique (by simpa only [smul_eq_mul] using ht) (ha.congr' he.symm)


theorem divergence_gradient {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    P201Specs.divergence (P201Specs.gradient u) x = P201Specs.laplacian u x := by
  change (∑ i : Fin n, _) = ∑ i : Fin n, _
  apply Finset.sum_congr rfl
  intro i _
  have hs : ({i, i} : Multiset (Fin n)).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, hs, P102.U4.partialWord]

theorem gradient_inner {n : ℕ} (u : Space n → ℝ) (x θ : Space n) :
    inner ℝ (P201Specs.gradient u x) θ = fderiv ℝ u x θ := by
  have he : ∑ i : Fin n, θ i • P201Specs.coordinate n i = θ := by
    simpa [P201Specs.coordinate, P102.U4.coordinateVector] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr θ
  rw [← he, _root_.map_sum]
  simp [inner_sum, inner_smul_right, P201Specs.gradient, P201Specs.coordinate,
    P102.U4.coordinateVector, EuclideanSpace.inner_single_right]

theorem gradient_contDiffOn {n : ℕ} (Ω : Domain n) (u : Space n → ℝ)
    (hu : ContDiffOn ℝ 2 u Ω) : ContDiffOn ℝ 1 (P201Specs.gradient u) Ω := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact (hu.fderiv_of_isOpen Ω.isOpen (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply contDiffOn_const

theorem integral_ball_laplacian_real {n : ℕ} (hn : 1 ≤ n)
    (Ω : Domain n) (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u Ω)
    (a : Space n) (r : ℝ) (hr : 0 < r) (hball : closedBall a r ⊆ (Ω : Set _)) :
    (∫ x in ball a r, P201Specs.laplacian u x) = r ^ (n - 1) *
      ∫ θ, fderiv ℝ u (a + r • θ) θ ∂P201Specs.unitSurface n := by
  obtain ⟨Z, V, hV, hKV, hVU, hZ, hcZ, hZU, heZ⟩ :=
    P201.SmoothFlux.compact_localization (closedBall a r) Ω (P201Specs.gradient u)
      (isCompact_closedBall a r) Ω.isOpen hball (gradient_contDiffOn Ω u hu)
  have he : ∀ x ∈ closedBall a r, Z =ᶠ[𝓝 x] P201Specs.gradient u := by
    intro x hx
    exact eventuallyEq_of_mem (hV.mem_nhds (hKV hx)) heZ
  rw [show (∫ x in ball a r, P201Specs.laplacian u x) =
      ∫ x in ball a r, P201Specs.divergence Z x from by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    exact ((P201.SmoothFlux.divergence_congr_of_eventuallyEq
      (he x (ball_subset_closedBall hx))).trans (divergence_gradient u x)).symm]
  have hflux : (∫ x in ball a r, P201Specs.divergence Z x) = r ^ (n - 1) *
      ∫ θ, inner ℝ (Z (a + r • θ)) θ ∂P201Specs.unitSurface n :=
    integral_ball_divergence hn Z hZ hcZ a r hr
  rw [hflux]
  congr 1
  apply integral_congr_ae
  filter_upwards [unitSurface_ae_mem n] with θ hθ
  have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
  have hx : a + r • θ ∈ closedBall a r := by
    simp [mem_closedBall, dist_eq_norm, norm_smul, hθn, abs_of_pos hr]
  rw [heZ (hKV hx), gradient_inner]


theorem integral_ball_laplacian {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u : Space n → 𝕜)
    (hu : ContDiffOn ℝ 2 u Ω)
    (a : Space n) (r : ℝ) (hr : 0 < r) (hball : closedBall a r ⊆ (Ω : Set _)) :
    (∫ x in ball a r, P201Specs.laplacian u x) = r ^ (n - 1) •
      ∫ θ, fderiv ℝ u (a + r • θ) θ ∂P201Specs.unitSurface n := by
  have hc := hu.continuousOn_fderiv_of_isOpen Ω.isOpen (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have haθ (θ : Space n) (hθ : θ ∈ sphere (0 : Space n) 1) : a + r • θ ∈ Ω := by
    apply hball
    have hθn : ‖θ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hθ
    simp [mem_closedBall, dist_eq_norm, norm_smul, hθn, abs_of_pos hr]
  have hi : IntegrableOn (P201Specs.laplacian u) (ball a r) :=
    (((laplacian_continuousOn Ω u hu).mono hball).integrableOn_compact
      (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hθi : Integrable (fun θ => fderiv ℝ u (a + r • θ) θ) (P201Specs.unitSurface n) :=
    unitSurface_integrable_of_continuousOn
      ((hc.comp (by fun_prop) haθ).clm_apply continuousOn_id)
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  have hlc : ContDiffOn ℝ 2 (fun x => l (u x)) Ω := l.contDiff.comp_contDiffOn hu
  have hlap (x : Space n) (hx : x ∈ Ω) :
      P201Specs.laplacian (fun y => l (u y)) x = l (P201Specs.laplacian u x) := by
    have hux := hu.contDiffAt (Ω.isOpen.mem_nhds hx)
    rw [laplacian_bridge _ _ (hlc.contDiffAt (Ω.isOpen.mem_nhds hx)),
      laplacian_bridge _ _ hux]
    exact hux.laplacian_CLM_comp_left
  have hder (x : Space n) (hx : x ∈ Ω) (v : Space n) :
      fderiv ℝ (fun y => l (u y)) x v = l (fderiv ℝ u x v) := by
    have huD := (hu.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : Space n →L[ℝ] ℝ => T v) (l.hasFDerivAt.comp x huD.hasFDerivAt).fderiv
  calc
    l (∫ x in ball a r, P201Specs.laplacian u x) =
        ∫ x in ball a r, P201Specs.laplacian (fun y => l (u y)) x := by
      rw [← l.integral_comp_comm hi]
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact (hlap x (hball (ball_subset_closedBall hx))).symm
    _ = r ^ (n - 1) * ∫ θ, fderiv ℝ (fun y => l (u y)) (a + r • θ) θ
          ∂P201Specs.unitSurface n :=
      integral_ball_laplacian_real hn Ω _ hlc a r hr hball
    _ = l (r ^ (n - 1) • ∫ θ, fderiv ℝ u (a + r • θ) θ ∂P201Specs.unitSurface n) := by
      rw [map_smul, ← l.integral_comp_comm hθi]
      change _ = r ^ (n - 1) * _
      congr 1
      apply integral_congr_ae
      filter_upwards [unitSurface_ae_mem n] with θ hθ
      exact hder _ (haθ θ hθ) θ

theorem spherical_mean_derivative : P201Specs.MeanValues.SphericalMeanDerivativeStatement := by
  intro n hn 𝕜 _ Ω u hu a r hr hball
  have hd := angular_derivative Ω u (hu.of_le (by norm_num)) a r hr.le hball
  have hJ := integral_ball_laplacian hn Ω u hu a r hr hball
  rw [hJ, smul_smul]
  convert hd using 1
  congr 1
  have hp : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp


theorem harmonic_sphere_means {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : IsHarmonic Ω u) : HasSphereMeanValue Ω u := by
  intro a r hr hball
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  rw [cthickening_closedBall hδ.le hr.le] at hδΩ
  have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (δ + r)) :
      HasDerivAt (unitSphereMean u a) 0 s := by
    have hzero : (∫ x in ball a s, P201Specs.laplacian u x) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact hu.2 x (hδΩ ((closedBall_subset_closedBall hs.2.le) (ball_subset_closedBall hx)))
    have hds := spherical_mean_derivative hn Ω u hu.1 a s hs.1
      ((closedBall_subset_closedBall hs.2.le).trans hδΩ)
    simpa only [hzero, smul_zero] using hds
  have hconst (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (δ + r)) :
      unitSphereMean u a s = unitSphereMean u a r := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) (δ + r)).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) hs
    exact ⟨hr, by linarith⟩
  have hlim : Tendsto (unitSphereMean u a) (𝓝[>] 0) (𝓝 (u a)) :=
    (unitSphereMean_limit hn Ω u a hu.1.continuousOn
    (hball (mem_closedBall_self hr.le))).mono_left nhdsWithin_le_nhds
  have he : unitSphereMean u a =ᶠ[𝓝[>] 0] fun _ => unitSphereMean u a r := by
    filter_upwards [(nhdsGT_basis 0).mem_of_mem (by linarith : 0 < δ + r)] with s hs
    exact hconst s hs
  have hmean : u a = unitSphereMean u a r :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)
  rw [sphere_mean_normalization hn u a r hr]
  exact hmean

theorem mean_values : P201Specs.MeanValues.MeanValuesStatement := by
  intro n hn 𝕜 _ Ω u hu a r hr hball
  have hsphere := harmonic_sphere_means hn Ω u hu
  exact ⟨hsphere a r hr hball,
    sphere_implies_ball hn Ω u hu.1.continuousOn hsphere a r hr hball⟩

theorem harmonic_of_sphere_mean {n : ℕ} (hn : 1 ≤ n) {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (u : Space n → 𝕜) (hu : ContDiffOn ℝ 2 u Ω)
    (hs : HasSphereMeanValue Ω u) : IsHarmonic Ω u := by
  refine ⟨hu, eq_zero_of_ball_integrals_eq_zero hn Ω (P201Specs.laplacian u)
    (laplacian_continuousOn Ω u hu) ?_⟩
  intro a r hr hball
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall a r).exists_cthickening_subset_open
    Ω.isOpen hball
  rw [cthickening_closedBall hδ.le hr.le] at hδΩ
  have he : unitSphereMean u a =ᶠ[𝓝 r] fun _ => u a := by
    filter_upwards [Ioo_mem_nhds hr (by linarith : r < δ + r)] with s hs'
    have hm := hs a s hs'.1 ((closedBall_subset_closedBall hs'.2.le).trans hδΩ)
    rw [sphere_mean_normalization hn u a s hs'.1] at hm
    exact hm.symm
  have h0 : HasDerivAt (unitSphereMean u a) 0 r :=
    (hasDerivAt_const r (u a)).congr_of_eventuallyEq he
  have hd := spherical_mean_derivative hn Ω u hu a r hr hball
  have hcoe : (P201Specs.omega n * r ^ (n - 1))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (omega_pos hn).ne' (pow_ne_zero _ hr.ne'))
  exact (smul_eq_zero.mp (hd.unique h0)).resolve_left hcoe

theorem sphere_converse : P201Specs.MeanValues.SphereConverseStatement := by
  intro n hn 𝕜 _ Ω u hc hs
  have hsm := sphere_mean_implies_contDiffOn hn Ω u hc hs
  exact ⟨hsm, harmonic_of_sphere_mean hn Ω u (hsm.of_le (by simp)) hs⟩

theorem ball_converse : P201Specs.MeanValues.BallConverseStatement := by
  intro n hn 𝕜 _ Ω u hc hb
  exact sphere_converse hn Ω u hc (ball_implies_sphere hn Ω u hc hb)


end P201.MeanValues
